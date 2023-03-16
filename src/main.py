import argparse
import faulthandler
import gc
import itertools
import logging
import os.path
import traceback
from typing import Optional

from sklearn.preprocessing import normalize

import instances

import z3_api_mods
from instances import *
from seed_info_utils import *
from seeds import *

faulthandler.enable()
enable_trace('spacer')
enable_trace('dl_rule_transf')

heuristic = 'default'
mutations = []

seed_number = 0
queue = []
current_ctx = None
general_stats = None
counter = defaultdict(int)
without_bug_counter = defaultdict(int)
log = dict()


def calculate_weights() -> list:
    weighted_stats = general_stats.get_weighted_stats() \
        if heuristic in {'transitions', 'states'} \
        else None
    weights = []

    for instance in queue:
        group = instance.get_group()
        filename = group.filename
        stats = instance.trace_stats
        # if without_bug_counter[filename] >= WITHOUT_BUG_LIMIT:
        #     weight = 0.1
        if heuristic == 'transitions':
            prob_matrix = stats.get_probability()
            size = stats.matrix.shape[0]
            weight_matrix_part = weighted_stats[:size, :size]
            trans_matrix = stats.matrix
            weight = np.sum(prob_matrix * trans_matrix * weight_matrix_part)
        elif heuristic == 'states':
            states_prob = stats.get_probability()
            weight = sum(states_prob[state] * weighted_stats[state]
                         for state in stats.states_num)
        elif heuristic in {'difficulty', 'simplicity'}:
            group = instance.get_group()
            is_nonlinear = not group.is_linear
            upred_num = group.upred_num
            weight = (is_nonlinear, upred_num)
        else:
            weight = 0.1
        if weight == 0:
            weight += 0.1
        weights.append(weight)
    weights = normalize([weights])[0]
    return weights


def get_trace_stats(instance: Instance, is_seed: bool = False,
                    trace_changed: bool = False):
    global general_stats

    instance.trace_stats.read_from_trace(is_seed)
    instance.update_traces_info(is_seed=is_seed)

    if not is_seed:
        instance.inc_mutation_stats('applications')
        instance.inc_mutation_stats('changed_traces', int(trace_changed))
        instance.inc_mutation_stats('new_transitions', utils.new_transitions)

        mut_type = instance.mutation.type
        current_mutation_stats = instances.mut_stats[mut_type.name]
        assert current_mutation_stats['changed_traces'] >= current_mutation_stats['new_traces'], \
            'There are more unique traces than their changes'

    if heuristic in {'transitions', 'states'}:
        general_stats += instance.trace_stats


def check_satis(instance: Instance, group: InstanceGroup = None,
                is_seed: bool = False):
    if not is_seed:
        seed = group[0]
        if seed.satis == unknown:
            seed.check(group, is_seed=True)
        satis = seed.satis

    instance.check(group, is_seed)
    if is_seed:
        satis = instance.satis

    return instance.satis == satis


def next_instance() -> Instance:
    global queue
    weights = calculate_weights()
    if heuristic == 'simplicity':
        weights = reversed(weights)
    next_instance = random.choices(queue, weights, k=1)[0]
    queue.remove(next_instance)
    return next_instance


def update_mutation_weights():
    instances.update_mutation_weights()
    logging.info(json.dumps({'update_mutation_weights':
                                 instances.get_mut_weights_dict()},
                            cls=MutTypeEncoder))


def print_general_info(solve_time: time = None, mut_time: time = None, trace_time: time = None,
                       model_time: time = None, select_time: time = None,
                       trace_changed: bool = None):
    """Print and log information about runs."""
    global counter, log

    traces_num = len(unique_traces)
    log['runs'] = counter['runs']
    log['current_time'] = time.perf_counter()
    for time_name in {'solve_time', 'mut_time', 'trace_time',
                      'model_time', 'select_time'}:
        time_value = locals()[time_name]
        if time_value:
            log[time_name] = time_value
    if counter['runs']:
        print('Total:', counter['runs'],
              'Bugs:', counter['bug'],
              'Timeout:', counter['timeout'],
              'Unknown:', counter['unknown'],
              'Errors:', counter['error'])
    log['unique_traces'] = traces_num
    if traces_num:
        print('Unique traces:', traces_num, '\n')
    else:
        print()
    logging.info(json.dumps(log))
    log = defaultdict()


def log_run_info(status: str, group: InstanceGroup, message: str = None,
                 instance: Instance = None, mut_instance: Instance = None):
    """Create a log entry with information about the run."""
    global log

    log['status'] = status
    if message:
        log['message'] = message
    if instance:
        if not mut_instance:
            instance_info = instance.get_log(group, is_mutant=False)
            log.update(instance_info)
            if status == 'error':
                if instance.chc:
                    log['chc'] = instance.chc.sexpr()
                log['mut_chain'] = instance.mutation.get_chain()
            else:
                log['satis'] = instance.satis.r

        else:
            mutant_info = mut_instance.get_log(group)
            log.update(mutant_info)
            if status not in {'pass', 'without_change'}:
                log['mut_chain'] = instance.mutation.get_chain()
                last_mutation = mut_instance.mutation
                log['mut_chain'].append(last_mutation.get_name())
                if status in {'bug', 'wrong_model',
                              'mutant_unknown', 'error'}:
                    log['satis'] = mut_instance.satis.r
                    if status == 'wrong_model':
                        log['model_state'] = mut_instance.model_info[0].r
                        log['bug_clause'] = str(mut_instance.model_info[1])


def analyze_check_exception(instance: Instance, err: Exception,
                            message: str = None, mut_instance: Instance = None,
                            is_seed: bool = False):
    """Log information about exceptions that occur during the check."""
    global counter
    group = instance.get_group()
    if not message:
        message = repr(err)

    if is_seed:
        if str(err) == 'timeout':
            counter['timeout'] += 1
            status = 'seed_timeout'
        elif instance.satis == unknown:
            counter['unknown'] += 1
            status = 'seed_unknown'
        else:
            counter['error'] += 1
            status = 'error'
        log_run_info(status,
                     group,
                     message,
                     instance)
    else:
        if str(err) == 'timeout' or isinstance(err, TimeoutError):
            counter['timeout'] += 1
            status = 'mutant_timeout' if mut_instance \
                else 'timeout_before_check'
            log_run_info(status,
                         group,
                         message,
                         instance,
                         mut_instance)
        else:
            if mut_instance:
                counter['unknown'] += 1
                status = 'mutant_unknown'
            else:
                counter['error'] += 1
                status = 'error'
            log_run_info(status,
                         group,
                         message,
                         instance,
                         mut_instance)
        if status == 'mutant_unknown':
            mut_instance.dump('output/unknown',
                              group.filename,
                              message=message,
                              to_name=mut_instance.id)
        elif status == 'timeout_before_check':
            group[0].dump('output/last_mutants',
                          group.filename)

        if status != 'error':
            group.roll_back()


def mk_seed_instance(idx: int, seed_file_name: str, parse: bool = False) -> \
        Optional[Instance]:
    group = InstanceGroup(idx, seed_file_name)
    instance = Instance()
    try:
        if parse:
            parse_ctx = Context()
            seed = parse_smt2_file(seed_file_name, ctx=parse_ctx)
            seed = seed.translate(current_ctx)
            if not seed:
                return None
            instance.set_chc(seed)
        else:
            instance.reset_chc()

        group.push(instance)
        return instance
    except Exception as err:
        message = traceback.format_exc()
        analyze_check_exception(instance,
                                err,
                                message=message,
                                is_seed=True)
        print(message)
        print_general_info()
        return None


def known_seeds_processor(files: set, base_idx: int, seed_info_index):
    def process_seed(i, seed, seed_info):
        global general_stats, counter

        if 'error' in seed_info:
            return None
        instance = mk_seed_instance(i, seed)
        if instance is None:
            return None
        counter['runs'] += 1
        solve_time = instance.process_seed_info(seed_info)
        instance.update_traces_info()
        if heuristic in {'transitions', 'states'}:
            general_stats += instance.trace_stats
        return instance, solve_time

    apply_data = {
        seed: {
            'i': i,
            'seed': seed
        }
        for i, seed in enumerate(files, start=base_idx)
    }
    processed_seeds = map_seeds_ordered(apply_data, seed_info_index, process_seed)
    return (it for it in processed_seeds if it is not None)


def new_seeds_processor(files: set, base_idx: int, seed_info_index):
    global counter

    seed_info = {}
    for i, seed in enumerate(files, start=base_idx):
        instance = mk_seed_instance(i, seed, parse=True)
        if instance is None:
            seed_info[seed] = {'error': 'error at instance creation'}
            continue
        counter['runs'] += 1
        try:
            st_time = time.perf_counter()
            check_satis(instance, is_seed=True)
            get_trace_stats(instance, is_seed=True)
            message = instance.check_model()
            if instance.model_info[0] != sat:
                handle_bug(instance,
                           message=message)
            solve_time = time.perf_counter() - st_time
            seed_info[seed] = {
                'satis': instance.satis.r,
                'time': solve_time,
                'trace_states': [state.save() for state in getattr(instance.trace_stats, 'states', [])]
            }
            yield instance, solve_time
        except Exception as err:
            analyze_check_exception(instance,
                                    err,
                                    is_seed=True)
            print_general_info()
            seed_info[seed] = {'error': 'error at seed check'}
        finally:
            if len(seed_info) > 300:
                store_seed_info(seed_info, seed_info_index)
                seed_info = {}
    if seed_info:
        store_seed_info(seed_info, seed_info_index)


def run_seeds(files: set):
    """Read and solve the seeds."""
    global queue, seed_number, current_ctx

    current_ctx = Context()
    instances.set_ctx(current_ctx)
    seed_info_index = build_seed_info_index()
    known_seed_files = files & set(seed_info_index.keys())
    other_seed_files = files - known_seed_files
    known_seeds = known_seeds_processor(known_seed_files, 0, seed_info_index)
    other_seeds = new_seeds_processor(other_seed_files, len(known_seed_files), seed_info_index)

    for i, (instance, solve_time) in enumerate(itertools.chain(known_seeds, other_seeds)):
        queue.append(instance)
        log_run_info('seed', instance.get_group(), instance=instance)
        print_general_info(solve_time=solve_time)
    seed_number = len(queue)

    assert seed_number > 0, 'All seeds are unknown or ' \
                            'in the incorrect format'


def handle_bug(instance: Instance, mut_instance: Instance = None,
               message: str = None):
    global counter, without_bug_counter

    group = instance.get_group()
    counter['bug'] += 1

    model_state = mut_instance.model_info[0] \
        if mut_instance \
        else instance.model_info[0]
    status = 'bug' if model_state == sat else 'wrong_model'
    # if model_state != 'unknown':
    #     without_bug_counter[group.filename] = 0
    log_run_info(status,
                 group,
                 message,
                 instance,
                 mut_instance)

    if mut_instance:
        mut_instance.dump('output/bugs',
                          group.filename,
                          to_name=mut_instance.id)
    else:
        instance.dump('output/bugs',
                      group.filename,
                      to_name=0)
        group.reset()


def ensure_current_context_is_deletable():
    global current_ctx
    refs = gc.get_referrers(current_ctx)
    if len(refs) > 1:
        # dot_file = io.StringIO()
        # objgraph.show_backrefs([current_ctx],
        #                        max_depth=7,
        #                        output=dot_file)
        # dot_file.seek(0)
        logging.error(json.dumps({'context_deletion_error': {
            # 'refs': str(refs),
            # 'grapf': dot_file.read()
        }}))
        current_ctx.__del__()


def fuzz(files: set):
    global queue, current_ctx, counter, without_bug_counter

    run_seeds(files)
    logging.info(json.dumps({'seed_number': seed_number,
                             'heuristic': heuristic,
                             'mutations': mutations,
                             'options': options}))
    if with_weights:
        runs_before_weight_update = MUT_WEIGHT_UPDATE_RUNS

    while queue:
        assert len(queue) == seed_number - counter['error']

        select_time = time.perf_counter()
        instance = next_instance()
        select_time = time.perf_counter() - select_time

        counter['runs'] += 1
        group = instance.get_group()
        try:
            instances.set_ctx(None)
            ensure_current_context_is_deletable()
            current_ctx = Context()
            instances.set_ctx(current_ctx)

            is_seed = len(group.instances) == 1
            instance.restore(is_seed=is_seed)

            if with_weights:
                if runs_before_weight_update <= 0:
                    update_mutation_weights()
                    runs_before_weight_update = MUT_WEIGHT_UPDATE_RUNS

            i = 0
            problems_num = 0
            mut_types_exc = set()

            while i < ONE_INST_MUT_LIMIT:
                trace_time = 0
                model_time = 0
                if i > 0:
                    counter['runs'] += 1
                i += 1
                if with_weights:
                    runs_before_weight_update -= 1
                # without_bug_counter[group.filename] += 1

                mut_instance = Instance()
                mut = mut_instance.mutation
                if mut_types_exc:
                    mut.exceptions = mut_types_exc
                mut_time = time.perf_counter()
                mut.apply(instance, mut_instance)
                mut_time = time.perf_counter() - mut_time
                mut_instance.dump('output/mutants',
                                  group.filename,
                                  to_name=mut_instance.id,
                                  clear=False)

                if mut.changed:
                    mut_types_exc = set()
                    try:
                        solve_time = time.perf_counter()
                        res = check_satis(mut_instance, group)
                        solve_time = time.perf_counter() - solve_time
                        trace_changed = (instance.trace_stats.hash !=
                                         mut_instance.trace_stats.hash)
                        trace_time = time.perf_counter()
                        get_trace_stats(mut_instance, trace_changed=trace_changed)
                        trace_time = time.perf_counter() - trace_time
                    except AssertionError as err:
                        analyze_check_exception(instance,
                                                err,
                                                mut_instance=mut_instance)

                        problems_num += 1
                        if problems_num == PROBLEMS_LIMIT:
                            i = ONE_INST_MUT_LIMIT
                        print_general_info(mut_time)
                        instance = group[0]
                        mut_instance.reset_chc()
                        continue

                    if not res:
                        handle_bug(instance, mut_instance)
                        problems_num += 1

                    elif mut.is_timeout:
                        counter['timeout'] += 1
                        log_run_info('mutant_timeout',
                                     group,
                                     instance=instance,
                                     mut_instance=mut_instance)
                        problems_num += 1
                        group.roll_back()
                        instance = group[0]

                        mut_instance.reset_chc()

                    else:
                        model_time = time.perf_counter()
                        message = mut_instance.check_model()
                        model_time = time.perf_counter() - model_time
                        if mut_instance.model_info[0] != sat and message != 'timeout':
                            handle_bug(instance, mut_instance, message)
                            problems_num += 1
                        else:
                            status = 'model_timeout' if message == 'timeout' else 'pass'
                            group.push(mut_instance)
                            if heuristic != 'default':
                                group.check_stats()
                            log_run_info(status,
                                         group,
                                         instance=instance,
                                         mut_instance=mut_instance)
                            instance = mut_instance

                    print_general_info(solve_time,
                                       mut_time,
                                       trace_time,
                                       model_time,
                                       select_time,
                                       trace_changed)
                    if select_time:
                        select_time = 0

                else:
                    instance.inc_mutation_stats('applications')
                    exc_type = instance.mutation.type
                    mut_types_exc.add(exc_type)
                    log_run_info('without_change',
                                 group,
                                 instance=instance,
                                 mut_instance=mut_instance)
                    print_general_info(mut_time=mut_time,
                                       select_time=select_time)

                    mut_instance.reset_chc()

                if problems_num == PROBLEMS_LIMIT:
                    i = ONE_INST_MUT_LIMIT

            instance.dump('output/last_mutants',
                          group.filename)
            group.reset()
            queue.append(instance)

        except Exception as err:
            message = traceback.format_exc()
            analyze_check_exception(instance,
                                    err,
                                    message=message)
            print(group.filename)
            print(message)
            print_general_info()


def set_arg_parameters(argv: argparse.Namespace):
    global mutations, heuristic, options
    set_solver(argv.solver)

    heuristic = argv.heuristic
    set_heuristic(heuristic)

    mutations = argv.mutations
    options = argv.options
    init_mut_types(options, mutations)


def main():
    global general_stats, seed_number

    parser = argparse.ArgumentParser()
    parser.add_argument('seeds',
                        nargs='*',
                        default='',
                        help='directory with seeds or keyword \'all\'')
    parser.add_argument('-heuristic', '-heur',
                        nargs='?',
                        choices=['default', 'transitions', 'states',
                                 'difficulty', 'simplicity'],
                        default='default',
                        help='trace data which will be used to '
                             'select an instance for mutation')
    parser.add_argument('-solver', '-s',
                        nargs='?',
                        choices=['spacer', 'eldarica'],
                        default='spacer')
    parser.add_argument('-mutations', '-mut',
                        nargs='*',
                        choices=['simplifications', 'spacer_parameters',
                                 'own'],
                        default=['simplifications', 'spacer_parameters',
                                 'own'])
    parser.add_argument('-options', '-opt',
                        nargs='*',
                        choices=['without_mutation_weights'],
                        default=[])
    argv = parser.parse_args()

    # help_simplify()
    logging.basicConfig(format='%(message)s',
                        filename='logfile',
                        filemode='w',
                        level=logging.INFO)

    np.set_printoptions(suppress=True)
    set_option(max_args=int(1e6), max_lines=int(1e6),
               max_depth=int(1e6), max_visited=int(1e6))

    set_arg_parameters(argv)
    if heuristic in {'transitions', 'states'}:
        general_stats = TraceStats()
        assert solver == 'spacer'

    directory = os.path.dirname(os.path.dirname(parser.prog))
    if directory:
        directory += '/'
    files = get_seeds(argv.seeds, directory)
    create_output_dirs()

    seed_number = len(files)
    assert seed_number > 0, 'Seeds not found'

    fuzz(files)


def create_output_dirs():
    """Create directories for storing instances"""

    if not os.path.exists('output'):
        os.mkdir('output')
    for dir in {'output/last_mutants', 'output/decl',
                'output/bugs', 'output/unknown', 'output/mutants'}:
        if not os.path.exists(dir):
            os.mkdir(dir)
        if dir != 'output':
            for benchmark_dir in {'spacer-benchmarks/',
                                  'chc-comp21-benchmarks/',
                                  'sv-benchmarks-clauses/'}:
                for subdir in os.walk(benchmark_dir):
                    dir_path = dir + '/' + subdir[0]
                    if not os.path.exists(dir_path):
                        os.mkdir(dir_path)


if __name__ == '__main__':
    main()
