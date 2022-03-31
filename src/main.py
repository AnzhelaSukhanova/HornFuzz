import argparse
import faulthandler
import gc
import logging
import itertools
from typing import Optional

import objgraph
import os.path

import instances
import oracles
from instances import *
from seeds import *
from seed_info_utils import *

# noinspection PyUnresolvedReferences
import z3_api_mods

faulthandler.enable()
enable_trace('spacer')
enable_trace('dl_rule_transf')

heuristics = []
heuristic_flags = defaultdict(bool)
mutations = []
options = []

seed_number = 0
queue = []
current_ctx = None
general_stats = None
counter = defaultdict(int)

PROBLEMS_LIMIT = 10
MUT_WEIGHT_UPDATE_RUNS = 10000

with_oracles = False
oracles_names = {'Eldarica'}


def calc_sort_key(heuristic: str, stats, weights=None) -> int:
    """Calculate the priority of an instance in the sorted queue."""

    if heuristic == 'transitions':
        prob_matrix = stats.get_probability(StatsType.TRANSITIONS)
        size = stats.matrix.shape[0]
        weight_matrix_part = weights[:size, :size]
        trans_matrix = stats.matrix
        sort_key = np.sum(prob_matrix * trans_matrix * weight_matrix_part)
    elif heuristic == 'states':
        states_prob = stats.get_probability(StatsType.STATES)
        sort_key = sum(states_prob[state] * weights[state]
                       for state in stats.states_num)
    elif heuristic == 'difficulty':
        is_nonlinear = not stats[0]
        upred_num = stats[1]
        sort_key = (is_nonlinear, upred_num)
    else:
        assert False, "Incorrect heuristic"
    return sort_key


def check_satis(instance: Instance, is_seed: bool = False, get_stats: bool = True):
    global general_stats

    solver = SolverFor('HORN',
                       ctx=instances.current_ctx)
    solver.set('engine', 'spacer')

    if not is_seed:
        seed = instance.get_group()[0]
        if seed.satis == unknown:
            seed.check(solver, is_seed=True, get_stats=get_stats)
        satis = seed.satis

    for param in instance.params:
        value = instance.params[param]
        solver.set(param, value)

    instance.check(solver, is_seed, get_stats)
    if is_seed:
        satis = instance.satis

    if get_stats and (heuristic_flags['transitions'] or
                      heuristic_flags['states']):
        general_stats += instance.trace_stats
    return instance.satis == satis


def sort_queue():
    """Sort the queue by statistics."""
    global queue

    if heuristic_flags['default']:
        return

    length = len(heuristics)
    for i in range(length):
        heur = heuristics[i]
        if heur in {'transitions', 'states'}:
            type = StatsType.TRANSITIONS if heur == 'transitions' \
                else StatsType.STATES
            weights = general_stats.get_weights(type)
        chunk_size = len(queue) // (i + 1)
        queue_chunks = [queue[j:j + chunk_size]
                        for j in range(0, len(queue), chunk_size)]
        queue = []
        for chunk in queue_chunks:
            for instance in chunk:
                if heur == 'transitions' or heur == 'states':
                    ins_stats = instance.trace_stats
                    instance.sort_key = calc_sort_key(heur,
                                                      ins_stats,
                                                      weights)
                else:
                    group = instance.get_group()
                    instance.sort_key = calc_sort_key(heur,
                                                      (group.is_linear,
                                                       group.upred_num))
            chunk.sort(key=lambda item: item.sort_key, reverse=True)
            queue += chunk


def update_mutation_weights():
    instances.update_mutation_weights()
    logging.info(json.dumps({'update_mutation_weights':
                                 instances.get_mut_weights_dict()},
                            cls=MutTypeEncoder))


def print_general_info(solve_time: time = None, mut_time: time = None,
                       trace_changed: bool = None):
    """Print and log information about runs."""
    global counter

    traces_num = len(unique_traces)
    log = {'runs': counter['runs'],
           'current_time': time.perf_counter()}
    if solve_time:
        log['solve_time'] = solve_time
    if mut_time:
        log['mut_time'] = mut_time
    if trace_changed is not None:
        log['trace_changed'] = trace_changed
    if counter['runs']:
        print('Total:', counter['runs'],
              'Bugs:', counter['bug'],
              'Timeout:', counter['timeout'],
              'Unknown:', counter['unknown'],
              'Errors:', counter['error'])
        if with_oracles and counter['runs'] > seed_number:
            print('Solver conflicts:', counter['conflict'])
    log['unique_traces'] = traces_num
    if traces_num:
        print('Unique traces:', traces_num, '\n')
    else:
        print()
    logging.info(json.dumps({'general_info': log}))


def log_run_info(status: str, message: str = None,
                 instance: Instance = None, mut_instance: Instance = None):
    """Create a log entry with information about the run."""

    log = {'status': status}
    if message:
        log['message'] = message
    if instance:
        if not mut_instance:
            instance_info = instance.get_log(is_mutant=False)
            log.update(instance_info)
            if status == 'error':
                if instance.chc:
                    log['chc'] = instance.chc.sexpr()
                chain = instance.mutation.get_chain()
                log['mut_chain'] = chain
            else:
                log['satis'] = instance.satis.r

        else:
            mutant_info = mut_instance.get_log()
            log.update(mutant_info)
            if status not in {'pass', 'without_change'}:
                chain = mut_instance.mutation.get_chain()
                log['mut_chain'] = chain
                if status in {'bug', 'wrong_model',
                              'mutant_unknown', 'error'}:
                    log['satis'] = mut_instance.satis.r
                    if status == 'wrong_model':
                        log['model_state'] = mut_instance.model_info[0].r
                        log['bug_clause'] = str(mut_instance.model_info[1])

    logging.info(json.dumps({'run_info': log}))


def analyze_check_exception(instance: Instance, err: Exception,
                            message: str = None, mut_instance: Instance = None,
                            is_seed: bool = False):
    """Log information about exceptions that occur during the check."""
    global counter
    group = instance.get_group()

    if is_seed:
        if str(err) == 'timeout':
            counter['timeout'] += 1
            status = 'seed_timeout'
        elif message:
            counter['error'] += 1
            status = 'error'
        else:
            counter['unknown'] += 1
            status = 'seed_unknown'
            message = repr(err)
        log_run_info(status,
                     message,
                     instance)
    else:
        if not message:
            message = repr(err)
        if str(err) == 'timeout' or isinstance(err, TimeoutError):
            counter['timeout'] += 1
            status = 'mutant_timeout' if mut_instance \
                else 'timeout_before_check'
            log_run_info(status,
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
                         message,
                         instance,
                         mut_instance)
        if status == 'unknown':
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
    instance = Instance(idx)
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
        if heuristic_flags['transitions'] or heuristic_flags['states']:
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
        log_run_info('seed', instance=instance)
        print_general_info(solve_time=solve_time)
    seed_number = len(queue)

    assert seed_number > 0, 'All seeds are unknown or ' \
                            'in the incorrect format'


def handle_bug(instance: Instance, mut_instance: Instance = None,
               message: str = None):
    global counter

    counter['bug'] += 1
    model_state = mut_instance.model_info[0] \
        if mut_instance \
        else instance.model_info[0]
    status = 'bug' if model_state == sat else 'wrong_model'
    log_run_info(status,
                 message=message,
                 instance=instance,
                 mut_instance=mut_instance)

    group = instance.get_group()
    if mut_instance:
        mut_instance.dump('output/bugs',
                          group.filename,
                          to_name=mut_instance.id)
    else:
        instance.dump('output/bugs',
                      group.filename,
                      to_name=0)
        group.reset()


def compare_satis(instance: Instance, is_seed: bool = False):
    group = instance.get_group()
    states = defaultdict()
    found_problem = False

    if not is_seed:
        instance.dump('output/last_mutants/',
                      group.filename,
                      clear=False)
        filename = 'output/last_mutants/' + group.filename
    else:
        filename = group.filename
    for name in oracles_names:
        state = oracles.solve(name, filename)
        states[name] = state
        if state != instance.satis.r and state in {'sat', 'unsat'}:
            found_problem = True
    return found_problem, states


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
    global queue, current_ctx, counter

    run_seeds(files)
    logging.info(json.dumps({'seed_number': seed_number,
                             'heuristics': heuristics,
                             'mutations': mutations,
                             'options': options}))
    if with_weights:
        runs_before_weight_update = MUT_WEIGHT_UPDATE_RUNS

    while queue:
        assert len(queue) == seed_number - counter['error']

        sort_queue()

        instance = queue.pop(0)
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
                if i > 0:
                    counter['runs'] += 1
                i += 1
                if with_weights:
                    runs_before_weight_update -= 1

                mut_instance = Instance(instance.group_id)
                mut = mut_instance.mutation
                if mut_types_exc:
                    mut.exceptions = mut_types_exc
                mut_time = time.perf_counter()
                timeout, changed = mut.apply(instance, mut_instance)
                mut_time = time.perf_counter() - mut_time
                mut_instance.update_mutation_stats(new_application=True)

                if changed:
                    mut_types_exc = set()
                    try:
                        st_time = time.perf_counter()
                        res = check_satis(mut_instance)
                        solve_time = time.perf_counter() - st_time
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

                    trace_changed = (instance.trace_stats.hash !=
                                     mut_instance.trace_stats.hash)
                    mut_instance.update_mutation_stats(new_trace_found=trace_changed)

                    if not res:
                        handle_bug(instance, mut_instance)
                        problems_num += 1

                    elif timeout:
                        counter['timeout'] += 1
                        log_run_info('mutant_timeout',
                                     instance=instance,
                                     mut_instance=mut_instance)
                        problems_num += 1
                        group.roll_back()
                        instance = group[0]

                        mut_instance.reset_chc()

                    else:
                        message = mut_instance.check_model()
                        if mut_instance.model_info[0] != sat and message != 'timeout':
                            handle_bug(instance, mut_instance, message)
                            problems_num += 1
                        else:
                            status = 'model_timeout' if message == 'timeout' else 'pass'

                            if with_oracles:
                                found_problem, states = compare_satis(mut_instance)
                            else:
                                found_problem = False
                            group.push(mut_instance)
                            if not heuristic_flags['default']:
                                group.check_stats()

                            if found_problem:
                                log_run_info('oracle_bug',
                                             message=str(states),
                                             instance=instance,
                                             mut_instance=mut_instance)
                                counter['conflict'] += 1
                            else:
                                log_run_info(status,
                                             instance=instance,
                                             mut_instance=mut_instance)
                            instance = mut_instance

                    print_general_info(solve_time,
                                       mut_time,
                                       trace_changed)

                else:
                    exc_type = instance.mutation.type
                    mut_types_exc.add(exc_type)
                    log_run_info('without_change',
                                 instance=instance,
                                 mut_instance=mut_instance)
                    print_general_info()

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


def main():
    global general_stats, heuristics, heuristic_flags, \
        mutations, options, seed_number, with_oracles

    parser = argparse.ArgumentParser()
    parser.add_argument('seeds',
                        nargs='*',
                        default='',
                        help='directory with seeds or keyword \'all\'')
    parser.add_argument('-heuristics', '-heur',
                        nargs='*',
                        choices=['transitions', 'states', 'difficulty'],
                        default=['default'],
                        help='trace data which will be used to '
                             'select an instance for mutation')
    parser.add_argument('-mutations', '-mut',
                        nargs='*',
                        choices=['simplifications', 'solving_parameters',
                                 'own'],
                        default=[])
    parser.add_argument('-options', '-opt',
                        nargs='*',
                        choices=['without_mutation_weights', 'with_oracles'],
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

    heuristics = argv.heuristics
    for heur in heuristics:
        heuristic_flags[heur] = True
    set_stats_type(heuristic_flags)
    if heuristic_flags['transitions'] or heuristic_flags['states']:
        general_stats = TraceStats()
        
    options = argv.options
    with_oracles = 'with_oracles' in options
    mutations = argv.mutations

    directory = os.path.dirname(os.path.dirname(parser.prog))
    if directory:
        directory += '/'
    files = get_seeds(argv.seeds, directory)
    create_output_dirs()
    init_mut_types(options, mutations)

    seed_number = len(files)
    assert seed_number > 0, 'Seeds not found'

    fuzz(files)


def create_output_dirs():
    """Create directories for storing instances"""

    if not os.path.exists('output'):
        os.mkdir('output')
    for dir in {'output/last_mutants', 'output/decl',
                'output/bugs', 'output/unknown'}:
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
