import argparse
import faulthandler
import itertools
import logging
import base64
import os.path
from typing import Optional

import instances
from instances import *
import file_handler

import z3_api_mods
from seed_info_utils import *
from log_analysis import prepare_data

faulthandler.enable()
enable_trace('spacer')
enable_trace('dl_rule_transf')

heuristic = 'default'
mutations = []

seed_number = 0
restore = False
queue = []
general_stats = None
counter = defaultdict(int)
log = dict()


def calculate_weights() -> list:
    if heuristic in {'transitions', 'states'}:
        weighted_stats = general_stats.get_weighted_stats()
        shape = weighted_stats.shape
    weights = []
    rev_times = []

    for instance in queue:
        stats = instance.trace_stats
        weight = 1e-5
        if heuristic != 'default':
            rev_time = (1/instance.solve_time - 1)/(1/abs(instance.solve_time) + 1) + 1 \
                if instance.solve_time else 0.05
            rev_times.append(rev_time)
            if heuristic == 'transitions':
                weight = stats.matrix.toarray()
                weight.resize(shape)
            elif heuristic == 'states':
                states_prob = stats.get_probability()
                weight = sum(states_prob[state] * weighted_stats[state]
                             for state in stats.states_num)
            else:
                group = instance.get_group()
                is_nonlinear = not group.is_linear
                upred_num = group.upred_num
                weight += 10 * is_nonlinear + upred_num
        weights.append(weight)
    
    if heuristic == 'transitions':
        weights = np.stack(weights)
        weights = np.matmul(weights, weighted_stats.toarray())
        weights = np.sum(weights, axis=(1, 2))
        weights *= np.array(rev_times)

    weights = normalize([weights], 'max')[0]
    return weights


def get_trace_stats(instance: Instance, is_seed: bool = False,
                    trace_changed: bool = False):
    global general_stats

    instance.trace_stats.read_from_trace(is_seed)
    instance.update_traces_info(is_seed=is_seed)

    if not is_seed:
        instance.inc_mutation_stats('applications')
        instance.inc_mutation_stats('changed_traces', int(trace_changed))
        instance.inc_mutation_stats('new_transitions', instance.trace_stats.new_transitions)

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
    global queue, log
    weights = calculate_weights()
    if heuristic == 'simplicity':
        weights = reversed(weights)
    next_instance = random.choices(queue, weights, k=1)[0]
    queue.remove(next_instance)

    trace_hashes = []
    for hash in unique_traces:
        encoded = base64.b64encode(hash)
        trace_hashes.append(encoded.decode('ascii'))
    logging.info(json.dumps({'trace_hashes': trace_hashes},
                            cls=MutTypeEncoder))
    return next_instance


def update_mutation_weights():
    instances.update_mutation_weights()
    logging.info(json.dumps({'mutation_weights': get_mut_weights_dict()},
                            cls=MutTypeEncoder))


def print_general_info(solve_time: time = None, mut_time: time = None, trace_time: time = None,
                       model_time: time = None, select_time: time = None,
                       trace_changed: bool = None):
    """Print and log information about runs."""
    global counter, log

    if counter['runs']:
        print('Total:', counter['runs'],
              'Bugs:', counter['bug'],
              'Timeout:', counter['timeout'],
              'Unknown:', counter['unknown'],
              'Errors:', counter['error'])
        for key in {'runs', 'bug', 'timeout', 'unknown', 'error'}:
            log[key] = counter[key]

    log['current_time'] = time.perf_counter()
    for time_name in {'solve_time', 'mut_time', 'trace_time',
                      'model_time', 'select_time'}:
        time_value = locals()[time_name]
        if time_value:
            log[time_name] = time_value

    traces_num = len(unique_traces)
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
            elif status == 'last_mutants':
                log['mut_chain'] = instance.mutation.get_chain()
            else:
                log['satis'] = instance.satis.r

    if mut_instance:
        mutant_info = mut_instance.get_log(group)
        log.update(mutant_info)
        if status not in {'pass', 'without_change'}:
            log['mut_chain'] = instance.mutation.get_chain()
            last_mutation = mut_instance.mutation
            log['mut_chain'].append(last_mutation.get_name())
            if status in {'bug', 'wrong_model', 'model_unknown',
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
            mut_instance.dump(output_dir + 'unknown/',
                              group.filename,
                              message=message,
                              to_name=mut_instance.id)
        elif status == 'timeout_before_check':
            group[0].dump(output_dir + 'last_mutants/',
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
            seed = seed.translate(ctx.current_ctx)
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
        instance.solve_time = solve_time
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
            solve_time = time.perf_counter()
            check_satis(instance, is_seed=True)
            solve_time = time.perf_counter() - solve_time
            instance.solve_time = solve_time
            get_trace_stats(instance, is_seed=True)
            message = instance.check_model()
            if instance.model_info[0] != sat:
                handle_bug(instance,
                           message=message)
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


def run_seeds(files):
    """Read and solve the seeds."""
    global queue, seed_number, counter

    ctx.set_ctx(Context())
    seed_info_index = build_seed_info_index()
    known_seed_files = files & set(seed_info_index.keys())
    other_seed_files = files - known_seed_files
    known_seeds = known_seeds_processor(known_seed_files, 0, seed_info_index)
    other_seeds = new_seeds_processor(other_seed_files, len(known_seed_files), seed_info_index)

    for i, (instance, solve_time) in enumerate(itertools.chain(known_seeds, other_seeds)):
        queue.append(instance)
        log_run_info('seed', instance.get_group(), instance=instance)
        print_general_info(solve_time=solve_time)

    set_seed_num()


def handle_bug(instance: Instance, mut_instance: Instance = None,
               message: str = None):
    global counter

    group = instance.get_group()
    counter['bug'] += 1

    model_state = mut_instance.model_info[0] \
        if mut_instance \
        else instance.model_info[0]
    status = 'bug' if model_state != unsat else 'wrong_model'
    log_run_info(status,
                 group,
                 message,
                 instance,
                 mut_instance)

    if mut_instance:
        mut_instance.dump(output_dir + 'bugs/',
                          group.filename,
                          to_name=mut_instance.id)
    else:
        instance.dump(output_dir + 'bugs/',
                      group.filename,
                      to_name=0)
        group.reset()


def set_seed_num():
    global seed_number
    seed_number = len(queue)
    assert seed_number > 0, 'All seeds are unknown or in the incorrect format'


def restore_data(files):
    global counter, log
    stats = prepare_data(LAST_LOG_NAME)
    df = stats.df
    runs_df = df[df['runs'].notnull()]
    last_row = runs_df.tail(1)
    for key in {'runs', 'bug', 'timeout', 'unknown', 'error'}:
        counter[key] = int(last_row[key])

    if stats.trace_hashes:
        trace_hashes = set()
        for hash in stats.trace_hashes:
            trace_hashes.add(base64.b64decode(hash))
        set_known_trace(trace_hashes)
        counter['unique_traces'] = len(trace_hashes)

    ctx.set_ctx(Context())
    for file in files:
        group, mutations, _ = file_handler.restore_group(file, with_mutations=False)
        group.mutations = mutations
        instance = Instance()
        group.push(instance)
        file_rows = df.loc[df['filename'] == group.filename]
        last_row = file_rows.tail(1)
        log.update(last_row.to_dict('records')[0])
        try:
            instance.restore(is_seed=False)
        except AssertionError:
            print(traceback.format_exc())
            print_general_info()
            continue
        try:
            solve_time = time.perf_counter()
            check_satis(instance, is_seed=True)
            solve_time = time.perf_counter() - solve_time
            instance.solve_time = solve_time
            get_trace_stats(instance, is_seed=True)
        except Exception:
            print_general_info()
            continue

        print_general_info(solve_time=solve_time)
        queue.append(instance)
    set_seed_num()


def fuzz(files):
    global queue, counter

    if restore:
        restore_data(files)
    else:
        run_seeds(files)
    logging.info(json.dumps({'seed_number': seed_number,
                             'heuristic': heuristic,
                             'mutations': mutations,
                             'options': options}))
    if with_weights:
        runs_before_weight_update = MUT_WEIGHT_UPDATE_RUNS

    while queue:

        select_time = time.perf_counter()
        instance = next_instance()
        select_time = time.perf_counter() - select_time

        counter['runs'] += 1
        group = instance.get_group()
        try:
            message = ctx.ensure_current_context_is_deletable()
            if message:
                logging.error(json.dumps(message))
            ctx.set_ctx(Context())

            is_seed = len(group.instances) == 1
            if not restore:
                instance.restore(is_seed=is_seed)
            else:
                group.pop()
                group.restore(group.mutations)
                instance = group[-1]

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

                mut_instance = Instance()
                mut = mut_instance.mutation
                if mut_types_exc:
                    mut.exceptions = mut_types_exc
                mut_time = time.perf_counter()
                mut.apply(instance, mut_instance)
                mut_time = time.perf_counter() - mut_time

                if mut.changed:
                    mut_types_exc = set()
                    try:
                        solve_time = time.perf_counter()
                        res = check_satis(mut_instance, group)
                        solve_time = time.perf_counter() - solve_time
                        instance.solve_time = solve_time
                        trace_changed = (instance.trace_stats.hash !=
                                         mut_instance.trace_stats.hash)
                        trace_time = time.perf_counter()
                        get_trace_stats(mut_instance, trace_changed=trace_changed)
                        trace_time = time.perf_counter() - trace_time
                    except (AssertionError, TimeoutError) as err:
                        analyze_check_exception(instance,
                                                err,
                                                mut_instance=mut_instance)

                        problems_num += 1
                        if problems_num == PROBLEMS_LIMIT:
                            i = ONE_INST_MUT_LIMIT
                        instance = group[0]
                        mut_instance.reset_chc()
                        print_general_info(mut_time=mut_time,
                                           trace_time=trace_time,
                                           select_time=select_time)
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
                        if mut_instance.model_info[0] == unsat and message != 'timeout':
                            handle_bug(instance, mut_instance, message)
                            problems_num += 1
                        else:
                            if message == 'timeout':
                                status = 'model_timeout'
                            elif mut_instance.model_info[0] == unknown:
                                status = 'model_unknown'
                            else:
                                status = 'pass'
                                group.push(mut_instance)
                            if heuristic != 'default':
                                group.check_stats()
                            log_run_info(status,
                                         group,
                                         instance=instance,
                                         mut_instance=mut_instance)
                            if status == 'pass':
                                instance = mut_instance

                    print_general_info(solve_time=solve_time,
                                       mut_time=mut_time,
                                       trace_time=trace_time,
                                       model_time=model_time,
                                       select_time=select_time,
                                       trace_changed=trace_changed)
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

            instance.dump(output_dir + 'last_mutants/',
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
            print_general_info(select_time=select_time)


def set_arg_parameters(argv: argparse.Namespace):
    global mutations, heuristic, options, restore
    set_solver(argv.solver)

    heuristic = argv.heuristic
    set_heuristic(heuristic)

    mutations = argv.mutations
    options = argv.options
    restore = 'restore' in options
    init_mut_types(options, mutations)


def main():
    global general_stats, seed_number, restore

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
                                 'own', 'eldarica_parameters'],
                        default=['simplifications', 'spacer_parameters',
                                 'own', 'eldarica_parameters'])
    parser.add_argument('-options', '-opt',
                        nargs='*',
                        choices=['without_mutation_weights', 'restore'],
                        default=[])
    argv = parser.parse_args()

    # help_simplify()

    np.set_printoptions(suppress=True)
    set_option(max_args=int(1e6), max_lines=int(1e6),
               max_depth=int(1e6), max_visited=int(1e6))

    set_arg_parameters(argv)
    if restore:
        if not os.path.exists(LAST_LOG_NAME) or os.stat(LAST_LOG_NAME).st_size == 0:
            if not os.path.exists(LOG_NAME) or os.stat(LOG_NAME).st_size == 0:
                 restore = False
            else:
                os.rename(LOG_NAME, LAST_LOG_NAME)

    if heuristic in {'transitions', 'states'}:
        general_stats = TraceStats()
        assert solver == 'spacer'

    directory = os.path.dirname(os.path.dirname(parser.prog))
    if directory:
        directory += '/'
    file_handler.create_output_dirs()
    seed_files = file_handler.get_seeds(argv.seeds, directory, restore)
    mode = 'w' if not restore else 'a'
    logging.basicConfig(format='%(message)s',
                        filename=LOG_NAME,
                        filemode=mode,
                        level=logging.INFO)

    seed_number = len(seed_files)
    assert seed_number > 0, 'Seeds not found'

    fuzz(seed_files)


if __name__ == '__main__':
    main()
