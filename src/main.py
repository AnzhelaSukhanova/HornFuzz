import argparse
import faulthandler
import gc
import logging
import traceback
import itertools
from typing import Optional

import objgraph
import os.path

import instances
import oracles
from instances import *
from seeds import *

# noinspection PyUnresolvedReferences
import z3_api_mods

faulthandler.enable()

general_stats = None
seed_number = 0
heuristics = ''
heuristic_flags = defaultdict(bool)
queue = []
current_ctx = None

ONE_INST_MUT_LIMIT = 1000
MUT_AFTER_PROBLEM = 10
MUT_WEIGHT_UPDATE_RUNS = 10000
seed_info_file = 'seed_info.json'
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


def check_satis(instance: Instance, is_seed: bool = False, get_stats: bool = True) -> bool:
    """
    Return True if the test suites have the same satisfiability and
    False otherwise.
    """

    global general_stats
    ctx = instance.chc.ctx
    solver = SolverFor('HORN', ctx=ctx)
    solver.set('engine', 'spacer')

    instance.check(solver, is_seed, get_stats)
    group = instance.get_group()
    satis = group[-1].satis if not is_seed else instance.satis

    if get_stats and (heuristic_flags['transitions'] or
                      heuristic_flags['states']):
        general_stats += instance.trace_stats
    return instance.satis == satis


def sort_queue():
    """Sort the queue by statistics."""

    global queue
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
    logging.info(json.dumps({'update_mutation_weights': instances.mut_types}))


def print_general_info(counter: defaultdict, solve_time: time = None,
                       mut_time: time = None, trace_has_changed: bool = None):
    """Print and log information about runs."""

    traces_num = len(unique_traces)
    log = {'runs': counter['runs'],
           'current_time': time.perf_counter()}
    if solve_time:
        log['solve_time'] = solve_time
    if mut_time:
        log['mut_time'] = mut_time
    if trace_has_changed is not None:
        log['trace_has_changed'] = trace_has_changed
    if counter['runs']:
        print('Total:', counter['runs'],
              'Bugs:', counter['bug'],
              'Timeout:', counter['timeout'],
              'Unknown:', counter['unknown'],
              'Errors:', counter['error'])
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
            elif status == 'seed':
                log['satis'] = str(instance.satis)

        else:
            mutant_info = mut_instance.get_log()
            log.update(mutant_info)
            if status != 'pass':
                chain = mut_instance.mutation.get_chain()
                log['mut_chain'] = chain
                if status in {'bug', 'mutant_unknown'}:
                    log['prev_chc'] = instance.chc.sexpr()
                    log['excepted_satis'] = str(instance.satis)

    logging.info(json.dumps({'run_info': log}))


def analyze_check_exception(instance: Instance, err: Exception,
                            counter: defaultdict, message: str = None,
                            mut_instance: Instance = None,
                            is_seed: bool = False):
    """Log information about exceptions that occur during the check."""
    global queue
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
        if status != 'error':
            group.roll_back()
            if status == 'timeout_before_check':
                group[0].dump('output/last_mutants', group.filename)
            queue.append(group[0])

    if status == 'error':
        for inst in group.instances.values():
            del inst.chc, inst
        del group


def load_seed_info():
    if os.path.isfile(seed_info_file) and \
            os.stat(seed_info_file).st_size > 0:
        with open(seed_info_file, 'r') as file:
            return json.load(file)
    return {}


def dump_seed_info(seed_info):
    current_seed_info = load_seed_info()
    for seed, data in seed_info.items():
        current_seed_info[seed] = data
    with open(seed_info_file, 'w+') as file:
        json.dump(current_seed_info, file, indent=2)


def mk_seed_instance(ctx: Context, idx: int, seed_file_name: str, counter) -> Optional[Instance]:
    group = InstanceGroup(idx, seed_file_name)
    instance = Instance(idx)
    try:
        parse_ctx = Context()
        seed = parse_smt2_file(seed_file_name, ctx=parse_ctx)
        seed = seed.translate(ctx)
        if not seed:
            return None
        instance.set_chc(seed)
        group.same_stats_limit = 5 * len(seed)
        group.push(instance)
        return instance
    except Exception as err:
        message = traceback.format_exc()
        analyze_check_exception(instance, err, counter, message=message, is_seed=True)
        print(message)
        print_general_info(counter)
        return None


def mk_known_seeds_processor(ctx: Context, files: set, counter):
    seed_info = load_seed_info()
    known_seeds = files & set(seed_info.keys())
    other_seeds = files - known_seeds

    def seed_processor():
        for i, seed in enumerate(known_seeds):
            info = seed_info[seed]
            if 'error' in info:
                continue
            instance = mk_seed_instance(ctx, i, seed, counter)
            if instance is None:
                continue
            counter['runs'] += 1
            solve_time = instance.process_seed_info(info)
            instance.update_traces_info()
            yield instance, solve_time

    return other_seeds, len(known_seeds), seed_processor


def mk_new_seeds_processor(ctx: Context, files: set, base_idx: int, counter):
    def seed_processor():
        seed_info = {}
        for i, seed in enumerate(files, start=base_idx):
            instance = mk_seed_instance(ctx, i, seed, counter)
            if instance is None:
                seed_info[seed] = {'error': 'error at instance creation'}
                continue
            counter['runs'] += 1
            try:
                st_time = time.perf_counter()
                check_satis(instance, is_seed=True)
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
                                        counter,
                                        is_seed=True)
                print_general_info(counter)
                seed_info[seed] = {'error': 'error at seed check'}
            if (i + 1) % 300 == 0:
                dump_seed_info(seed_info)
        if seed_info:
            dump_seed_info(seed_info)

    return seed_processor


def run_seeds(files: set, counter: defaultdict):
    """Read and solve the seeds."""
    global queue, seed_number, current_ctx

    current_ctx = Context()
    new_seeds, new_seeds_instance_base_idx, known_seeds_processor = mk_known_seeds_processor(current_ctx, files, counter)
    new_seeds_processor = mk_new_seeds_processor(current_ctx, new_seeds, new_seeds_instance_base_idx, counter)

    for i, (instance, solve_time) in enumerate(itertools.chain(known_seeds_processor(), new_seeds_processor())):
        queue.append(instance)
        log_run_info('seed', instance=instance)
        print_general_info(counter, solve_time=solve_time)
    seed_number = len(queue)

    assert seed_number > 0, 'All seeds are unknown or ' \
                            'in the incorrect format'


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
        if state != str(instance.satis) and state in {'sat', 'unsat'}:
            found_problem = True
    return found_problem, states


def ensure_current_context_is_deletable():
    global current_ctx
    refs = gc.get_referrers(current_ctx)
    if len(refs) > 1:
        dot_file = io.StringIO()
        objgraph.show_backrefs([current_ctx],
                               max_depth=7,
                               output=dot_file)
        dot_file.seek(0)
        logging.error(json.dumps({'context_deletion_error': {
            'refs': str(refs),
            'grapf': dot_file.read()
        }}))
        current_ctx.__del__()


def fuzz(files: set):
    global queue, current_ctx

    counter = defaultdict(int)
    run_seeds(files, counter)
    init_runs_number = 2 * seed_number - \
                       counter['unknown'] - counter['timeout']
    logging.info(json.dumps({'seed_number': seed_number,
                             'heuristics': heuristics}))
    stats_limit = seed_number
    runs_before_weight_update = MUT_WEIGHT_UPDATE_RUNS

    while queue:
        instance = queue.pop(0)
        counter['runs'] += 1
        group = instance.get_group()
        try:
            if counter['runs'] > init_runs_number:
                ensure_current_context_is_deletable()
                start_mut_ind = len(group.instances) - 1
                instance.restore()
                current_ctx = instance.chc.ctx
                mut_limit = ONE_INST_MUT_LIMIT
            else:
                start_mut_ind = 0
                mut_limit = 1

            if runs_before_weight_update <= 0:
                update_mutation_weights()
                runs_before_weight_update = MUT_WEIGHT_UPDATE_RUNS

            stats_limit -= 1

            i = 0
            while i < mut_limit:
                if i > 0:
                    counter['runs'] += 1
                runs_before_weight_update -= 1

                mut_instance = Instance(instance.group_id)
                mut = mut_instance.mutation
                mut_time = time.perf_counter()
                timeout = mut.apply(instance, mut_instance)
                mut_time = time.perf_counter() - mut_time
                mut_instance.update_mutation_stats(new_application=True)

                try:
                    st_time = time.perf_counter()
                    res = check_satis(mut_instance)
                    solve_time = time.perf_counter() - st_time
                except AssertionError as err:
                    analyze_check_exception(instance,
                                            err,
                                            counter,
                                            mut_instance=mut_instance)
                    mut_instance.dump('output/problems',
                                      group.filename,
                                      len(group.instances),
                                      repr(err),
                                      mut_instance.id)
                    i = max(i + 1, mut_limit - MUT_AFTER_PROBLEM)
                    instance = group[0]
                    start_mut_ind = 0
                    print_general_info(counter, mut_time)
                    continue

                trace_has_changed = (instance.trace_stats.hash !=
                                     mut_instance.trace_stats.hash)
                mut_instance.update_mutation_stats(new_trace_found=trace_has_changed)

                if not res:
                    counter['bug'] += 1
                    log_run_info('bug',
                                 instance=instance,
                                 mut_instance=mut_instance)
                    i = max(i + 1, mut_limit - MUT_AFTER_PROBLEM)
                    if i == mut_limit - 1:
                        queue.append(instance)
                    mut_instance.dump('output/bugs',
                                      group.filename,
                                      len(group.instances),
                                      to_name=mut_instance.id)

                elif timeout:
                    counter['timeout'] += 1
                    log_run_info('simplify_timeout',
                                 instance=instance,
                                 mut_instance=mut_instance)
                    group.roll_back()
                    instance = group[0]
                    queue.append(instance)

                else:
                    found_problem, states = compare_satis(mut_instance)
                    if i == mut_limit - 1:
                        queue.append(mut_instance)
                    group.push(mut_instance)
                    if not heuristic_flags['default'] and \
                            len(instance_groups) > 1:
                        stats_limit = group.check_stats(stats_limit)
                    if found_problem:
                        log_run_info('oracle_bug',
                                     message=str(states),
                                     instance=instance,
                                     mut_instance=mut_instance)
                        counter['conflict'] += 1
                    else:
                        log_run_info('pass',
                                     instance=instance,
                                     mut_instance=mut_instance)
                    instance = mut_instance
                    i += 1

                print_general_info(counter,
                                   solve_time,
                                   mut_time,
                                   trace_has_changed)

            instance.dump('output/last_mutants',
                          group.filename,
                          start_mut_ind)

            if not heuristic_flags['default'] and not stats_limit:
                sort_queue()
                queue_len = len(queue)
                stats_limit = random.randint(queue_len // 5, queue_len)

        except Exception as err:
            message = traceback.format_exc()
            analyze_check_exception(instance,
                                    err,
                                    counter,
                                    message=message)
            print(group.filename)
            print(message)
            print_general_info(counter)


def main():
    global general_stats, heuristics, heuristic_flags, \
        seed_number, seed_info

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
    argv = parser.parse_args()

    # help_simplify()
    logging.basicConfig(format='%(message)s',
                        filename='logfile',
                        filemode='w',
                        level=logging.INFO)

    np.set_printoptions(suppress=True)
    set_option(max_args=int(1e6), max_lines=int(1e6),
               max_depth=int(1e6), max_visited=int(1e6))
    enable_trace('spacer')

    heuristics = argv.heuristics
    for heur in heuristics:
        heuristic_flags[heur] = True
    set_stats_type(heuristic_flags)
    if heuristic_flags['transitions'] or heuristic_flags['states']:
        general_stats = TraceStats()

    directory = os.path.dirname(os.path.dirname(parser.prog))
    if directory:
        directory += '/'
    files = get_seeds(argv.seeds, directory)
    create_output_dirs()
    init_mut_types()

    seed_number = len(files)
    assert seed_number > 0, 'Seeds not found'

    fuzz(files)


def create_output_dirs():
    """Create directories for storing instances"""

    if not os.path.exists('output'):
        os.mkdir('output')
    for dir in {'output/last_mutants', 'output/reduced',
                'output/ctx', 'output/bugs',
                'output/problems'}:
        if not os.path.exists(dir):
            os.mkdir(dir)
        if dir != 'output':
            for subdir in os.walk('spacer-benchmarks/'):
                dir_path = dir + '/' + subdir[0]
                if not os.path.exists(dir_path):
                    os.mkdir(dir_path)
            for subdir in os.walk('chc-comp21-benchmarks/'):
                dir_path = dir + '/' + subdir[0]
                if not os.path.exists(dir_path):
                    os.mkdir(dir_path)
            for subdir in os.walk('sv-benchmarks-clauses/'):
                dir_path = dir + '/' + subdir[0]
                if not os.path.exists(dir_path):
                    os.mkdir(dir_path)


if __name__ == '__main__':
    main()
