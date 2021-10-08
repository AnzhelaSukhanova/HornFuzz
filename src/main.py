import argparse
import logging
import traceback
from os.path import dirname

from instances import *
from seeds import *

general_stats = None
seed_number = 0
heuristics = ''
heuristic_flags = defaultdict(bool)
queue = []

ONE_INST_MUT_LIMIT = 1000
MUT_AFTER_PROBLEM = 10


def calc_sort_key(heuristic, stats, weights=None):
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
        expr_num = stats.expr_num
        sum_num = expr_num.sum()
        if heuristic == 'many-targets':
            sort_key = sum_num
        else:
            sort_key = 1 / sum_num
    return sort_key


def check_satis(instance, is_seed=False, get_stats=True):
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
                elif heur == 'many-targets' or heur == 'few-targets':
                    instance.sort_key = calc_sort_key(heur,
                                                      instance.info)
                else:
                    group = instance.get_group()
                    instance.sort_key = calc_sort_key(heur,
                                                      (group.is_linear,
                                                       group.upred_num))
            chunk.sort(key=lambda item: item.sort_key, reverse=True)
            queue += chunk


def print_general_info(counter):
    """Print and log information about runs."""

    traces_num = len(unique_traces)
    log = {'runs': counter['runs'], 'time': time.perf_counter()}
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
    logging.info(json.dumps({'general_info': log}))


def log_run_info(status, message=None, instance=None, mut_instance=None):
    """Create a log entry with information about the run."""

    log = {'status': status}
    if message:
        log['message'] = message
    if instance:
        if not mut_instance:
            instance_info = instance.get_log(is_mutant=False)
            log.update(instance_info)
            if status == 'error':
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
                log['prev_chc'] = instance.chc.sexpr()
                log['excepted_satis'] = str(instance.satis)

    logging.info(json.dumps({'run_info': log}))


def analyze_check_exception(instance, err, counter,
                            mut_instance=None, is_seed=False):
    """Log information about exceptions that occur during the check."""
    global queue
    group = instance.get_group()

    if is_seed:
        if str(err) == 'timeout':
            counter['timeout'] += 1
            status = 'seed_timeout'
        else:
            counter['unknown'] += 1
            status = 'seed_unknown'
        log_run_info(status,
                     repr(err),
                     instance)
    else:
        if str(err) == 'timeout':
            counter['timeout'] += 1
            log_run_info('mutant_timeout',
                         repr(err),
                         instance,
                         mut_instance)
            group.roll_back()
            queue.append(group[0])
        else:
            counter['unknown'] += 1
            log_run_info('mutant_unknown',
                         repr(err),
                         instance,
                         mut_instance)
            group.roll_back()
            queue.append(group[0])


def run_seeds(files, counter):
    global queue, seed_number

    for i, filename in enumerate(files):
        seed = z3.parse_smt2_file(filename)
        if not seed:
            seed_number -= 1
            continue
        if i > 0:
            print_general_info(counter)
        counter['runs'] += 1
        group = InstanceGroup(i, filename)
        instance = Instance(i, seed)
        group.same_stats_limit = 5 * len(seed)
        group.push(instance)

        try:
            check_satis(instance, is_seed=True)
        except AssertionError as err:
            analyze_check_exception(instance, err, counter, is_seed=True)
            continue
        log_run_info('seed',
                     instance=instance)
        queue.append(instance)
    assert seed_number > 0, 'All seeds were given in incorrect format'


def fuzz(files):
    global queue

    counter = defaultdict(int)
    run_seeds(files, counter)
    stats_limit = seed_number

    while queue:
        instance = None
        try:
            if not heuristic_flags['default'] and not stats_limit:
                sort_queue()
                queue_len = len(queue)
                stats_limit = random.randint(queue_len // 5, queue_len)
            instance = queue.pop(0)
            group = instance.get_group()

            if counter['runs'] >= 2*seed_number:
                start_mut_ind = len(group.instances)
                instance.restore()
                mut_limit = ONE_INST_MUT_LIMIT
            else:
                start_mut_ind = 0
                mut_limit = 1
            stats_limit -= 1

            i = 0
            while i < mut_limit:
                i += 1
                counter['runs'] += 1
                print_general_info(counter)

                mut_instance = Instance(instance.group_id)
                mut = mut_instance.mutation
                mut.apply(instance, mut_instance)

                try:
                    res = check_satis(mut_instance)
                except AssertionError as err:
                    analyze_check_exception(instance, err, counter, mut_instance)
                    filename = group.filename[:-4] + '_' + \
                               str(mut_instance.id) + '.smt2'
                    mut_instance.dump('output/problems',
                                      filename,
                                      0,
                                      repr(err))
                    i = max(i, mut_limit - MUT_AFTER_PROBLEM)
                    continue

                if not res:
                    counter['bug'] += 1
                    log_run_info('bug',
                                 instance=instance,
                                 mut_instance=mut_instance)
                    queue.append(instance)
                    filename = group.filename[:-4] + '_' + \
                               str(mut_instance.id) + '.smt2'
                    mut_instance.dump('output/bugs',
                                      filename,
                                      0)
                    i = max(i, mut_limit - MUT_AFTER_PROBLEM)
                    continue

                else:
                    queue.append(mut_instance)
                    group.push(mut_instance)
                    if not heuristic_flags['default'] and \
                            len(instance_groups) > 1:
                        stats_limit = group.check_stats(stats_limit)
                    log_run_info('pass',
                                 instance=instance,
                                 mut_instance=mut_instance)
                    instance = mut_instance

            instance.dump('output/last_mutants',
                          group.filename,
                          start_mut_ind)

        except Exception as err:
            if type(err).__name__ == 'TimeoutError':
                counter['timeout'] += 1
                status = 'timeout_before_check'
            else:
                counter['error'] += 1
                status = 'error'
            message = traceback.format_exc()
            log_run_info(status,
                         message,
                         instance)
            print(message)

    if not queue:
        print_general_info(counter)


def main():
    global general_stats, heuristics, heuristic_flags, seed_number

    parser = argparse.ArgumentParser()
    parser.add_argument('seeds',
                        nargs='*',
                        default='',
                        help='directory with seeds or keyword \'all\'')
    parser.add_argument('-heuristics', '-heur',
                        nargs='*',
                        choices=['transitions', 'states',
                                 'many-targets', 'few-targets',
                                 'difficulty'],
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

    directory = dirname(dirname(parser.prog))
    if directory:
        directory += '/'
    files = get_seeds(argv.seeds, directory)
    create_output_dirs()

    seed_number = len(files)
    assert seed_number > 0, 'Seeds not found'
    logging.info(json.dumps({'seed_number': seed_number, 'heuristics': heuristics}))

    fuzz(files)


def create_output_dirs():
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


if __name__ == '__main__':
    main()
