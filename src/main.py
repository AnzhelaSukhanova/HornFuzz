import argparse
import logging
import traceback
from os.path import dirname

from instances import *
from seeds import *

general_stats = None
heuristics = ''
heuristic_flags = defaultdict(bool)
queue = []


def reduce(instance):
    """
    Search for a reduced version of mutation chain that is
    the minimal set of bug-triggering transformations.
    """
    group = instance.get_group()
    initial_size = len(group.instances)
    chunk_size = initial_size // 2
    while chunk_size:
        for i in range(initial_size - 1, 0, -chunk_size):
            from_ind = max(i - chunk_size + 1, 1)
            ind_chunk = range(from_ind, i + 1)
            new_group = undo(instance, ind_chunk)
            new_instance = group[-1]
            try:
                res = check_satis(new_instance)
            except AssertionError as err:
                log_run_info(new_group,
                             'reduce_problem',
                             repr(err),
                             new_instance)
                continue
            if not res:
                group = new_group
        chunk_size //= 2


def undo(instance, ind):
    """Undo the mutation and return the resulting instance."""
    # TODO
    group = instance.get_group
    return group


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


def parse_seeds(argv):
    """Return the parsed seeds given by files in smt2-format."""

    seeds = [
        z3.parse_smt2_file(seed)
        for seed in argv
    ]
    return seeds


def check_satis(instance, snd_instance=None, mut_instance=None, is_seed=False):
    """
    Return True if the test suites have the same satisfiability and
    False otherwise.
    """

    global general_stats
    solver = SolverFor('HORN')
    solver.set('engine', 'spacer')
    group = instance.get_group()

    if is_seed:
        satis = instance.check(solver, is_seed)
        group.satis = satis
        group.same_stats_limit = 5 * len(instance.chc)
    else:
        if snd_instance:
            snd_group = snd_instance.get_group()
            if snd_group.satis == unsat:
                group.satis = unsat

        satis = mut_instance.check(solver, is_seed)
    if heuristic_flags['transitions'] or heuristic_flags['states']:
        general_stats += instance.trace_stats
    return group.satis == satis


def sort_queue():
    """Sort the queue by statistics."""

    global queue
    length = len(heuristics)
    for i in range(length):
        heur = heuristics[i]
        if heur in {'transitions', 'states'}:
            type = StatsType.TRANSITIONS if heur == 'transitions' else StatsType.STATES
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


def log_run_info(group, status, message=None, mut_instance=None, snd_instance=None):
    """Create a log entry with information about the run."""

    cur_instance = group[-1]
    log = {'filename': group.filename, 'status': status}
    if message:
        log['message'] = message
    if not mut_instance:
        cur_instance_info = cur_instance.get_log(is_seed=True)
        log.update(cur_instance_info)
        if status == 'error':
            log['chc'] = cur_instance.chc.sexpr()
            chain = cur_instance.mutation.get_chain()
            log['mut_chain'] = chain
    else:
        snd_id = snd_instance.id if snd_instance else None
        mutant_info = mut_instance.get_log(snd_id)
        log.update(mutant_info)
        if status != 'pass':
            log['prev_chc'] = cur_instance.chc.sexpr()
            if snd_instance:
                log['second_chc'] = snd_instance.chc.sexpr()
            log['current_chc'] = mut_instance.chc.sexpr()
            log['excepted_satis'] = str(group.satis)
            # reduce(mut_instance)
            chain = mut_instance.mutation.get_chain()
            log['mut_chain'] = chain
    logging.info(json.dumps({'run_info': log}))


def analyze_check_exception(err, group, counter,
                            mut_instance=None, is_seed=False):
    """Log information about exceptions that occur during the check"""
    global queue

    if is_seed:
        if str(err) == 'timeout':
            counter['timeout'] += 1
            status = 'seed_timeout'
        else:
            counter['unknown'] += 1
            status = 'seed_unknown'
        log_run_info(group,
                     status,
                     repr(err))
    else:
        snd_instance = mut_instance.mutation.snd_inst
        if str(err) == 'timeout':
            counter['timeout'] += 1
            log_run_info(group,
                         'mutant_timeout',
                         repr(err),
                         mut_instance,
                         snd_instance)
            group.roll_back()
            queue.append(group[0])
        else:
            counter['unknown'] += 1
            log_run_info(group,
                         'mutant_unknown',
                         repr(err),
                         mut_instance,
                         snd_instance)
            group.roll_back()
            queue.append(group[0])


def fuzz(files, seeds):
    global queue, instance_group

    counter = defaultdict(int)
    stats_limit = len(seeds)
    cur_group = None
    for i, seed in enumerate(seeds):
        counter['runs'] += 1
        print_general_info(counter)
        instance_group[i] = InstanceGroup(files.pop())
        cur_group = instance_group[i]
        instance = Instance(i, seed)
        cur_group.push(instance)
        try:
            check_satis(instance, is_seed=True)
        except AssertionError as err:
            analyze_check_exception(err, cur_group, counter, is_seed=True)
            continue
        log_run_info(cur_group,
                     'seed',
                     str(cur_group.satis))
        queue.append(instance)

    while queue:
        print_general_info(counter)
        queue_len = len(queue)
        counter['runs'] += 1
        try:
            if not heuristic_flags['default'] and stats_limit == 0:
                sort_queue()
                stats_limit = random.randint(queue_len // 5, queue_len)
            cur_instance = queue.pop(0)
            stats_limit -= 1
            cur_group = cur_instance.get_group()

            mut_instance = Instance(cur_instance.group_id)
            mut = mut_instance.mutation
            mut_instance.chc = mut.apply(cur_instance)

            try:
                res = check_satis(cur_instance, mut.snd_inst, mut_instance)
            except AssertionError as err:
                analyze_check_exception(err, cur_group, counter, mut_instance)
                continue

            if not res:
                counter['bug'] += 1
                log_run_info(cur_group,
                             'bug',
                             mut_instance=mut_instance,
                             snd_instance=mut.snd_inst)
                queue.append(cur_instance)

            else:
                queue.append(mut_instance)
                cur_group.push(mut_instance)
                if not heuristic_flags['default']:
                    stats_limit = cur_group.check_stats(stats_limit)
                log_run_info(cur_group,
                             'pass',
                             mut_instance=mut_instance,
                             snd_instance=mut.snd_inst)
        except Exception as err:
            if type(err).__name__ == 'TimeoutError':
                counter['timeout'] += 1
                status = 'timeout_before_check'
            else:
                counter['error'] += 1
                status = 'error'
            message = traceback.format_exc()
            log_run_info(cur_group,
                         status,
                         message)
            print(message)

    if not queue:
        print_general_info(counter)


def main():
    global general_stats, heuristics, heuristic_flags

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

    seed_number = len(files)
    logging.info(json.dumps({'seed_number': seed_number, 'heuristics': heuristics}))
    assert seed_number > 0, 'Seeds not found'
    seeds = parse_seeds(files)

    fuzz(files, seeds)


if __name__ == '__main__':
    main()
