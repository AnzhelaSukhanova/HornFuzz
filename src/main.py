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


def is_same_res(instance, result=False, message=None):
    try:
        same_res = result == check_satis(instance, get_stats=False)
        if message:
            same_res = False
    except AssertionError as err:
        same_res = repr(err) == message
    return same_res


def reduce_instance(instance, mutation, message=None):
    group = instance.get_group()
    new_instance = deepcopy(instance)
    new_instance.mutation = mutation
    last_chc = instance.chc
    reduced_ind = set()
    upred_ind = group.upred_ind

    for pred in upred_ind:
        ind = group.upred_ind[pred].intersection(reduced_ind)
        new_instance.chc = remove_clauses(new_instance.chc, ind)

        mut_instance = deepcopy(new_instance)
        mut = new_instance.mutation
        if mut.path[0]:
            for i in ind:
                if mut.path[0] == i:
                    continue
                elif mut.path[0] > i:
                    mut.path[0] -= 1
        new_instance.get_system_info()

        mut.apply(new_instance, mut_instance)

        if not is_same_res(mut_instance):
            new_instance.chc = last_chc
        else:
            last_chc = new_instance.chc
            reduced_ind = reduced_ind.union(group.upred_ind[pred])
    old_len = len(instance.chc)
    new_len = len(new_instance.chc)
    if old_len != new_len:
        print('Reduced:',
              old_len, '->', new_len,
              '(number of clauses)')
        new_instance.chc = reduce_instance(new_instance, mutation, message)
    return new_instance.chc


def reduce(instance, message=None):
    """
    Search for a reduced version of mutation chain that is
    the minimal set of bug-triggering transformations.
    """
    group = instance.get_group()
    group.push(instance)
    initial_size = len(group.instances)
    chunk_size = initial_size // 2

    while chunk_size:
        for i in range(initial_size - 1, 0, -chunk_size):
            from_ind = max(i - chunk_size + 1, 1)
            ind_chunk = range(from_ind, i + 1)
            new_group = undo_mutations(instance, ind_chunk)
            new_instance = new_group[-1]
            if group != new_group and \
                    is_same_res(new_instance, message=message):
                group = new_group

            if chunk_size == 1:
                if group[ind_chunk[0]].mutation.type == MutType.SIMPLIFY:
                    group[ind_chunk[0]] = reduce_simplify(group[ind_chunk[0] - 1], message)
        chunk_size //= 2

    instance = group[-1]
    group.pop()
    return instance


def undo_mutations(instance, ind):
    """Undo the mutations from a given interval."""
    cur_group = instance.get_group()
    new_group = deepcopy(cur_group)
    new_group.instances.clear()
    for i in range(ind[0]):
        new_group.push(cur_group[i])
    last_instance = new_group[ind[0] - 1]
    for i in range(ind[-1] + 1, len(cur_group.instances)):
        mut_instance = Instance(last_instance.group_id)
        mut_instance.mutation = cur_group[i].mutation
        mut = mut_instance.mutation
        info = last_instance.info
        if mut.trans_num is not None:
            clause_ind = mut.path[0]
            expr_num = info.expr_num[mut.kind_ind][clause_ind]
            if mut.trans_num >= expr_num:
                return cur_group
        mut.apply(last_instance, mut_instance)
        new_group.push(mut_instance)
        last_instance = mut_instance

    return new_group


def reduce_simplify(instance, message=None):
    mut_instance = Instance(instance.group_id)
    mut = mut_instance.mutation
    mut.type = MutType.SIMPLIFY
    flags_num = len(mut.simp_flags)

    for i in range(flags_num):
        mut.simp_flags[i] = False
        mut.apply(instance, mut_instance)
        if not is_same_res(mut_instance, message=message):
            mut.simp_flags[i] = True
        mut_instance.chc = instance.chc

    mut.path[0] = [i for i in range(len(instance.chc))]
    for i in range(len(instance.chc)):
        mut.path[0].remove(i)
        mut.apply(instance, mut_instance)
        if not is_same_res(mut_instance, message=message):
            mut.path[0].append(i)
        mut_instance.chc = instance.chc
    if mut.path[0] == range(len(instance.chc)):
        mut.path[0] = None

    mut.apply(instance, mut_instance)
    return mut_instance


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


def parse_seeds(filenames):
    """Return the parsed seeds given by files in smt2-format."""

    global seed_number
    seeds = []
    for name in filenames:
        seed = z3.parse_smt2_file(name)
        if seed:
            seeds.append(seed)
        else:
            seed_number -= 1
    return seeds


def check_satis(instance, is_seed=False, get_stats=True):
    """
    Return True if the test suites have the same satisfiability and
    False otherwise.
    """

    global general_stats
    solver = SolverFor('HORN')
    solver.set('engine', 'spacer')

    instance.check(solver, is_seed, get_stats)
    if not is_seed:
        group = instance.get_group()
        satis = group[-1].satis
    else:
        satis = instance.satis

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


def log_run_info(status, message=None, cur_instance=None, mut_instance=None):
    """Create a log entry with information about the run."""

    log = {'status': status}
    if message:
        log['message'] = message
    if cur_instance:
        if not mut_instance:
            cur_instance_info = cur_instance.get_log(is_seed=True)
            log.update(cur_instance_info)
            if status == 'error':
                log['chc'] = cur_instance.chc.sexpr()
                chain = cur_instance.mutation.get_chain()
                log['mut_chain'] = chain
            elif status == 'seed':
                log['satis'] = str(cur_instance.satis)

        else:
            if status in {'mutant_unknown', 'bug'}:
                mut_instance = reduce(mut_instance, message)
            mutant_info = mut_instance.get_log()
            log.update(mutant_info)

            if status != 'pass':
                if status in {'mutant_unknown', 'bug'}:
                    try:
                        reduced_inst = reduce_instance(cur_instance,
                                                       mut_instance.mutation,
                                                       message)
                        filename = 'reduced/' + str(mut_instance.group_id) + '_' + \
                                   str(mut_instance.id) + '.smt2'
                        with open(filename, 'w') as file:
                            file.write(reduced_inst.sexpr())
                    except Exception:
                        print(traceback.format_exc())
                        reduced_inst = cur_instance.chc
                    log['prev_chc'] = reduced_inst.sexpr()
                else:
                    log['prev_chc'] = cur_instance.chc.sexpr()

                log['current_chc'] = mut_instance.chc.sexpr()
                log['excepted_satis'] = str(cur_instance.satis)
                chain = mut_instance.mutation.get_chain()
                log['mut_chain'] = chain

    logging.info(json.dumps({'run_info': log}))


def analyze_check_exception(cur_instance, err, counter,
                            mut_instance=None, is_seed=False):
    """Log information about exceptions that occur during the check."""
    global queue
    group = cur_instance.get_group()

    if is_seed:
        if str(err) == 'timeout':
            counter['timeout'] += 1
            status = 'seed_timeout'
        else:
            counter['unknown'] += 1
            status = 'seed_unknown'
        log_run_info(status,
                     repr(err),
                     cur_instance)
    else:
        if str(err) == 'timeout':
            counter['timeout'] += 1
            log_run_info('mutant_timeout',
                         repr(err),
                         cur_instance,
                         mut_instance)
            group.roll_back()
            queue.append(group[0])
        else:
            counter['unknown'] += 1
            log_run_info('mutant_unknown',
                         repr(err),
                         cur_instance,
                         mut_instance)
            group.roll_back()
            queue.append(group[0])


def fuzz(files, seeds):
    global queue, instance_group

    counter = defaultdict(int)
    stats_limit = len(seeds)
    for i, seed in enumerate(seeds):
        if i > 0:
            print_general_info(counter)
        counter['runs'] += 1
        instance_group[i] = InstanceGroup(files.pop())
        cur_group = instance_group[i]
        cur_instance = Instance(i, seed)
        cur_group.same_stats_limit = 5 * len(seed)
        cur_group.push(cur_instance)
        try:
            check_satis(cur_instance, is_seed=True)
        except AssertionError as err:
            analyze_check_exception(cur_instance, err, counter, is_seed=True)
            continue
        log_run_info('seed',
                     cur_instance=cur_instance)
        queue.append(cur_instance)

    while queue:
        print_general_info(counter)
        queue_len = len(queue)
        counter['runs'] += 1
        cur_instance = None
        try:
            if not heuristic_flags['default'] and stats_limit == 0:
                sort_queue()
                stats_limit = random.randint(queue_len // 5, queue_len)
            cur_instance = queue.pop(0)
            stats_limit -= 1
            cur_group = cur_instance.get_group()

            mut_instance = Instance(cur_instance.group_id)
            mut = mut_instance.mutation
            mut.apply(cur_instance, mut_instance)

            try:
                res = check_satis(mut_instance)
            except AssertionError as err:
                analyze_check_exception(cur_instance, err, counter, mut_instance)
                continue

            if not res:
                counter['bug'] += 1
                log_run_info('bug',
                             cur_instance=cur_instance,
                             mut_instance=mut_instance)
                queue.append(cur_instance)

            else:
                queue.append(mut_instance)
                cur_group.push(mut_instance)
                if not heuristic_flags['default'] and \
                        len(instance_group) > 1:
                    stats_limit = cur_group.check_stats(stats_limit)
                log_run_info('pass',
                             cur_instance=cur_instance,
                             mut_instance=mut_instance)

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
                         cur_instance)
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
    if not os.path.exists('reduced'):
        os.mkdir('reduced')
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
    assert seed_number > 0, 'Seeds not found'
    seeds = parse_seeds(files)
    assert seed_number > 0, 'All seeds were given in incorrect format'
    logging.info(json.dumps({'seed_number': seed_number, 'heuristics': heuristics}))

    fuzz(files, seeds)


if __name__ == '__main__':
    main()
