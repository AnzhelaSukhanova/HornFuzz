import argparse
import logging
from os.path import dirname
from copy import deepcopy

from mutations import *
from seeds import get_seeds

SEED_CHECK_TIME_LIMIT = int(2 * 1e3)
MUT_CHECK_TIME_LIMIT = int(1e5)
INSTANCE_ID = 0

general_stats = None
runs_number = 0
unique_traces = set()
heuristic = ''


class InstanceGroup(object):

    def __init__(self, filename, mut):
        self.filename = filename
        self.mutation = mut
        self.satis = unknown
        self.instances = defaultdict(Instance)
        self.same_stats = 0
        self.same_stats_limit = 0
        self.is_linear = True
        self.uninter_pred = set()

    def push(self, instance):
        """Add an instance to the group."""
        length = len(self.instances)
        self.instances[length] = instance
        if length == 0 and heuristic == 'difficulty':
            self.get_pred_info()

    def roll_back(self):
        """Roll back the group to the seed."""
        seed = self.instances[0]
        self.instances = {seed}
        self.mutation.type_seq.clear()
        return seed

    def check_stats(self, stats_limit):
        """
        Increase the counter if the current trace is the same as the previous
        one. Reset the number of steps before sorting instances if their
        traces repeat long enough.
        """
        assert len(self.instances) >= 2, 'Not enough instances to compare'
        i = len(self.instances) - 1
        instance = self.instances[i]
        prev_instance = self.instances[i - 1]
        if instance.trace_stats.data == prev_instance.trace_stats.data:
            self.same_stats += 1
        else:
            self.same_stats = 0
        if self.same_stats >= self.same_stats_limit:
            self.roll_back()
            return 0
        return stats_limit

    def get_pred_info(self):
        """
        Get whether the chc-system is linear and the number of
        uninterpreted predicates.
        """
        assert len(self.instances) > 0, "Instance group is empty"
        instance = self.instances[0]
        for expr in instance.chc:
            expr_set = {expr}
            while len(expr_set):
                cur_expr = expr_set.pop()
                if not is_var(expr) and not is_const(expr):
                    if is_app(cur_expr):
                        func = cur_expr.decl()
                        if func.kind() == Z3_OP_UNINTERPRETED:
                            self.uninter_pred.add(func)
                        elif self.is_linear and \
                                not is_var(cur_expr) and \
                                not is_const(cur_expr):
                            body = cur_expr.children()[0]
                            if is_implies(cur_expr) or \
                                    (is_not(cur_expr) and is_and(body)):
                                upred_num = count_expr(body,
                                                       Z3_OP_UNINTERPRETED,
                                                       True)
                                if upred_num > 1:
                                    self.is_linear = False
                    for child in cur_expr.children():
                        expr_set.add(child)


instance_group = defaultdict(InstanceGroup)


class Instance(object):

    def __init__(self, group_id, chc):
        global INSTANCE_ID
        self.id = INSTANCE_ID
        INSTANCE_ID += 1
        self.group_id = group_id
        self.chc = chc
        self.time = time
        if heuristic == 'transitions' or heuristic == 'states':
            self.trace_stats = TraceStats()
        self.sort_key = 0
        group = self.get_group()
        group_size = len(group.instances)
        if group_size == 0:
            self.info = ClauseInfo(len(chc))
        else:
            prev_instance = group.instances[group_size - 1]
            self.info = deepcopy(prev_instance.info)

    def check(self, solver, is_seed):
        global runs_number
        solver.reset()
        runs_number += 1
        if is_seed:
            solver.set('timeout', SEED_CHECK_TIME_LIMIT)
        else:
            solver.set('timeout', MUT_CHECK_TIME_LIMIT)

        st_time = time.perf_counter()
        solver.add(self.chc)
        satis = solver.check()
        self.time = time.perf_counter() - st_time
        assert satis != unknown, solver.reason_unknown()
        if heuristic == 'transitions' or heuristic == 'states':
            self.trace_stats.get()
        return satis

    def get_group(self):
        """Return the group of the instance."""
        global instance_group
        return instance_group[self.group_id]


class TraceStats(object):

    def __init__(self):
        if heuristic == 'transitions':
            self.data = TransMatrix()
        else:
            self.data = defaultdict(int)

    def __add__(self, other):
        sum = deepcopy(self)
        if heuristic == 'states':
            for state in other.data:
                sum.data[state] += other.data[state]
        else:
            sum.data += other.data
        return sum

    def get(self):
        """Get z3-trace stats from .z3-trace."""
        global unique_traces
        if heuristic == 'transitions':
            self.data.read_from_trace()
            unique_traces.add(self.data)
        else:
            count_states(self.data)
            unique_traces.add(repr(self.data))

    def get_weights(self):
        """Return the weights of trace transitions or states."""
        if heuristic == 'transitions':
            prob_matrix = self.data.get_probability_matrix()
            weights = get_weight_matrix(prob_matrix)
        else:
            total_states_num = sum(self.data.values())
            weights = {state: total_states_num / self.data[state]
                       for state in self.data}
        return weights


def calc_sort_key(stats, weights=None):
    if heuristic == 'transitions':
        prob_matrix = stats.data.get_probability_matrix()
        size = stats.data.matrix.shape[0]
        weight_matrix_part = weights[:size, :size]
        trans_matrix = stats.data.matrix
        sort_key = np.sum(prob_matrix * trans_matrix * weight_matrix_part)
    elif heuristic == 'states':
        total_states_num = sum(stats.data.values())
        states_prob = {state: stats.data[state] / total_states_num
                       for state in stats.data}
        sort_key = sum(states_prob[state] * weights[state]
                       for state in stats.data)
    elif heuristic == 'difficulty':
        is_nonlinear = not stats[0]
        upred_num = len(stats[1])
        sort_key = (is_nonlinear, upred_num)
    else:
        expr_num = stats.expr_num
        sum = expr_num.sum()
        if heuristic == 'many-targets':
            sort_key = sum
        else:
            sort_key = 1 / sum
    return sort_key


def parse_seeds(argv):
    """Return the parsed seeds given by files in smt2-format."""

    seeds = [
        z3.parse_smt2_file(seed)
        for seed in argv
    ]
    return seeds


def check_equ(instance, mut_instance):
    """
    Return True if the test suites have the same satisfiability and
    False otherwise.
    """

    global general_stats
    solver = SolverFor('HORN')
    solver.set('engine', 'spacer')
    group = instance.get_group()

    mut = group.mutation
    if mut.number == 1:
        satis = instance.check(solver, is_seed=True)
        group.satis = satis
        group.same_stats_limit = 5*len(instance.chc)
        if heuristic == 'transitions' or heuristic == 'states':
            general_stats += instance.trace_stats
        logging.info('%s -- %s: %s, %s %s',
                     instance.id, 'Seed',
                     satis,
                     'time(sec):', instance.time)

    satis = mut_instance.check(solver, is_seed=False)
    if heuristic == 'transitions' or heuristic == 'states':
        general_stats += instance.trace_stats
    logging.info('%s -- %s %s (%s): %s, %s %s',
                 mut_instance.id, 'Mutant of', instance.id,
                 str(mut.cur_type().name), satis,
                 'time(sec):', mut_instance.time)
    return group.satis == satis


def sort_queue(queue):
    """Sort the queue by statistics."""

    if heuristic == 'transitions' or heuristic == 'states':
        weights = general_stats.get_weights()
    for instance in queue:
        if heuristic == 'transitions' or heuristic == 'states':
            ins_stats = instance.trace_stats
            instance.sort_key = calc_sort_key(ins_stats, weights)
        elif heuristic == 'many-targets' or heuristic == 'few-targets':
            instance.sort_key = calc_sort_key(instance.info)
        else:
            group = instance.get_group()
            instance.sort_key = calc_sort_key((group.is_linear,
                                               group.uninter_pred))
    queue.sort(key=lambda item: item.sort_key, reverse=True)


def print_runs_info(counter):
    """Print information about runs."""

    traces_num = len(unique_traces)
    if runs_number:
        print('Total:', runs_number,
              'Timeout:', counter['timeout'],
              'Unknown:', counter['unknown'],
              'Problems:', counter['problem'])
    if traces_num != 0:
        print('Unique traces:', traces_num, '\n')
    else:
        print()


def fuzz(files, seeds):
    global runs_number, instance_group

    queue = []
    counter = defaultdict(int)
    for i, seed in enumerate(seeds):
        instance_group[i] = InstanceGroup(files.pop(), Mutation())
        instance = Instance(i, seed)
        instance_group[i].push(instance)
        queue.append(instance)
    seed_len = len(seeds)
    stats_limit = seed_len

    while queue:
        print_runs_info(counter)
        if stats_limit == 0:
            sort_queue(queue)
            stats_limit = random.randint(seed_len // 5, seed_len)
        cur_instance = queue.pop(0)
        stats_limit -= 1
        group = cur_instance.get_group()
        logging.info(group.filename)
        mut = group.mutation
        try:
            mut_chc = mut.apply(cur_instance)
        except (TimeoutError, AssertionError) as err:
            runs_number += 1
            counter['timeout'] += 1
            logging.info('%s\n', repr(err))
            continue
        mut_instance = Instance(cur_instance.group_id, mut_chc)

        try:
            res = check_equ(cur_instance, mut_instance)
        except AssertionError as err:
            if group.satis == unknown:
                if str(err) == 'timeout':
                    counter['timeout'] += 1
                else:
                    counter['unknown'] += 1
                logging.info('%s\n', repr(err))
            elif str(err) == 'timeout':
                counter['timeout'] += 1
                logging.info(repr(err))
                seed = group.instances[0]
                logging.info('%s %s\n%s %s\n',
                             'Seed\'s time(sec):',
                             seed.time,
                             'Mutant\'s time(sec):',
                             mut_instance.time)
                instance = group.roll_back()
                queue.append(instance)
            else:
                counter['unknown'] += 1
                logging.error('%s -- %s\n',
                              'Problem',
                              repr(err))
                instance = group.roll_back()
                queue.append(instance)
            continue

        if not res:
            chain = mut.get_chain()
            counter['problem'] += 1
            logging.error('%s\n%s',
                          'Problem in this chain of mutations:',
                          chain)
            logging.error('%s\n->\n%s\n',
                          cur_instance.chc,
                          mut_instance.chc)
            queue.append(cur_instance)

        else:
            queue.append(mut_instance)
            group.push(mut_instance)
            if heuristic == 'transitions' or heuristic == 'states':
                stats_limit = group.check_stats(stats_limit)
            logging.info('No problems found\n')

    if not queue:
        print_runs_info(counter)


def main():
    global general_stats, heuristic

    parser = argparse.ArgumentParser()
    parser.add_argument('seeds',
                        nargs='*',
                        default='',
                        help='directory with seeds or keyword \'all\'')
    parser.add_argument('-heuristic', '-heur',
                        nargs='*',
                        choices=['transitions', 'states',
                                 'many-targets', 'few-targets',
                                 'difficulty'],
                        default=['transitions'],
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
    # enable_trace('smt_search')
    heuristic = argv.heuristic[0]
    if heuristic == 'transitions' or heuristic == 'states':
        general_stats = TraceStats()

    directory = dirname(dirname(parser.prog))
    if directory:
        directory += '/'
    files = get_seeds(argv.seeds, directory)

    seed_num = len(files)
    assert seed_num > 0, 'Seeds not found'
    seeds = parse_seeds(files)

    fuzz(files, seeds)


if __name__ == '__main__':
    main()
