import argparse
import logging
from os.path import dirname

from mutations import *
from seeds import *

SEED_CHECK_TIME_LIMIT = int(2 * 1e3)
MUT_CHECK_TIME_LIMIT = int(1e5)
INSTANCE_ID = 0

general_stats = None
runs_number = 0
seed_number = 0
unique_traces = set()
unique_seed_traces = set()
heuristics = ''
heuristic_flags = defaultdict(bool)


class InstanceGroup(object):

    def __init__(self, filename, mut):
        self.filename = filename
        self.mutation = mut
        self.satis = unknown
        self.instances = defaultdict(Instance)
        self.same_stats = 0
        self.same_stats_limit = 0
        self.is_linear = True
        self.upred_num = 0
        self.uninter_pred = set()
        self.bound_vars = set()

    def __getitem__(self, item):
        ins = self.instances
        if item < 0:
            item = len(ins) + item
        return ins[item]

    def push(self, instance):
        """Add an instance to the group."""
        length = len(self.instances)
        self.instances[length] = instance
        if length == 0:
            self.get_pred_info()

    def roll_back(self):
        """Roll back the group to the seed."""
        seed = self.instances[0]
        self.instances = {0: seed}
        self.mutation.clear()
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
        if instance.trace_stats == prev_instance.trace_stats:
            self.same_stats += 1
        else:
            self.same_stats = 0
        if self.same_stats >= self.same_stats_limit:
            probability = (self.same_stats_limit - 1) / self.same_stats
            choice = np.random.choice([False, True], 1,
                                      p=[probability, 1 - probability])
            if choice:
                self.roll_back()
                return 0
        return stats_limit

    def get_pred_info(self):
        """
        Get whether the chc-system is linear, the number of
        uninterpreted predicates and their set.
        """
        assert len(self.instances) > 0, "Instance group is empty"
        instance = self.instances[0]
        self.upred_num, self.uninter_pred = count_expr(instance.chc,
                                                       Z3_OP_UNINTERPRETED,
                                                       is_unique=True)
        for clause in instance.chc:
            if self.is_linear:
                child = clause.children()[0]
                if is_quantifier(clause):
                    body = clause.body()
                elif is_not(clause) and child.is_exists():
                    body = child.body()
                else:
                    body = clause
                if is_implies(body):
                    expr = body.children()[0]
                elif is_and(body):
                    expr = body
                elif body.decl().kind() == Z3_OP_UNINTERPRETED:
                    expr = None
                else:
                    assert False, self.filename + \
                                  ' -- clause-kind: ' + \
                                  str(body.decl())
                if expr is not None:
                    upred_num, _ = count_expr(expr,
                                              Z3_OP_UNINTERPRETED,
                                              is_unique=True)
                    if upred_num > 1:
                        self.is_linear = False

    def get_vars(self):
        instance = self[-1]
        for clause in instance.chc:
            for var in get_bound_vars(clause):
                self.bound_vars.add(var)


instance_group = defaultdict(InstanceGroup)


class Instance(object):

    def __init__(self, group_id, chc):
        global INSTANCE_ID
        self.id = INSTANCE_ID
        INSTANCE_ID += 1
        self.group_id = group_id
        self.chc = chc
        if heuristic_flags['transitions'] or heuristic_flags['states']:
            self.trace_stats = TransMatrix()
        self.sort_key = 0
        group = self.get_group()
        group_size = len(group.instances)
        if group_size == 0:
            self.info = ClauseInfo(len(chc))
        else:
            prev_instance = group[group_size - 1]
            self.info = deepcopy(prev_instance.info)

    def check(self, solver, snd_id, is_seed):
        """Check the satisfiability of the instance."""
        global runs_number
        solver.reset()
        runs_number += 1
        if is_seed:
            solver.set('timeout', SEED_CHECK_TIME_LIMIT)
        else:
            solver.set('timeout', MUT_CHECK_TIME_LIMIT)

        solver.add(self.chc)
        satis = solver.check()
        self.log(is_seed, satis, snd_id)
        assert satis != unknown, solver.reason_unknown()
        if heuristic_flags['transitions'] or heuristic_flags['states']:
            self.trace_stats.read_from_trace()
            if is_seed:
                unique_seed_traces.add(self.trace_stats)
            unique_traces.add(self.trace_stats)
        return satis

    def get_group(self):
        """Return the group of the instance."""
        global instance_group
        return instance_group[self.group_id]

    def log(self, is_seed, satis, snd_id):
        """Create a log entry with information about the instance."""
        log = {'id': self.id}
        group = self.get_group()
        if is_seed:
            key = 'seed_info'
        else:
            key = 'mutant_info'
            log['prev_inst_id'] = group[-1].id
            if snd_id:
                log['snd_inst_id'] = snd_id
            log['mut_type'] = group.mutation.cur_type().name
        log['satis'] = str(satis)
        logging.info(json.dumps({key: log}))


def get_weights(stats, heuristic):
    """Return the weights of trace transitions or states."""
    if heuristic == 'transitions':
        prob_matrix = stats.get_probability_matrix()
        weights = get_weight_matrix(prob_matrix)
    else:
        stats.count_states()
        total_states_num = sum(stats.states_num.values())
        weights = {state: total_states_num / stats.states_num[state]
                   for state in stats.states_num}
    return weights


def calc_sort_key(heuristic, stats, weights=None):
    """Calculate the priority of an instance in the sorted queue."""

    if heuristic == 'transitions':
        prob_matrix = stats.get_probability_matrix()
        size = stats.matrix.shape[0]
        weight_matrix_part = weights[:size, :size]
        trans_matrix = stats.matrix
        sort_key = np.sum(prob_matrix * trans_matrix * weight_matrix_part)
    elif heuristic == 'states':
        total_states_num = sum(stats.states_num.values())
        states_prob = {state: stats.states_num[state] / total_states_num
                       for state in stats.states_num}
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


def check_equ(instance, snd_instance, mut_instance):
    """
    Return True if the test suites have the same satisfiability and
    False otherwise.
    """

    global general_stats
    solver = SolverFor('HORN')
    solver.set('engine', 'spacer')
    group = instance.get_group()

    if group.satis == unknown:
        satis = instance.check(solver, None, is_seed=True)
        group.satis = satis
        group.same_stats_limit = 5 * len(instance.chc)
        if heuristic_flags['transitions'] or heuristic_flags['states']:
            general_stats += instance.trace_stats
    if snd_instance:
        snd_group = snd_instance.get_group()
        if snd_group.satis == unsat:
            group.satis = unsat
        snd_id = snd_instance.id
    else:
        snd_id = None

    satis = mut_instance.check(solver, snd_id, is_seed=False)
    if heuristic_flags['transitions'] or heuristic_flags['states']:
        general_stats += instance.trace_stats
    return group.satis == satis


def sort_queue(queue):
    """Sort the queue by statistics."""

    length = len(heuristics)
    for i in range(length):
        heur = heuristics[i]
        if heur == 'transitions' or heur == 'states':
            weights = get_weights(general_stats, heur)
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


def find_inst_for_union(instance):
    """Find an instance that is independent of this instance."""

    fst_group = instance.get_group()
    for key in instance_group:
        snd_group = instance_group[key]
        if not fst_group.uninter_pred.intersection(snd_group.uninter_pred):
            if not fst_group.bound_vars:
                fst_group.get_vars()
            if not snd_group.bound_vars:
                snd_group.get_vars()
            if not fst_group.bound_vars.intersection(snd_group.bound_vars):
                return snd_group[-1]
    return None


def print_runs_info(counter):
    """Print information about runs."""

    global seed_number
    traces_num = len(unique_traces)
    log = {'runs': runs_number, 'time': time.perf_counter()}
    if runs_number:
        print('Total:', runs_number,
              'Timeout:', counter['timeout'],
              'Unknown:', counter['unknown'],
              'Problems:', counter['problem'])
    if traces_num != 0:
        log['unique_traces'] = traces_num
        print('Unique traces:', traces_num, '\n')
    else:
        print()
    if not seed_number:
        log['unique_seed_traces'] = len(unique_seed_traces)
        seed_number -= 1
    logging.info(json.dumps({'general_info': log}))


def add_log_entry(filename, status, message, snd_instance,
                  group=None, mut_instance=None):
    """Create a log entry with information about the run."""

    log = {'filename': filename, 'status': status, 'message': message}
    if status in {'mut_timeout', 'mut_unknown', 'problem', 'reduce_problem'}:
        cur_instance = group[-1]
        log['prev_chc'] = cur_instance.chc.sexpr()
        if snd_instance:
            log['second_chc'] = snd_instance.chc.sexpr()
        log['current_chc'] = mut_instance.chc.sexpr()
    logging.info(json.dumps({'run_info': log}))


def fuzz(files, seeds):
    global runs_number, instance_group, seed_number

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
        mut = group.mutation
        instance_num = random.randrange(1, 3)
        if group.satis == unknown:
            seed_number -= 1
        if instance_num == 2 and group.satis != unknown:
            snd_instance = find_inst_for_union(cur_instance)
        else:
            snd_instance = None
        try:
            mut_chc = mut.apply(cur_instance, snd_instance)
        except (TimeoutError, AssertionError) as err:
            runs_number += 1
            counter['timeout'] += 1
            add_log_entry(group.filename,
                          'timeout_before_check',
                          repr(err),
                          snd_instance)
            continue
        mut_instance = Instance(cur_instance.group_id, mut_chc)

        try:
            res = check_equ(cur_instance, snd_instance, mut_instance)
        except AssertionError as err:
            if group.satis == unknown:
                if str(err) == 'timeout':
                    counter['timeout'] += 1
                    status = 'seed_timeout'
                else:
                    counter['unknown'] += 1
                    status = 'seed_unknown'
                add_log_entry(group.filename,
                              status,
                              repr(err),
                              snd_instance)
            elif str(err) == 'timeout':
                counter['timeout'] += 1
                add_log_entry(group.filename,
                              'mutant_timeout',
                              repr(err),
                              snd_instance,
                              group, mut_instance)
                instance = group.roll_back()
                queue.append(instance)
            else:
                counter['unknown'] += 1
                add_log_entry(group.filename,
                              'mutant_unknown',
                              repr(err),
                              snd_instance,
                              group, mut_instance)
                instance = group.roll_back()
                queue.append(instance)
            continue

        if not res:
            # mut.reduce(group.instances, mut_instance)
            chain = mut.get_chain()
            counter['problem'] += 1
            message = 'Problem in this chain of mutations: ' + chain
            add_log_entry(group.filename,
                          'problem',
                          message,
                          snd_instance,
                          group, mut_instance)
            queue.append(cur_instance)

        else:
            queue.append(mut_instance)
            group.push(mut_instance)
            if heuristic_flags['transitions'] or heuristic_flags['states']:
                stats_limit = group.check_stats(stats_limit)
            add_log_entry(group.filename,
                          'pass',
                          'No problems found',
                          snd_instance)

    if not queue:
        print_runs_info(counter)


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

    heuristics = argv.heuristics
    for heur in heuristics:
        heuristic_flags[heur] = True
    if heuristic_flags['transitions'] or heuristic_flags['states']:
        general_stats = TransMatrix()

    directory = dirname(dirname(parser.prog))
    if directory:
        directory += '/'
    files = get_seeds(argv.seeds, directory)

    seed_number = len(files)
    logging.info(json.dumps({'seed_number': seed_number}))
    assert seed_number > 0, 'Seeds not found'
    seeds = parse_seeds(files)

    fuzz(files, seeds)


if __name__ == '__main__':
    main()
