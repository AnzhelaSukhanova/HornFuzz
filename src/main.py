import argparse
import logging
import traceback
from os.path import dirname

from mutations import *
from seeds import *

SEED_CHECK_TIME_LIMIT = int(2 * 1e3)
MUT_CHECK_TIME_LIMIT = int(1e5)
INSTANCE_ID = 0

general_stats = None
unique_traces = set()
heuristics = ''
heuristic_flags = defaultdict(bool)
queue = []


class InstanceGroup(object):

    def __init__(self, filename):
        self.filename = filename
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
            self.get_clause_info()

    def roll_back(self):
        """Roll back the group to the seed."""
        seed = self[0]
        self.instances = {0: seed}

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

    def get_clause_info(self):
        """
        Get whether the chc-system is linear, the number of
        uninterpreted predicates and their set.
        """
        assert len(self.instances) > 0, "Instance group is empty"
        instance = self.instances[0]
        info = instance.info
        chc = instance.chc

        self.upred_num, self.uninter_pred = count_expr(chc,
                                                       Z3_OP_UNINTERPRETED,
                                                       is_unique=True)
        info.expr_exists[Z3_OP_AND] = expr_exists(chc, Z3_OP_AND)
        info.expr_exists[Z3_OP_OR] = expr_exists(chc, Z3_OP_OR)
        info.expr_exists[Z3_QUANTIFIER_AST] = \
            expr_exists(chc, Z3_QUANTIFIER_AST)

        for i, clause in enumerate(chc):
            for j in range(3):
                if info.expr_exists[info_kinds[j]]:
                    info.expr_num[j, i] += count_expr(clause, info_kinds[j])

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

    def __init__(self, group_id, chc=None):
        global INSTANCE_ID
        self.id = INSTANCE_ID
        INSTANCE_ID += 1
        self.group_id = group_id
        self.chc = chc
        self.trace_stats = TraceStats()
        self.sort_key = 0
        group = self.get_group()

        if not group.instances:
            chc_len = len(self.chc)
            self.mutation = Mutation(None)
            self.info = ClauseInfo(chc_len)
        else:
            prev_instance = group[-1]
            self.mutation = Mutation(prev_instance.mutation)
            self.info = deepcopy(prev_instance.info)

    def check(self, solver, is_seed):
        """Check the satisfiability of the instance."""
        solver.reset()
        if is_seed:
            solver.set('timeout', SEED_CHECK_TIME_LIMIT)
        else:
            solver.set('timeout', MUT_CHECK_TIME_LIMIT)

        solver.add(self.chc)
        satis = solver.check()
        assert satis != unknown, solver.reason_unknown()
        self.trace_stats.read_from_trace()
        unique_traces.add(self.trace_stats.hash)
        return satis

    def get_group(self):
        """Return the group of the instance."""
        global instance_group
        return instance_group[self.group_id]

    def get_log(self, is_seed=False, snd_id=None):
        """Create a log entry with information about the instance."""
        log = {'id': self.id}
        group = self.get_group()
        if not is_seed:
            log['prev_inst_id'] = group[-1].id
            if snd_id:
                log['snd_inst_id'] = snd_id
            log['mut_type'] = self.mutation.type.name
        return log


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


def log_run_info(group, status, info, mut_instance=None, snd_instance=None):
    """Create a log entry with information about the run."""

    cur_instance = group[-1]
    log = {'filename': group.filename, 'status': status, 'info': info}
    if not mut_instance:
        cur_instance_info = cur_instance.get_log(is_seed=True)
        log.update(cur_instance_info)
    else:
        snd_id = snd_instance.id if snd_instance else None
        mutant_info = mut_instance.get_log(snd_id)
        log.update(mutant_info)
        if status in {'mut_timeout', 'mut_unknown', 'bug', 'reduce_problem'}:
            log['prev_chc'] = cur_instance.chc.sexpr()
            if snd_instance:
                log['second_chc'] = snd_instance.chc.sexpr()
            log['current_chc'] = mut_instance.chc.sexpr()
            log['excepted_satis'] = group.satis
    logging.info(json.dumps({'run_info': log}))


def analyze_check_exception(err, group, counter, mut_instance=None, is_seed=False):
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

            instance_num = random.randrange(1, 3)
            mut_instance = Instance(cur_instance.group_id)
            mut = mut_instance.mutation
            mut.snd_inst = find_inst_for_union(cur_instance) if instance_num == 2 else None
            mut_instance.chc = mut.apply(cur_instance)

            try:
                res = check_satis(cur_instance, mut.snd_inst, mut_instance)
            except AssertionError as err:
                analyze_check_exception(err, cur_group, counter, mut_instance)
                continue

            if not res:
                # mut.reduce(cur_group.instances, mut_instance)
                chain = mut.get_chain()
                counter['bug'] += 1
                info = 'Bug in this chain of mutations: ' + chain
                log_run_info(cur_group,
                             'bug',
                             info,
                             mut_instance,
                             mut.snd_inst)
                queue.append(cur_instance)

            else:
                queue.append(mut_instance)
                cur_group.push(mut_instance)
                if not heuristic_flags['default']:
                    stats_limit = cur_group.check_stats(stats_limit)
                log_run_info(cur_group,
                             'pass',
                             'No bugs found',
                             mut_instance,
                             mut.snd_inst)
        except Exception as err:
            if type(err).__name__ == 'TimeoutError':
                counter['timeout'] += 1
                status = 'timeout_before_check'
            else:
                counter['error'] += 1
                status = 'error'
            log_run_info(cur_group,
                         status,
                         traceback.format_exc())

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
