import argparse
import logging
from os.path import dirname

from mutations import *
from seeds import get_seeds

SEED_CHECK_TIME_LIMIT = int(2 * 1e3)
MUT_CHECK_TIME_LIMIT = int(1e5)
INSTANCE_ID = 0

stats = TransMatrix()
states_num = defaultdict(int)
runs_number = 0
priority = ''


class InstanceGroup(object):

    def __init__(self, filename, mut):
        self.filename = filename
        self.mutation = mut
        self.satis = unknown
        self.instances = defaultdict(Instance)

    def push(self, instance):
        length = len(self.instances)
        self.instances[length] = instance

    def roll_back(self):
        seed = self.instances[0]
        group.instances = {seed}
        return seed


instance_group = defaultdict(InstanceGroup)


class Instance(object):

    def __init__(self, group_id, chc):
        global INSTANCE_ID
        self.id = INSTANCE_ID
        INSTANCE_ID += 1
        self.group_id = group_id
        self.chc = chc
        self.time = time
        if priority == 'transitions':
            self.trans_matrix = TransMatrix()
        else:
            self.states_num = defaultdict(int)
        self.sort_key = 0

    def check(self, solver, is_seed):
        global runs_number, priority
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
        if priority == 'transitions':
            self.trans_matrix.read_from_trace()
        else:
            count_states(self.states_num)
        return satis

    def calc_sort_key(self, weights):
        if priority == 'transitions':
            prob_matrix = self.trans_matrix.get_probability_matrix()
            size = self.trans_matrix.matrix.shape[0]
            weight_matrix_part = weights[:size, :size]
            trans_matrix = self.trans_matrix.matrix
            self.sort_key = np.sum(prob_matrix * trans_matrix * weight_matrix_part)
        else:
            total_states_num = sum(self.states_num.values())
            states_prob = {state: self.states_num[state] / total_states_num 
                           for state in self.states_num}
            self.sort_key = sum(states_prob[state] * weights[state] for state in self.states_num)

    def get_group(self):
        global instance_group
        return instance_group[self.group_id]


def parse_seeds(argv):
    """Return the parsed seeds given by files in smt2-format"""

    seeds = [
        z3.parse_smt2_file(seed)
        for seed in argv
    ]
    return seeds


def check_equ(instance, mut_instance):
    """Return True if the test suites have the same satisfiability and False otherwise"""
    solver = SolverFor('HORN')
    solver.set('engine', 'spacer')
    group = instance.get_group()

    mut = group.mutation
    if mut.number == 1:
        satis = instance.check(solver, is_seed=True)
        group.satis = satis
        update_stats(instance)
        logging.info('%s -- %s: %s, %s %s',
                     instance.id, 'Seed',
                     satis,
                     'time(sec):', instance.time)

    satis = mut_instance.check(solver, is_seed=False)
    update_stats(mut_instance)
    logging.info('%s -- %s %s (%s): %s, %s %s',
                 mut_instance.id, 'Mutant of', instance.id, str(mut.cur_type().name),
                 satis,
                 'time(sec):', mut_instance.time)
    return group.satis == satis


def update_stats(instance):
    global priority, stats, states_num
    if priority == 'transitions':
        stats += instance.trans_matrix
    else:
        for state in instance.states_num:
            states_num[state] += instance.states_num[state]


def sort_queue(queue):
    """Sort the queue by rare transitions"""

    if priority == 'transitions':
        global stats
        prob_matrix = stats.get_probability_matrix()
        weights = get_weight_matrix(prob_matrix)

    else:
        global states_num
        total_states_num = sum(states_num.values())
        weights = {state: total_states_num / states_num[state] for state in states_num}

    for instance in queue:
        instance.calc_sort_key(weights)
    queue.sort(key=lambda item: item.sort_key, reverse=True)


def print_runs_info(counter):
    """Print information about runs"""

    global runs_number
    if runs_number:
        print('Total:', runs_number,
              'Timeout:', counter['timeout'],
              'Unknown:', counter['unknown'],
              'Problems:', counter['problem'], '\n')


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
            mut_chc = mut.apply(cur_instance.chc)
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
            logging.info('No problems found\n')

    if not queue:
        print_runs_info(counter)


def main():
    global priority

    parser = argparse.ArgumentParser()
    parser.add_argument('seeds',
                        nargs='*',
                        default='',
                        help='directory with seeds or keyword \'all\'')
    parser.add_argument('-priority',
                        nargs='*',
                        choices=['transitions', 'states'],
                        default='transitions',
                        help='trace data which will be used to select an instance for mutation')
    argv = parser.parse_args()

    # help_simplify()
    logging.basicConfig(format='%(message)s', filename='logfile', level=logging.INFO)
    np.set_printoptions(suppress=True)
    set_option(max_args=int(1e6), max_lines=int(1e6), max_depth=int(1e6), max_visited=int(1e6))
    enable_trace('spacer')
    # enable_trace('smt_search')
    priority = argv.priority

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
