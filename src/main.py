import argparse
import logging
import time
from copy import deepcopy
from os.path import dirname

from mutations import *
from seeds import get_seeds

SEED_TIME_LIMIT = int(2 * 1e3)
MUT_TIME_LIMIT = int(1e5)
INSTANCE_ID = 0
PRIORITY_LIMIT = 10

stats = TransMatrix()
runs_number = 0
priority = ''


class Instance(object):

    def __init__(self, filename, chc, mut, time):
        global INSTANCE_ID
        self.id = INSTANCE_ID
        INSTANCE_ID += 1
        self.filename = filename
        self.chc = chc
        self.satis = unknown
        self.mutation = mut
        self.time = time
        self.repeat_limit = 5 * len(self.chc)
        if priority == 'transitions':
            self.trans_matrix = TransMatrix()
        else:
            self.states_num = defaultdict(int)
        self.sort_key = 0

    def check(self, solver, is_seed):
        global runs_number, priority
        runs_number += 1
        if is_seed:
            solver.set('timeout', SEED_TIME_LIMIT)
        else:
            solver.set('timeout', MUT_TIME_LIMIT)

        st_time = time.perf_counter()
        solver.add(self.chc)
        self.satis = solver.check()
        solver.reset()
        self.time.append(time.perf_counter() - st_time)
        assert self.satis != unknown, solver.reason_unknown()
        if priority == 'transitions':
            self.trans_matrix.read_from_trace()
        else:
            count_states(self.states_num)

    def calc_sort_key(self, weights):
        if priority == 'transitions':
            prob_matrix = self.trans_matrix.get_probability_matrix()
            size = self.trans_matrix.size
            weight_matrix_part = weights[:size, :size]
            trans_matrix = self.trans_matrix.trans_matrix
            self.sort_key = np.sum(prob_matrix * trans_matrix * weight_matrix_part)
        else:
            total_states_num = sum(self.states_num.values())
            states_prob = {state: self.states_num[state] / total_states_num 
                           for state in self.states_num}
            self.sort_key = sum(states_prob[state] * weights[state] for state in self.states_num)


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

    mut = instance.mutation
    if mut.number == 1:
        instance.check(solver, is_seed=True)
        logging.info("%s -- %s: %s, %s %s",
                     instance.id, 'Seed',
                     str(instance.satis),
                     'time(sec):', instance.time[0])

    mut_instance.check(solver, is_seed=False)
    logging.info("%s -- %s %s (%s): %s, %s %s",
                 mut_instance.id, 'Mutant of', instance.id, str(mut.cur_type().name),
                 str(mut_instance.satis),
                 'time(sec):', mut_instance.time[-1])
    return instance.satis == mut_instance.satis


def get_instance(queue, repeat_counter, prev_name):
    """Return an instance from the queue"""

    queue_len = len(queue)
    if queue_len == 0:
        return None
    i = 0
    cur_instance = queue[i]
    if repeat_counter >= cur_instance.repeat_limit:
        while prev_name == cur_instance.filename:
            i += 1
            if i == queue_len:
                cur_instance = None
                break
            cur_instance = queue[i]
    cur_instance = queue.pop(i) if cur_instance is not None else None
    return cur_instance


def sort_queue(queue):
    """Sort the queue by rare transitions"""

    if priority == 'transitions':
        global stats
        for instance in queue:
            stats += instance.trans_matrix
        prob_matrix = stats.get_probability_matrix()
        weights = get_weight_matrix(prob_matrix)

    else:
        states_num = defaultdict(int)
        for instance in queue:
            for state in instance.states_num:
                states_num[state] += instance.states_num[state]
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
    queue = []
    priority_queue = []
    counter = defaultdict(int)
    prev_name = ''
    is_sorted = False
    for i, seed in enumerate(seeds):
        instance = Instance(files[i], seed, Mutation(), [])
        queue.append(instance)
    stats_limit = len(seeds)

    while queue:
        print_runs_info(counter)
        if is_sorted:
            if not priority_queue:
                filenames = []
                for i in range(len(queue)):
                    instance = queue[i]
                    if instance.filename not in filenames:
                        priority_queue.append(instance)
                        filenames.append(instance.filename)
                    if len(priority_queue) == PRIORITY_LIMIT:
                        break
            cur_instance = get_instance(priority_queue, counter['repeat'], prev_name)
            priority_queue.append(cur_instance)
        else:
            cur_instance = get_instance(queue, counter['repeat'], prev_name)
            queue.append(cur_instance)
        if cur_instance is None:
            break
        cur_name = cur_instance.filename
        logging.info(cur_name)
        mut = cur_instance.mutation
        mut_chc = mut.apply(cur_instance.chc)
        mut_instance = Instance(cur_name, mut_chc, deepcopy(mut), cur_instance.time)

        res = True
        try:
            res = check_equ(cur_instance, mut_instance)
        except AssertionError as err:
            if cur_instance.satis == unknown:
                if err == 'timeout':
                    counter['timeout'] += 1
                else:
                    queue.remove(cur_instance)
                    if is_sorted:
                        priority_queue.remove(cur_instance)
                    counter['unknown'] += 1
                logging.info(repr(err))
            elif err == 'timeout':
                counter['timeout'] += 1
                logging.info(repr(err))
                logging.info("%s %s\n%s %s",
                             'Seed\'s time(sec):',
                             mut_instance.time[0],
                             'Mutant\'s time(sec):',
                             mut_instance.time[-1])
            else:
                counter['unknown'] += 1
                logging.error("%s -- %s",
                              'Problem',
                              repr(err))
            counter['repeat'] = 2

        if not res:
            chain = mut.get_chain()
            counter['problem'] += 1
            logging.error("%s\n%s",
                          'Problem in this chain of mutations:',
                          chain)
            logging.error("%s\n->\n%s",
                          cur_instance.chc,
                          mut_instance.chc)
            counter['repeat'] = 2

        elif mut_instance.satis != unknown:
            if prev_name == cur_name:
                counter['repeat'] += 1
            else:
                counter['repeat'] = 2
            queue.append(mut_instance)
            if is_sorted:
                priority_queue.append(mut_instance)
            logging.info('No problems found')

        logging.info('\n')
        prev_name = cur_name
        if runs_number % stats_limit == 0:
            sort_queue(queue)
            is_sorted = True
            priority_queue.clear()

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
    enable_trace("spacer")
    # enable_trace("smt_search")
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
