import sys
import logging
import time
from os.path import dirname

from mutations import *
from seeds import get_seeds

TIME_LIMIT = int(2 * 1e3)
INSTANCE_ID = 0
STATS_NUMBER = 1e2
stats = TransMatrix()
logging.basicConfig(format='%(message)s', filename='logfile', level=logging.INFO)


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
        self.repeat_limit = 10 * len(self.chc)


def parse_seeds(argv):
    """Return the parsed seeds given by files in smt2-format"""

    seeds = [
        z3.parse_smt2_file(seed)
        for seed in argv
    ]
    return seeds


def check_equ(instance, mut_instance):
    """Return True if the test suites have the same satisfiability and False otherwise"""
    global stats
    solver = SolverFor('HORN')
    solver.set('engine', 'spacer')
    solver.set('timeout', TIME_LIMIT)

    mut = instance.mutation
    if mut.number == 1:
        st_time = time.perf_counter()
        solver.add(instance.chc)
        instance.satis = solver.check()
        solver.reset()
        instance.time.append(time.perf_counter() - st_time)
        assert instance.satis != unknown, solver.reason_unknown()
        stats = stats.merge(get_statistics(instance.id))
        logging.info("%s %s %s %s",
                     'Seed:',
                     str(instance.satis) + ',',
                     'time(sec):', instance.time[0])

    mut_st_time = time.perf_counter()
    solver.add(mut_instance.chc)
    mut_instance.satis = solver.check()
    mut_instance.time.append(time.perf_counter() - mut_st_time)
    assert mut_instance.satis != unknown, solver.reason_unknown()
    stats = stats.merge(get_statistics(mut_instance.id))

    ins_id = 'seed' if instance.id == 0 else str(instance.id)
    logging.info("%s %s %s %s",
                 str(mut_instance.id) + ': Mutant of ' + ins_id + ' (' + str(mut.cur_type().name) + '):',
                 str(mut_instance.satis) + ',',
                 'time(sec):', mut_instance.time[-1])
    return instance.satis == mut_instance.satis


def fuzz(files, seeds):
    global stats
    queue = []
    for i, seed in enumerate(seeds):
        instance = Instance(files[i], seed, Mutation(), [])
        queue.append(instance)

    repeat_counter = 0
    prev_name = ''
    rare_state = 0
    while True and queue:
        queue_len = len(queue)
        if rare_state == 0:
            i = random.randint(0, queue_len - 1)
        else:
            i = 0
        cur_instance = queue[i]
        if repeat_counter == cur_instance.repeat_limit:
            i = cur_instance.repeat_limit
            if i == queue_len:
                break
            cur_instance = queue[i]

        cur_name = cur_instance.filename
        print(cur_name)
        logging.info(cur_name)
        mut = cur_instance.mutation
        mut_chc = mut.apply(cur_instance.chc)
        mut_instance = Instance(cur_name, mut_chc, deepcopy(mut), cur_instance.time)
        res = True

        try:
            res = check_equ(cur_instance, mut_instance)
        except AssertionError as err:
            if err == 'timeout' or cur_instance.satis == unknown:
                print(repr(err))
                logging.info(repr(err))
                if cur_instance.satis != unknown:
                    logging.info("%s %s\n%s %s",
                                 'Seed\'s time(sec):',
                                 mut_instance.time[0],
                                 'Mutant\'s time(sec):',
                                 mut_instance.time[-1])
            else:
                print('Problem --', repr(err))
                logging.error("%s -- %s",
                              'Problem',
                              repr(err))
            repeat_counter = 2

        if not res:
            chain = mut.get_chain()
            print('Problem in this chain of mutations:\n', chain)
            logging.error("%s\n%s",
                          'Problem in this chain of mutations:',
                          chain)
            logging.error("%s\n->\n%s",
                          cur_instance.chc,
                          mut_instance.chc)
            repeat_counter = 2

        elif mut_instance.satis != unknown:
            if prev_name == cur_name:
                repeat_counter += 1
            else:
                repeat_counter = 2
            queue.append(mut_instance)
            logging.info('No problems found')

        print()
        logging.info('\n')
        prev_name = cur_name

        if stats.instance_num > STATS_NUMBER:
            prob_matrix = stats.calc_probability_matrix()
            prob_vector_in_power = prob_matrix[0]
            while np.count_nonzero(prob_vector_in_power) < stats.size - 1:
                prob_vector_in_power = prob_vector_in_power.dot(prob_matrix)
            prob_vector_in_power = np.nan_to_num(prob_vector_in_power)[1:]
            min_prob_ind = prob_vector_in_power.argmin() + 1
            rare_state = stats.states[min_prob_ind]
            instance_info = stats.instance_info[min_prob_ind]
            sorted_id = sorted(instance_info.items(), key=lambda item: item[1], reverse=True)
            id_order = {elem[0]: i for i, elem in enumerate(sorted_id)}
            queue.sort(key=lambda item: id_order[item.id] if item.id in id_order else INSTANCE_ID)


def main(argv):
    # help_simplify()
    np.set_printoptions(suppress=True)
    enable_trace("spacer")
    # enable_trace("smt_search")

    directory = dirname(dirname(argv[0]))
    if directory:
        directory += '/'
    argv = argv[1:]
    files = get_seeds(argv, directory)

    seed_num = len(files)
    assert seed_num > 0, 'Seeds not found'
    seeds = parse_seeds(files)

    fuzz(files, seeds)


if __name__ == '__main__':
    main(sys.argv)
