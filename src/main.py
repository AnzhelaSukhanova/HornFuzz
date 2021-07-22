from mutations import *
import sys
import time
import logging
from queue import PriorityQueue

TIME_LIMIT = int(2 * 1e3)
logging.basicConfig(format='%(message)s', filename='logfile', level=logging.INFO)


class Example(object):

    def __init__(self, filename, chc, mut, time):
        self.filename = filename
        self.chc = chc
        self.satis = unknown
        self.mutation = mut
        self.time = time
        self.exec_len = 0
        self.repeat_limit = 10 * len(self.chc)

    def __lt__(self, other):
        return self.mutation.number < other.mutation.number


def get_seed(argv):
    """Return the parsed seeds given by files in smt2-format"""

    seeds = [
        z3.parse_smt2_file(seed)
        for seed in argv
    ]
    return seeds


def check_equ(example, mut_example):
    """Return True if the test suites have the same satisfiability and False otherwise"""

    global exec_way
    solver = SolverFor('HORN')
    solver.set('engine', 'spacer')
    solver.set('timeout', TIME_LIMIT)

    mut = example.mutation
    if mut.number == 1:
        st_time = time.perf_counter()
        solver.add(example.chc)
        exec_way.clear()
        sys.setprofile(tracefunc)
        example.satis = solver.check()
        example.exec_len = len(exec_way)
        solver.reset()
        example.time.append(time.perf_counter() - st_time)
        assert example.satis != unknown, solver.reason_unknown()
        logging.info("%s %s %s %s",
                     'Seed:',
                     str(example.satis) + ',',
                     'time(sec):', example.time[0])

    mut_st_time = time.perf_counter()
    solver.add(mut_example.chc)
    exec_way.clear()
    mut_example.satis = solver.check()
    mut_example.exec_len = len(exec_way)
    mut_example.time.append(time.perf_counter() - mut_st_time)
    assert mut_example.satis != unknown, solver.reason_unknown()

    logging.info("%s %s %s %s",
                 'Mutant #' + str(mut.number) + ' (' + str(mut.cur_type().name) + '):',
                 str(mut_example.satis) + ',',
                 'time(sec):', mut_example.time[-1])
    return example.satis == mut_example.satis


def main(argv):
    # help_simplify()
    seed_num = len(argv)
    assert seed_num > 0, 'Seeds not found'
    enable_trace("spacer")
    seeds = get_seed(argv)

    queue = PriorityQueue()
    for i, seed in enumerate(seeds):
        example = Example(argv[i], seed, Mutation(), [])
        queue.put((i, example))

    repeat_counter = 0
    prev_name = ''
    while True and queue.queue:
        i = 0
        _, cur_example = queue.queue[i]
        if repeat_counter == cur_example.repeat_limit:
            queue_len = len(queue.queue)
            i = cur_example.repeat_limit
            if i == queue_len:
                break
            _, cur_example = queue.queue[i]
        queue.queue.pop(i)
        cur_name = cur_example.filename
        print(cur_name)
        logging.info(cur_name)
        mut = cur_example.mutation
        mut_chc = mut.apply(cur_example.chc)
        mut_example = Example(cur_name, mut_chc, mut, cur_example.time)
        res = True

        try:
            res = check_equ(cur_example, mut_example)
        except AssertionError as err:
            if err == 'timeout' or cur_example.satis == unknown:
                print(repr(err))
                logging.info(repr(err))
                if cur_example.satis != unknown:
                    logging.info("%s %s\n%s %s",
                                 'Seed\'s time(sec):',
                                 mut_example.time[0],
                                 'Mutant\'s time(sec):',
                                 mut_example.time[-1])
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
                          cur_example.chc,
                          mut_example.chc)
            repeat_counter = 2

        elif mut_example.satis != unknown:
            cur_exec_len = cur_example.exec_len
            mut_exec_len = mut_example.exec_len
            if mut_exec_len == cur_exec_len and prev_name == cur_name:
                repeat_counter += 1
            else:
                repeat_counter = 2
            queue.put((mut_example.exec_len, mut_example))
            queue.put((cur_example.exec_len, cur_example))
            logging.info('No problems found')

        print()
        logging.info('\n')
        prev_name = cur_name


if __name__ == '__main__':
    main(sys.argv[1:])
