from z3 import *
from mutations import *
import sys


def get_seed(argv):
    """Return the parsed seeds given by files in smt2-format"""

    seeds = list()
    seed_num = len(argv)
    for i in range(seed_num):
        seed = z3.parse_smt2_file(argv[i])
        seeds.append(seed)
    return seeds


def check_equ(seeds, mut_seeds):
    """Return True if the test suites have the same satisfiability and False otherwise"""

    s1 = SolverFor("HORN")
    s1.set('engine', 'spacer')
    s2 = SolverFor("HORN")
    s2.set('engine', 'spacer')

    seed_num = len(seeds)
    for i in range(seed_num):
        s1.add(seeds[i])
    old_res = s1.check()
    assert old_res != unknown, s1.reason_unknown()

    for i in range(len(mut_seeds)):
        s2.add(mut_seeds[i])
    new_res = s2.check()
    assert new_res != unknown, s2.reason_unknown()
    return old_res == new_res


def main(argv):
    print(''.join(argv))
    seed_num = len(argv)
    assert seed_num > 0, 'Seeds not found'
    seeds = get_seed(argv)

    mut_seeds = list()
    mut_seeds.append(seeds)
    mut = Mutation()

    i = 1
    found_err = False
    while not mut.is_final:
        mut_seeds.append(mut.apply(seeds))
        for j in range(i):
            if not check_equ(mut_seeds[j], mut_seeds[i]):
                if not found_err:
                    print('Found a problem in these chains of mutations:')
                    found_err = True
                mut.print_chain(j, i)
        i += 1
    if not found_err:
        print('No problems found')


if __name__ == '__main__':
    main(sys.argv[1:])
