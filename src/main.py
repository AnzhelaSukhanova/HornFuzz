from z3 import *
from mutations import *
import sys


def get_seed(argv, seed_num):
    seeds = list()
    for i in range(seed_num):
        seed = z3.parse_smt2_file(argv[i])
        seeds.append(seed)
    return seeds


def check_equ(seeds, mut_seeds, seed_num):
    s1 = SolverFor("HORN")
    s1.set('engine', 'spacer')
    s2 = SolverFor("HORN")
    s2.set('engine', 'spacer')

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
    argc = len(argv)
    assert argc > 1, 'Seeds not found'

    seed_num = argc - 1
    seeds = get_seed(sys.argv[1:], seed_num)
    mut_seeds = mutate(seeds, seed_num)
    result = check_equ(seeds, mut_seeds, seed_num)
    print(result)


if __name__ == '__main__':
    main(sys.argv)
