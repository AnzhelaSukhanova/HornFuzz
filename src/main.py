from z3 import *
from mutations import *
import sys


def get_seed(argv):
    seeds = list()
    seed_num = len(argv)
    for i in range(seed_num):
        seed = z3.parse_smt2_file(argv[i])
        seeds.append(seed)
    return seeds


def check_equ(seeds, mut_seeds):
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
    seed_num = len(argv)
    assert seed_num > 0, 'Seeds not found'

    seeds = get_seed(argv)
    mut_seeds = mutate(seeds)
    result = check_equ(seeds, mut_seeds)
    return result


if __name__ == '__main__':
    print(main(sys.argv[1:]))
