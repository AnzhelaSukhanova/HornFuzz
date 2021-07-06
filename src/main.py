from mutations import *
import sys

time_limit = int(1e5)


def get_seed(argv):
    """Return the parsed seeds given by files in smt2-format"""

    seeds = [
        z3.parse_smt2_file(seed)
        for seed in argv
    ]
    return seeds


def check_equ(seeds, mut_seeds):
    """Return True if the test suites have the same satisfiability and False otherwise"""

    solver = SolverFor('HORN')
    solver.set('engine', 'spacer')
    solver.set('timeout', time_limit)

    for seed in seeds:
        solver.add(seed)
        old_res = solver.check()
        solver.reset()
        assert old_res != unknown, solver.reason_unknown()
        if old_res == unsat:
            break

    solver.add(mut_seeds)
    new_res = solver.check()
    assert new_res != unknown, solver.reason_unknown()
    print(old_res, new_res)
    return old_res == new_res


def main(argv):
    print(' '.join(argv))
    seed_num = len(argv)
    assert seed_num > 0, 'Seeds not found'
    seeds = get_seed(argv)

    mut_seeds = [seeds]
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
    print()


if __name__ == '__main__':
    main(sys.argv[1:])
