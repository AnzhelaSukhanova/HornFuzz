import json
import os


def get_relational(directory: str) -> set:
    """
    Return tests from the /spacer-benchmarks/relational
    that don't return 'unknown' and don't work long.
    """

    files = {
        'point-location-nr.52.smt2',
        'point-location-nr.53.smt2',
        'point-location-nr.50.smt2',
        'inc-loop-1.smt2',
        'point-location-nr.54.smt2',
        'mccarthy-monotone.smt2',
        'mccarthy-equivalent.smt2',
        'point-location-nr.51.smt2',
        'point-location-nr.49.smt2',
        'inc-loop-2.smt2',
        'inc-loop-5.smt2'
    }
    seeds = {directory +
             'spacer-benchmarks/relational/' +
             file for file in files}
    return seeds


def get_problem(directory: str) -> set:
    files = {
        'LIA-Lin/chc-LIA-Lin_214.smt2',
        'LIA-Lin/chc-LIA-Lin_239.smt2',
        'LIA-Lin/chc-LIA-Lin_244.smt2',
        'LIA-Lin/chc-LIA-Lin_258.smt2',
        'LIA-Lin/chc-LIA-Lin_450.smt2',
        'LIA-Lin-Arrays/chc-LIA-Lin-Arrays_117.smt2',
        'LIA-Lin-Arrays/chc-LIA-Lin-Arrays_182.smt2',
        'LIA-NonLin/chc-LIA-NonLin_033.smt2',
        'LIA-NonLin/chc-LIA-NonLin_417.smt2',
        'LIA-NonLin/chc-LIA-NonLin_518.smt2',
        'LIA-NonLin/chc-LIA-NonLin_575.smt2'
    }
    seeds = {directory +
             'chc-comp21-benchmarks/' +
             file for file in files}
    return seeds


def get_filenames(files: list) -> list:
    filenames = []
    for item in files:
        if os.path.isdir(item):
            for root, subdirs, files in os.walk(item):
                for file in files:
                    path = os.path.join(root, file)
                    filenames.append(path)
        else:
            filenames.append(item)
    return filenames


def get_instance_names(dir_path: str) -> set:
    """Return all seed-names from the directory with its subdirectories."""

    seeds = set()
    for root, subdirs, files in os.walk(dir_path):
        for file in files:
            if file.endswith('.smt2'):
                path = os.path.join(root, file)
                seeds.add(path)
    return seeds


def exclude_unknown_seed(seeds: set) -> set:
    file = open('exclude_seed.json', 'r')
    blacklist = json.load(file)
    return seeds.difference(blacklist)


def get_seeds(argv, directory: str) -> set:
    if len(argv) == 0:
        seeds = get_relational(directory)
    elif argv[0] == 'debug':
        seeds = get_problem(directory)
    elif argv[0] == 'all':
        dir_path = directory + 'spacer-benchmarks/'
        seeds = get_instance_names(dir_path)
        dir_path = directory + 'chc-comp21-benchmarks/'
        seeds.update(get_instance_names(dir_path))
        dir_path = directory + 'sv-benchmarks-clauses/'
        seeds.update(get_instance_names(dir_path))
        seeds = exclude_unknown_seed(seeds)
    else:
        if argv[0].endswith('.smt2'):
            seeds = set(argv)
        else:
            dir_path = directory + argv[0] + '/'
            seeds = get_instance_names(dir_path)
            seeds = exclude_unknown_seed(seeds)
    return seeds


def create_output_dirs():
    """Create directories for storing instances"""

    if not os.path.exists('output'):
        os.mkdir('output')
    for dir in {'output/last_mutants', 'output/decl',
                'output/bugs', 'output/unknown', 'output/mutants'}:
        if not os.path.exists(dir):
            os.mkdir(dir)
        if dir != 'output':
            for benchmark_dir in {'spacer-benchmarks/',
                                  'chc-comp21-benchmarks/',
                                  'sv-benchmarks-clauses/'}:
                for subdir in os.walk(benchmark_dir):
                    dir_path = dir + '/' + subdir[0]
                    if not os.path.exists(dir_path):
                        os.mkdir(dir_path)

