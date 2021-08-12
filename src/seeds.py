import json
from os import walk
from os.path import join


def get_relational(directory):
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


def get_filenames(dir_path):
    """Return all seed-names from the directory with its subdirectories."""

    seeds = set()
    for root, subdirs, files in walk(dir_path):
        for file in files:
            if file.endswith('.smt2'):
                path = join(root, file)
                seeds.add(path)
    return seeds


def exclude_unknown_seed(seeds):
    file = open('exclude_seed.json', 'r')
    blacklist = json.load(file)
    return seeds.difference(blacklist)


def get_seeds(argv, directory):
    if len(argv) == 0:
        seeds = get_relational(directory)
    elif argv[0] == 'all':
        dir_path = directory + 'spacer-benchmarks/'
        seeds = get_filenames(dir_path)
        dir_path = directory + 'chc-comp21-benchmarks/'
        seeds.update(get_filenames(dir_path))
        seeds = exclude_unknown_seed(seeds)
    else:
        if argv[0].endswith('.smt2'):
            seeds = argv
        else:
            dir_path = directory + argv[0] + '/'
            seeds = get_filenames(dir_path)
            seeds = exclude_unknown_seed(seeds)
    return seeds
