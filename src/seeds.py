import subprocess
import re
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


def get_spacer_benchmarks(dir_path):
    """
    Return all tests from the /spacer-benchmarks
    or /spacer-benchmarks/<subdir>.
    """

    seeds = set()
    for root, subdirs, files in walk(dir_path):
        for file in files:
            if file.endswith('.smt2'):
                path = join(root, file)
                seeds.add(path)
    return seeds


def extract(files, root):
    """Extract files from given archives and return their paths."""

    ext_files = set()
    for file in files:
        path = join(root, file)
        if file.endswith('.gz'):
            subprocess.run(['gzip -d ' + path], shell=True)
            path = path[:-3]
        elif not file.endswith('.smt2'):
            break
        ext_files.add(path)
    return ext_files


def get_chc_comp(dir_path):
    """
    Return all tests from the /chc-comp<year>-benchmarks
    or /chc-comp<year>-benchmarks/<subdir>.
    """

    ext_files = set()
    for root, subdirs, files in walk(dir_path):
        ext_files.update(extract(files, root))
    return ext_files


def exclude_unknown_seed(seeds):
    file = open('exclude_seed.json', 'r')
    blacklist = json.load(file)
    return seeds.difference(blacklist)


def get_seeds(argv, directory):
    if len(argv) == 0:
        seeds = get_relational(directory)
    elif argv[0] == 'all':
        dir_path = directory + 'spacer-benchmarks/'
        seeds = get_spacer_benchmarks(dir_path)
        dir_path = directory + 'chc-comp21-benchmarks/'
        seeds.update(get_chc_comp(dir_path))
        seeds = exclude_unknown_seed(seeds)
    else:
        if argv[0].endswith('.smt2'):
            seeds = argv
        else:
            dirs = argv[0].split('/')
            if dirs[0] == 'spacer-benchmarks':
                dir_path = directory + argv[0] + '/'
                seeds = get_spacer_benchmarks(dir_path)
                seeds = exclude_unknown_seed(seeds)
            elif re.match(r'chc-comp\d\d-benchmarks', dirs[0]):
                dir_path = directory + argv[0] + '/'
                seeds = get_chc_comp(dir_path)
                seeds = exclude_unknown_seed(seeds)
            else:
                seeds = set()
    return seeds
