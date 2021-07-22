from main import *
from os import walk
from os.path import dirname, join
import subprocess


def test_relational(directory):
    """
    Run tests from the /spacer-benchmarks/relational
    that don't return 'unknown' and don't work long
    """

    files = [
        'point-location-nr.52.smt2',
        'point-location-nr.53.smt2',
        'point-location-nr.50.smt2',
        'inc-loop-1.smt2',
        'point-location-nr.54.smt2',
        'mccarthy-monotone.smt2',
        #'copy-array.smt2', #has output
        'mccarthy-equivalent.smt2',
        'point-location-nr.51.smt2',
        'point-location-nr.49.smt2',
        'inc-loop-2.smt2',
        'inc-loop-5.smt2'
    ]
    seeds = [directory +
             'spacer-benchmarks/relational/' +
             file for file in files]
    main(seeds)


def get_spacer_benchmarks(dir_path):
    """
    Return all tests from the /spacer-benchmarks
    or /spacer-benchmarks/<subdir>
    """
    seeds = []
    for root, subdirs, files in walk(dir_path):
        for file in files:
            if file.endswith('.smt2'):
                path = join(root, file)
                seeds.append(path)
    return seeds


def extract(files, root):
    """Extract files from given archives and return their paths"""
    ext_files = []
    for file in files:
        path = join(root, file)
        if file.endswith('.gz'):
            subprocess.run(['gzip -d ' + path], shell=True)
            path = path[:-3]
        elif not file.endswith('.smt2'):
            break
        ext_files.append(path)
    return ext_files


def get_chc_comp(dir_path):
    """
    Return all tests from the /chc-comp<year>-benchmarks
    or /chc-comp<year>-benchmarks/<subdir>
    """
    ext_files = []
    for root, subdirs, files in walk(dir_path):
        ext_files += extract(files, root)
    return ext_files


def test(argv, directory):
    if len(argv) == 0:
        test_relational(directory)
    elif argv[0] == '-all':
        dir_path = directory + 'spacer-benchmarks/'
        seeds = get_spacer_benchmarks(dir_path)
        dir_path = directory + 'chc-comp21-benchmarks/'
        seeds += get_chc_comp(dir_path)
        random.shuffle(seeds)
        main(seeds)
    else:
        dirs = argv[0].split('/')
        if dirs[0] == 'spacer-benchmarks':
            dir_path = directory + argv[0] + '/'
            seeds = get_spacer_benchmarks(dir_path)
            main(seeds)
        elif dirs[0][:8] == 'chc-comp':
            dir_path = directory + argv[0] + '/'
            seeds = get_chc_comp(dir_path)
            main(seeds)


if __name__ == '__main__':
    directory = dirname(dirname(sys.argv[0]))
    if directory:
        directory += '/'
    test(sys.argv[1:], directory)
