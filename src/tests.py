from main import *
import os
import subprocess


def test_relational():
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
    seeds = ['spacer-benchmarks/relational/' + file for file in files]
    main(seeds)


def get_spacer_benchmarks(dir_path):
    """
    Return all tests from the /spacer-benchmarks
    or /spacer-benchmarks/<subdir>
    """
    seeds = []
    for root, subdirs, files in os.walk(dir_path):
        for file in files:
            if file.endswith('.smt2'):
                path = os.path.join(root, file)
                subpath = 'spacer-' + path.split("/spacer-")[1]
                seeds.append(subpath)
    return seeds


def extract(files, root):
    """Extract files from given archives and return their paths"""
    ext_files = []
    for file in files:
        if file.endswith('.gz'):
            ext_file = file[:-3]
            if ext_file not in files:
                path = os.path.join(root, file)
                subprocess.run(['gzip -d ' + path], shell=True)
            path = os.path.join(root, ext_file)
            ext_files.append(path)
    return ext_files


def get_chc_comp(dir_path):
    """
    Return all tests from the /chc-comp<year>-benchmarks
    or /chc-comp<year>-benchmarks/<subdir>
    """
    seeds = []
    for root, subdirs, files in os.walk(dir_path):
        ext_files = extract(files, root)
        for path in ext_files:
            subpath = 'chc-comp' + path.split("/chc-comp")[1]
            seeds.append(subpath)
    return seeds


def test(argv):
    if len(argv) == 0:
        test_relational()
    elif argv[0] == '-all':
        dir_path = os.path.abspath(os.getcwd()) + '/spacer-benchmarks/'
        seeds = get_spacer_benchmarks(dir_path)
        dir_path = os.path.abspath(os.getcwd()) + '/chc-comp21-benchmarks/'
        seeds += get_chc_comp(dir_path)
        random.shuffle(seeds)
        main(seeds)
    else:
        dirs = argv[0].split('/')
        if dirs[0] == 'spacer-benchmarks':
            dir_path = os.path.abspath(os.getcwd()) + '/' + argv[0] + '/'
            seeds = get_spacer_benchmarks(dir_path)
            main(seeds)
        elif dirs[0][:8] == 'chc-comp':
            dir_path = os.path.abspath(os.getcwd()) + '/' + argv[0] + '/'
            seeds = get_chc_comp(dir_path)
            main(seeds)


if __name__ == '__main__':
    test(sys.argv[1:])
