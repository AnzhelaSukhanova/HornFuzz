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


def test_spacer_benchmarks(dir_path):
    """
    Run all tests from the /spacer-benchmarks
    or /spacer-benchmarks/<subdir>
    """
    seeds = []
    for root, subdirs, files in os.walk(dir_path):
        for file in files:
            if file.endswith('.smt2'):
                path = os.path.join(root, file)
                subpath = 'spacer-' + path.split("/spacer-")[1]
                seeds.append(subpath)
    main(seeds)


def test_chc_comp(dir_path):
    """
    Run all tests from the /chc-comp<year>-benchmarks
    or /chc-comp<year>-benchmarks/<subdir>
    """
    seeds = []
    for root, subdirs, files in os.walk(dir_path):
        for file in files:
            if file.endswith('.gz'):
                ext_file = file[:-3]
                path = os.path.join(root, file)
                if ext_file not in files:
                    subprocess.run(['gzip -d ' + path], shell=True)
                    path = path[:-3]
                subpath = 'chc-comp' + path.split("/chc-comp")[1]
                seeds.append(subpath)
    main(seeds)


def test(argv):
    if len(argv) == 0:
        test_relational()
    elif argv[0] == '-all':
        dir_path = os.path.abspath(os.getcwd()) + '/spacer-benchmarks/'
        test_spacer_benchmarks(dir_path)
        dir_path = os.path.abspath(os.getcwd()) + '/chc-comp21-benchmarks/'
        test_chc_comp(dir_path)
    else:
        dirs = argv[0].split('/')
        if dirs[0] == 'spacer-benchmarks':
            dir_path = os.path.abspath(os.getcwd()) + '/' + argv[0] + '/'
            test_spacer_benchmarks(dir_path)
        elif dirs[0][:8] == 'chc-comp':
            dir_path = os.path.abspath(os.getcwd()) + '/' + argv[0] + '/'
            test_chc_comp(dir_path)


if __name__ == '__main__':
    test(sys.argv[1:])
