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
        'unsafe_self_comp.smt2',
        'point-location-nr.49.smt2',
        'inc-loop-2.smt2',
        'inc-loop-5.smt2'
    ]
    for file in files:
        main(['spacer-benchmarks/relational/' + file])


def test_mut_conn():
    """Check mutation connecting seeds if they don't depend on each other"""

    sets = [
        ['inc-loop-1.smt2', 'unsafe_self_comp.smt2'],
        ['inc-loop-2.smt2', 'point-location-nr.49.smt2'],
        ['inc-loop-5.smt2', 'point-location-nr.50.smt2', 'unsafe_self_comp.smt2'],
        ['mccarthy-monotone.smt2', 'point-location-nr.51.smt2', 'unsafe_self_comp.smt2'],
        ['mccarthy-equivalent.smt2', 'point-location-nr.52.smt2', 'unsafe_self_comp.smt2']
    ]
    for files in sets:
        argv = []
        for file in files:
            argv.append('spacer-benchmarks/relational/' + file)
        main(argv)


def test_spacer_benchmarks(dir_path):
    """
    Run all tests from the /spacer-benchmarks
    or /spacer-benchmarks/<subdir>
    """

    for root, subdirs, files in os.walk(dir_path):
        for file in files:
            if file.endswith('.smt2'):
                path = os.path.join(root, file)
                subpath = 'spacer-' + path.split("/spacer-")[1]
                try:
                    main([subpath])
                except AssertionError as err:
                    print(repr(err) + '\n')


def test_chc_comp(dir_path):
    """
    Run all tests from the /chc-comp<year>-benchmarks
    or /chc-comp<year>-benchmarks/<subdir>
    """

    for root, subdirs, files in os.walk(dir_path):
        for file in files:
            if file.endswith('.gz'):
                ext_file = file[:-3]
                path = os.path.join(root, file)
                if ext_file not in files:
                    subprocess.run(['gzip -d ' + path], shell=True)
                    path = path[:-3]
                subpath = 'chc-comp' + path.split("/chc-comp")[1]
                try:
                    main([subpath])
                except AssertionError as err:
                    print(repr(err) + '\n')


def test(argv):
    if len(argv) == 0:
        test_relational()
    elif argv[0] == '-conn':
        test_mut_conn()
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
