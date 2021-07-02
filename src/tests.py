from main import *
import os


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


def test_all():
    """Run all tests from the /spacer-benchmarks/relational"""

    dir = os.path.abspath(os.getcwd()) + '/spacer-benchmarks'
    for root, subdirs, files in os.walk(dir):
        for file in files:
            if file.endswith('.smt2'):
                filepath = os.path.join(root, file)
                subpath = 'spacer-' + filepath.split("/spacer-", 1)[1]
                try:
                    main([subpath])
                except AssertionError as err:
                    print(repr(err) + '\n')


def test(argv):
    if len(argv) == 0:
        test_relational()
    elif argv[0] == '-all':
        test_all()


if __name__ == '__main__':
    test(sys.argv[1:])
