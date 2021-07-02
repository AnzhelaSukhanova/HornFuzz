from main import *


def test_relational():
    """
    Run tests from the /spacer-benchmarks/relational
    that don't return 'unknown'
    """

    main(['spacer-benchmarks/relational/point-location-nr.52.smt2'])
    main(['spacer-benchmarks/relational/point-location-nr.53.smt2'])
    main(['spacer-benchmarks/relational/point-location-nr.50.smt2'])
    main(['spacer-benchmarks/relational/inc-loop-1.smt2'])
    main(['spacer-benchmarks/relational/point-location-nr.54.smt2'])
    main(['spacer-benchmarks/relational/mccarthy-monotone.smt2'])
    #main(['spacer-benchmarks/relational/copy-array.smt2']) #has output
    main(['spacer-benchmarks/relational/mccarthy-equivalent.smt2'])
    main(['spacer-benchmarks/relational/point-location-nr.51.smt2'])
    main(['spacer-benchmarks/relational/unsafe_self_comp.smt2'])
    main(['spacer-benchmarks/relational/point-location-nr.49.smt2'])
    main(['spacer-benchmarks/relational/inc-loop-2.smt2'])
    main(['spacer-benchmarks/relational/inc-loop-5.smt2'])


if __name__ == '__main__':
    test_relational()
