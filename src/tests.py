from main import *


def test_relational():
    assert main(['spacer-benchmarks/relational/point-location-nr.52.smt2'])
    assert main(['spacer-benchmarks/relational/point-location-nr.53.smt2'])
    assert main(['spacer-benchmarks/relational/point-location-nr.50.smt2'])
    assert main(['spacer-benchmarks/relational/inc-loop-1.smt2'])
    assert main(['spacer-benchmarks/relational/point-location-nr.54.smt2'])
    assert main(['spacer-benchmarks/relational/mccarthy-monotone.smt2'])
    assert main(['spacer-benchmarks/relational/copy-array.smt2'])
    assert main(['spacer-benchmarks/relational/mccarthy-equivalent.smt2'])
    assert main(['spacer-benchmarks/relational/point-location-nr.51.smt2'])
    assert main(['spacer-benchmarks/relational/unsafe_self_comp.smt2'])
    assert main(['spacer-benchmarks/relational/point-location-nr.49.smt2'])
    assert main(['spacer-benchmarks/relational/inc-loop-2.smt2'])
    assert main(['spacer-benchmarks/relational/inc-loop-5.smt2'])
