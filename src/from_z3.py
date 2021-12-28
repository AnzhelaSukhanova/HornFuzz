from z3 import *


def to_expr_ref(a, ctx):
    if isinstance(a, Pattern):
        return PatternRef(a, ctx)
    ctx_ref = ctx.ref()
    k = Z3_get_ast_kind(ctx_ref, a)
    if k == Z3_QUANTIFIER_AST:
        return QuantifierRef(a, ctx)
    sk = Z3_get_sort_kind(ctx_ref, Z3_get_sort(ctx_ref, a))
    if sk == Z3_BOOL_SORT:
        return BoolRef(a, ctx)
    if sk == Z3_INT_SORT:
        if k == Z3_NUMERAL_AST:
            return IntNumRef(a, ctx)
        return ArithRef(a, ctx)
    if sk == Z3_REAL_SORT:
        if k == Z3_NUMERAL_AST:
            return RatNumRef(a, ctx)
        if _is_algebraic(ctx, a):
            return AlgebraicNumRef(a, ctx)
        return ArithRef(a, ctx)
    if sk == Z3_BV_SORT:
        if k == Z3_NUMERAL_AST:
            return BitVecNumRef(a, ctx)
        else:
            return BitVecRef(a, ctx)
    if sk == Z3_ARRAY_SORT:
        return ArrayRef(a, ctx)
    if sk == Z3_DATATYPE_SORT:
        return DatatypeRef(a, ctx)
    if sk == Z3_FLOATING_POINT_SORT:
        if k == Z3_APP_AST and _is_numeral(ctx, a):
            return FPNumRef(a, ctx)
        else:
            return FPRef(a, ctx)
    if sk == Z3_FINITE_DOMAIN_SORT:
        if k == Z3_NUMERAL_AST:
            return FiniteDomainNumRef(a, ctx)
        else:
            return FiniteDomainRef(a, ctx)
    if sk == Z3_ROUNDING_MODE_SORT:
        return FPRMRef(a, ctx)
    if sk == Z3_SEQ_SORT:
        return SeqRef(a, ctx)
    if sk == Z3_RE_SORT:
        return ReRef(a, ctx)
    return ExprRef(a, ctx)


def _is_numeral(ctx, a):
    return Z3_is_numeral_ast(ctx.ref(), a)


def _is_algebraic(ctx, a):
    return Z3_is_algebraic_number(ctx.ref(), a)


def to_ast_list(args: list):
    sz = len(args)
    _args = (Ast * sz)()
    for i in range(sz):
        _args[i] = args[i].as_ast() if not isinstance(args[i], Ast) \
            else args[i]
    return _args


def _coerce_expr_merge(s, a):
    if is_expr(a):
        s1 = a.sort()
        if s is None:
            return s1
        if s1.eq(s):
            return s
        elif s.subsort(s1):
            return s1
        elif s1.subsort(s):
            return s
        else:
            if z3_debug():
                assert s1.ctx == s.ctx, "context mismatch"
                assert False, "sort mismatch"
    else:
        return s


def coerce_exprs(a, ctx=None):
    if isinstance(a, Ast):
        return a
    if not is_expr(a):
        a = _py2expr(a, ctx)
    s = None
    s = _coerce_expr_merge(s, a)
    a = s.cast(a)
    return a


def _py2expr(a, ctx=None):
    if isinstance(a, bool):
        return BoolVal(a, ctx)
    if is_int(a):
        return IntVal(a, ctx)
    if isinstance(a, float):
        return RealVal(a, ctx)
    if isinstance(a, str):
        return StringVal(a, ctx)
    if is_expr(a):
        return a
    if z3_debug():
        assert False, "Python bool, int, long or float expected. " \
                      "Got:" + str(type(a))
