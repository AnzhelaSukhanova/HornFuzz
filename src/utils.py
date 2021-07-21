from z3 import *

exec_way = set()


def tracefunc(frame, event, arg):
    global exec_way
    if event == "call":
        exec_way.add(frame.f_code.co_name)
    return tracefunc


def get_bound_vars(expr):
    """Return bound variables"""

    vars = []
    if is_not(expr):
        expr = expr.children()[0]
    assert expr.is_forall() or expr.is_exists(), \
        'А quantifier-free expression is given'
    for i in range(expr.num_vars()):
        name = expr.var_name(i)
        sort = expr.var_sort(i)
        var = Const(name, sort)
        vars.append(var)
    return vars


def update_expr(expr, children):
    """Return the expression with new children"""

    upd_expr = expr
    old_children = upd_expr.children()
    while len(children) > len(old_children):
        old_children.append(children[0])
    for i in range(len(children)):
        upd_expr = substitute(upd_expr, (old_children[i], children[i]))
    return upd_expr


def is_there_expr(expr, kind):
    """Return if there is a subexpression of the specific kind"""
    stack = [expr]
    while len(stack):
        cur_expr = stack.pop()
        if not is_var(expr) and not is_const(expr):
            if is_app(cur_expr) and cur_expr.decl().kind() == kind:
                return True
            for child in cur_expr.children():
                stack.append(child)
    return False


def count_expr(expr, kind):
    """Return the number of subexpressions of the specific kind"""
    expr_num = 0
    stack = [expr]
    while len(stack):
        cur_expr = stack.pop()
        if not is_var(expr) and not is_const(expr):
            if is_app(cur_expr) and cur_expr.decl().kind() == kind:
                expr_num += 1
            for child in cur_expr.children():
                stack.append(child)
    return expr_num
