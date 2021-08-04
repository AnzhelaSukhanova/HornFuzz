from z3 import *
from collections import defaultdict
from scipy.sparse import dok_matrix
import numpy as np

TRACE_FILE = '.z3-trace'
STACK_LIMIT = 3*1e2

trace_states = defaultdict(int)
offset = 0


class TransMatrix(object):

    def __init__(self):
        self.matrix = dok_matrix((1, 1), dtype=int)

    def __add__(self, other):
        """Return the sum of two transition matrices"""
        sum = TransMatrix()
        size = len(trace_states)
        shape = (size, size)
        self.matrix.resize(shape)
        other.matrix.resize(shape)
        sum.matrix = self.matrix
        sum.matrix += other.matrix
        return sum

    def add_trans(self, i, j):
        """Add transition to matrix"""
        global trace_states
        i_ind = trace_states[i]
        j_ind = trace_states[j]
        self.matrix[i_ind, j_ind] += 1

    def read_from_trace(self):
        """Read z3-trace from last read line"""
        global offset
        trace = open(TRACE_FILE, 'r')
        trace.seek(offset)
        lines = trace.readlines()
        states = [state.rstrip() for state in lines]
        for state in states:
            if state not in trace_states:
                trace_states[state] = len(trace_states)
        size = len(trace_states)
        self.matrix = np.zeros((size, size), dtype=int)

        state = states[0]
        for next_state in states[1:]:
            self.add_trans(state, next_state)
            state = next_state
        offset = trace.tell()
        trace.close()

    def get_probability_matrix(self):
        """Return the transition matrix in probabilistic form"""
        prob_matrix = dok_matrix(self.matrix.shape, dtype=float)
        trans_num = self.matrix.sum(axis=1)
        not_zero_ind = [tuple(item) for item in np.transpose(self.matrix.nonzero())]
        for i, j in not_zero_ind:
            prob_matrix[i, j] = self.matrix[i, j] / trans_num[i]
        return prob_matrix


def get_weight_matrix(prob_matrix):
    """Return the matrix whose values are reverse to the values of the probability matrix"""
    weight_matrix = dok_matrix(prob_matrix.shape, dtype=float)
    not_zero_ind = [tuple(item) for item in np.transpose(prob_matrix.nonzero())]
    for i in not_zero_ind:
        weight_matrix[i] = 1 / prob_matrix[i]
    return weight_matrix


def count_states(states_num):
    trace = open(TRACE_FILE, 'r+')
    lines = trace.readlines()
    states = [state.rstrip() for state in lines]
    for state in states:
        states_num[state] += 1
    trace.truncate(0)
    trace.close()


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


def update_expr(expr, children, vars=None):
    """Return the expression with new children"""

    upd_expr = expr
    old_children = upd_expr.children()
    while len(children) > len(old_children):
        old_children.append(children[0])
    if not is_quantifier(expr):
        for i in range(len(children)):
            upd_expr = substitute(upd_expr, (old_children[i], children[i]))
    else:
        if vars is None:
            vars = get_bound_vars(expr)
        if expr.is_forall():
            upd_expr = ForAll(vars, children[0])
        else:
            upd_expr = Exists(vars, children[0])
    return upd_expr


def is_there_expr(expr, kind):
    """Return if there is a subexpression of the specific kind"""

    stack = [expr]
    stack_count = 0
    while len(stack) and stack_count < STACK_LIMIT:
        stack_count += 1
        cur_expr = stack.pop()
        ctx_ref = cur_expr.ctx.ref()
        ast = cur_expr.as_ast()
        if Z3_get_ast_kind(ctx_ref, ast) == kind:
            return True
        elif not is_var(expr) and not is_const(expr):
            if is_app(cur_expr) and cur_expr.decl().kind() == kind:
                return True
            for child in cur_expr.children():
                stack.append(child)
    return False


def count_expr(expr, kind):
    """Return the number of subexpressions of the specific kind"""

    expr_num = 0
    stack = [expr]
    stack_count = 0
    while len(stack) and stack_count < STACK_LIMIT:
        stack_count += 1
        cur_expr = stack.pop()
        ctx_ref = cur_expr.ctx.ref()
        ast = cur_expr.as_ast()
        if Z3_get_ast_kind(ctx_ref, ast) == kind:
            expr_num += 1
            for child in cur_expr.children():
                stack.append(child)
        elif not is_var(expr) and not is_const(expr):
            if is_app(cur_expr) and cur_expr.decl().kind() == kind:
                expr_num += 1
            for child in cur_expr.children():
                stack.append(child)
    return expr_num
