from z3 import *
from collections import defaultdict
import numpy as np

TRACE_FILE = '.z3-trace'
trace_states = []


class TransMatrix(object):

    def __init__(self):
        self.trans_matrix = np.array([], dtype=int)
        self.size = len(trace_states)

    def __add__(self, other):
        """Return the sum of two transition matrices"""
        global trace_states
        sum = TransMatrix()
        sum.trans_matrix = np.zeros((sum.size, sum.size), dtype=int)
        sum.trans_matrix[:self.size, :self.size] += self.trans_matrix
        sum.trans_matrix[:other.size, :other.size] += other.trans_matrix
        return sum

    def add_trans(self, i, j):
        """Add transition to matrix"""
        global trace_states
        i_ind = trace_states.index(i)
        j_ind = trace_states.index(j)
        self.trans_matrix[i_ind, j_ind] += 1

    def read_from_trace(self):
        """Read z3-trace from last read line"""
        trace = open(TRACE_FILE, 'r+')
        lines = trace.readlines()
        states = [state.rstrip() for state in lines]
        for state in states:
            if state not in trace_states:
                trace_states.append(state)
        self.size = len(trace_states)
        self.trans_matrix = np.zeros((self.size, self.size), dtype=int)

        state = states[0]
        for next_state in states[1:]:
            self.add_trans(state, next_state)
            state = next_state
        trace.truncate(0)
        trace.close()

    def get_probability_matrix(self):
        """Return the transition matrix in probabilistic form"""
        prob_matrix = np.zeros((self.size, self.size), dtype=float)
        if self.size > 1:
            trans_num = np.sum(self.trans_matrix, axis=1)
        else:
            trans_num = self.trans_matrix
        not_zero_ind = np.where(trans_num != 0)
        prob_matrix[not_zero_ind] = self.trans_matrix[not_zero_ind] / trans_num[not_zero_ind, None]
        return prob_matrix


def get_weight_matrix(prob_matrix):
    """Return the matrix whose values are reverse to the values of the probability matrix"""

    weight_matrix = np.divide(1, prob_matrix,
                              out=np.zeros_like(prob_matrix),
                              where=prob_matrix != 0,
                              dtype=float)
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
    while len(stack):
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
    while len(stack):
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


def timeout_handler(signum, frame):
    raise Exception('Timeout of applying mutation')
