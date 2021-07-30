from z3 import *
from collections import defaultdict
import numpy as np

TRACE_FILE = '.z3-trace'
trace_states = []
trace_last_line = 0


class TransMatrix(object):

    def __init__(self):
        self.trans_matrix = np.array([], dtype=int)
        self.trans_num = defaultdict(int)
        self.size = len(trace_states)

    def __add__(self, other):
        """Return the sum of two transition matrices"""
        global trace_states
        sum = TransMatrix()
        sum.trans_matrix = np.zeros((sum.size, sum.size), dtype=int)
        sum.trans_matrix[:self.size, :self.size] += self.trans_matrix
        sum.trans_matrix[:other.size, :other.size] += other.trans_matrix
        for i in self.trans_num:
            sum.trans_num[i] = self.trans_num[i]
        for i in other.trans_num:
            sum.trans_num[i] += other.trans_num[i]
        return sum

    def add_trans(self, i, j, instance_id):
        """Add transition to matrix"""
        global trace_states
        i_ind = trace_states.index(i)
        j_ind = trace_states.index(j)

        self.trans_matrix[i_ind, j_ind] += 1
        self.trans_num[i_ind] += 1

    def read_from_trace(self, instance_id):
        """Read z3-trace from last read line"""
        global trace_last_line
        trace = open(TRACE_FILE, 'r')
        lines = trace.readlines()
        trace_len = len(lines)
        states = [state.rstrip() for state in lines[trace_last_line: trace_len]]
        for state in states:
            if state not in trace_states:
                trace_states.append(state)
        self.size = len(trace_states)
        trace_last_line = trace_len
        self.trans_matrix = np.zeros((self.size, self.size), dtype=int)

        state = states[0]
        for next_state in states[1:]:
            self.add_trans(state, next_state, instance_id)
            state = next_state

    def get_probability_matrix(self):
        """Return the transition matrix in probabilistic form"""
        prob_matrix = np.empty((self.size, self.size), dtype=float)
        for i in self.trans_num:
            prob_matrix[i] = np.divide(self.trans_matrix[i], self.trans_num[i])
        return prob_matrix


def get_weight_matrix(prob_matrix):
    """Return the matrix whose values are reverse to the values of the probability matrix"""

    shape = prob_matrix.shape
    weight_matrix = np.zeros(shape, dtype=float)
    for i in range(shape[0]):
        for j in range(shape[1]):
            if prob_matrix[i, j]:
                weight_matrix[i, j] = 1 / prob_matrix[i, j]
    return weight_matrix


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
