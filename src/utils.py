from z3 import *
from collections import defaultdict
import numpy as np
from copy import deepcopy

TRACE_FILE = '.z3-trace'
trace_last_line = 0


class TransMatrix(object):

    def __init__(self):
        self.trans_matrix = np.array([], dtype=int)
        self.instance_info = defaultdict()
        self.trans_num = defaultdict(int)
        self.instance_num = 0
        self.size = 0
        self.states = []

    def add_trans(self, i, j, instance_id):
        """Add transition to matrix"""
        old_trans_matrix = self.trans_matrix
        old_size = self.size
        if i not in self.states:
            self.states.append(i)
            self.size += 1
        if j not in self.states:
            self.states.append(j)
            self.size += 1
        self.trans_matrix = np.zeros((self.size, self.size), dtype=int)
        self.trans_matrix[:old_size, :old_size] = old_trans_matrix
        i_ind = self.states.index(i)
        j_ind = self.states.index(j)

        self.trans_num[i_ind] += 1
        self.trans_matrix[i_ind, j_ind] += 1
        if j_ind not in self.instance_info:
            self.instance_info[j_ind] = defaultdict(int)
        self.instance_info[j_ind][instance_id] += 1

    def calc_probability_matrix(self):
        """Return the transition matrix in probabilistic form"""
        prob_matrix = np.empty((self.size, self.size), dtype=float)
        for i in self.trans_num:
            prob_matrix[i] = np.divide(self.trans_matrix[i], self.trans_num[i])
        return prob_matrix

    def merge(self, other):
        """Return the union of two transition matrices"""
        new_matrix = deepcopy(self)
        new_matrix.instance_num += other.instance_num
        for j in other.instance_info:
            for i in other.trans_num:
                if other.trans_matrix[i, j] > 0:
                    for id in other.instance_info[j]:
                        for k in range(other.instance_info[j][id]):
                            new_matrix.add_trans(other.states[i], other.states[j], id)
                    break
        return new_matrix


def get_statistics(instance_id):
    """Read z3-trace from last read line"""

    global trace_last_line
    trace = open(TRACE_FILE, 'r')
    matrix = TransMatrix()
    lines = trace.readlines()
    trace_len = len(lines)

    state = lines[0].rstrip().split(':')[-1]
    for i in range(trace_last_line, trace_len):
        line = lines[i]
        next_state = line.rstrip().split(':')[-1]
        matrix.add_trans(state, next_state, instance_id)
        state = next_state
    matrix.instance_num += 1
    trace_last_line = trace_len
    return matrix


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
