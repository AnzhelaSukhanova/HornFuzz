import hashlib
import random
import traceback
from collections import defaultdict
from copy import deepcopy
from enum import Enum

import numpy as np
from scipy.sparse import dok_matrix
from z3 import *

TRACE_FILE = '.z3-trace'

trace_states = defaultdict(int)
trans_offset = 0
info_kinds = [Z3_OP_AND, Z3_OP_OR, Z3_QUANTIFIER_AST,
              Z3_OP_LE, Z3_OP_GE, Z3_OP_LT, Z3_OP_GT,
              Z3_OP_UNINTERPRETED]


def global_ctx_access_exception():
    raise Exception('Global z3 context access')


class State(object):

    def __init__(self, line: str):
        parts = line.rstrip().split('/')
        self.state = parts[0].split('..')[0]  # function
        self.state += parts[-1]  # file:line

    def __eq__(self, other):
        if self.state != other.state:
            return False
        return True

    def __hash__(self):
        return hash(self.state)

    def encode(self, standart: str):
        return self.state.encode(standart)


class ClauseInfo(object):

    def __init__(self, number: int):
        self.expr_exists = defaultdict(bool)
        self.is_expr_in_clause = np.zeros((len(info_kinds), number),
                                          dtype=bool)


class StatsType(Enum):
    DEFAULT = 0
    TRANSITIONS = 1
    STATES = 2
    ALL = 3


stats_type = StatsType.DEFAULT


def set_stats_type(heuristics: defaultdict):
    """Set the type of statistics based on heuristics."""
    global stats_type

    if heuristics['transitions'] and heuristics['states']:
        stats_type = StatsType.ALL
    elif heuristics['transitions']:
        stats_type = StatsType.TRANSITIONS
    elif heuristics['states']:
        stats_type = StatsType.STATES


class TraceStats(object):

    def __init__(self):
        self.hash = 0

        if stats_type in {StatsType.TRANSITIONS, StatsType.ALL}:
            self.matrix = dok_matrix((1, 1), dtype=int)

        if stats_type in {StatsType.STATES, StatsType.ALL}:
            self.states_num = defaultdict(int)

    def __add__(self, other):
        """Return the sum of two transition matrices."""
        sum = TraceStats()

        if stats_type in {StatsType.TRANSITIONS, StatsType.ALL}:
            size = len(trace_states)
            shape = (size, size)
            self.matrix.resize(shape)
            other.matrix.resize(shape)
            sum.matrix = self.matrix
            sum.matrix += other.matrix

        if stats_type in {StatsType.STATES, StatsType.ALL}:
            sum.states_num = deepcopy(self.states_num)
            for state in other.states_num:
                sum.states_num[state] += other.states_num[state]
        return sum

    def add_trans(self, i: int, j: int):
        """Add transition to matrix."""
        global trace_states
        i_ind = trace_states[i]
        j_ind = trace_states[j]
        self.matrix[i_ind, j_ind] += 1

    def read_from_trace(self):
        """Read z3-trace from last read line."""
        global trans_offset
        trace = open(TRACE_FILE, 'r')
        trace.seek(trans_offset)
        lines = trace.readlines()
        hash_builder = hashlib.sha512()
        prev_state = None

        for line in lines:
            state = State(line)
            hash_builder.update(state.encode('utf-8'))
            if stats_type.value > 0:
                if state not in trace_states:
                    trace_states[state] = len(trace_states)

            if stats_type in {StatsType.STATES, StatsType.ALL}:
                self.states_num[state] += 1

            if stats_type in {StatsType.TRANSITIONS, StatsType.ALL}:
                size = len(trace_states)
                self.matrix = dok_matrix((size, size), dtype=int)
                if prev_state:
                    self.add_trans(prev_state, state)
                prev_state = state

        self.hash = hash_builder.digest()

        trans_offset = trace.tell()
        trace.close()

    def get_probability(self, type: StatsType):
        """
        Return the transition matrix in probabilistic form
        or state probabilities.
        """
        if type == StatsType.TRANSITIONS:
            prob = dok_matrix(self.matrix.shape, dtype=float)
            trans_num = self.matrix.sum(axis=1)
            not_zero_ind = [tuple(item)
                            for item in np.transpose(self.matrix.nonzero())]
            for i, j in not_zero_ind:
                prob[i, j] = self.matrix[i, j] / trans_num[i]
        elif type == StatsType.STATES:
            total_states_num = sum(self.states_num.values())
            prob = {state: self.states_num[state] / total_states_num
                    for state in self.states_num}
        else:
            assert False, 'The probability cannot be calculated ' \
                          'for this type of statistics'
        return prob

    def get_weights(self, type: StatsType):
        """Return the weights of trace transitions or states."""
        if type == StatsType.TRANSITIONS:
            prob_matrix = self.get_probability(type)
            weights = dok_matrix(prob_matrix.shape, dtype=float)
            not_zero_ind = [tuple(item)
                            for item in np.transpose(prob_matrix.nonzero())]
            for i in not_zero_ind:
                weights[i] = 1 / prob_matrix[i]
        elif type == StatsType.STATES:
            total_states_num = sum(self.states_num.values())
            weights = {state: total_states_num / self.states_num[state]
                       for state in self.states_num}
        else:
            assert False, 'Weights cannot be calculated ' \
                          'for this type of statistics'
        return weights


def get_bound_vars(expr) -> list:
    """Return bound variables."""

    vars = []
    if is_not(expr):
        expr = expr.children()[0]
    if is_quantifier(expr):
        for i in range(expr.num_vars()):
            name = expr.var_name(i)
            sort = expr.var_sort(i)
            var = Const(name, sort)
            vars.append(var)
    return vars


def update_expr(expr, children, vars: list = None):
    """Return the expression with new children."""

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


def expr_exists(instance, kinds: list) -> defaultdict:
    """Return if there is a subexpression of the specific kind."""

    expr_ex = defaultdict(bool)
    ind = list(range(len(kinds)))
    length = len(instance) if isinstance(instance, AstVector) else 1
    for i in range(length):
        expr = instance[i] if isinstance(instance, AstVector) else instance
        expr_set = {expr} if not is_var(expr) and not is_const(expr) else {}
        while len(expr_set) and ind:
            cur_expr = expr_set.pop()
            for j in ind:
                if check_ast_kind(cur_expr, kinds[j]) or \
                        is_app_of(cur_expr, kinds[j]):
                    expr_ex[j] = True
                    ind.remove(j)
                    break
            if ind:
                for child in cur_expr.children():
                    expr_set.add(child)
    return expr_ex


def count_expr(instance, kinds: list, is_unique=False):
    """Return the number of subexpressions of the specific kind."""

    unique_expr = defaultdict(set)
    expr_num = defaultdict(int)
    length = len(instance) if isinstance(instance, AstVector) else 1
    for i in range(length):
        expr = instance[i] if isinstance(instance, AstVector) else instance
        expr_set = {expr} if not is_var(expr) and not is_const(expr) else {}
        while len(expr_set):
            cur_expr = expr_set.pop()
            for j in range(len(kinds)):
                if check_ast_kind(cur_expr, kinds[j]) or \
                        is_app_of(cur_expr, kinds[j]):
                    if is_unique:
                        expr_num[j] += 1
                        unique_expr[j].add(cur_expr.decl())
                    else:
                        expr_num[j] += 1
                    break
            for child in cur_expr.children():
                expr_set.add(child)
    if is_unique:
        return expr_num, unique_expr
    else:
        return expr_num


def check_ast_kind(expr, kind) -> bool:
    ctx_ref = expr.ctx.ref()
    ast = expr.as_ast()
    return Z3_get_ast_kind(ctx_ref, ast) == kind


def shuffle_vars(vars):
    """Shuffle the variables preserving sort order."""

    sort_groups = defaultdict(list)
    sort_order = []

    for var in vars:
        sort = var.sort()
        sort_order.append(sort)
        sort_groups[var.sort()].append(var)
    for sort in sort_groups:
        random.shuffle(sort_groups[sort])
    vars.clear()

    for sort in sort_order:
        next_var = sort_groups[sort].pop()
        vars.append(next_var)


def remove_clauses(chc_system: AstVector, ind) -> AstVector:
    """Remove the clauses from the chc-system at the given indices."""
    new_system = AstVector(ctx=chc_system.ctx)
    for i, clause in enumerate(chc_system):
        if i not in ind:
            new_system.push(clause)
    return new_system
