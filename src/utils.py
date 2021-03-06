import hashlib
import json
import random
import traceback
from collections import defaultdict
from copy import deepcopy
from enum import Enum
from typing import List

import numpy as np
from scipy.sparse import dok_matrix
from src.from_z3 import *

TRACE_FILE = '.z3-trace'

trace_states = defaultdict(int)
trace_offset = 0
info_kinds = {Z3_OP_AND: '(declare-fun and *)',
              Z3_OP_OR: '(declare-fun or *)',
              Z3_QUANTIFIER_AST: 'quantifiers',
              Z3_OP_LE: '(declare-fun <= *)',
              Z3_OP_GE: '(declare-fun >= *)',
              Z3_OP_LT: '(declare-fun < *)',
              Z3_OP_GT: '(declare-fun > *)',
              Z3_OP_UNINTERPRETED: 'uninterpreted-functions',
              None: None}

current_ctx = None


def set_ctx(ctx):
    global current_ctx
    current_ctx = ctx


class State(object):

    def __init__(self, line: str):
        parts = line.rstrip().split('/')
        self.name = parts[0].split('..')[0]  # function
        self.name += parts[-1]  # file:line

    def __eq__(self, other):
        if self.name != other.name:
            return False
        return True

    def __hash__(self):
        return hash(self.name)

    def encode(self, standart: str):
        return self.name.encode(standart)

    def save(self):
        return self.name

    @staticmethod
    def load(data) -> 'State':
        state = State('')
        state.name = data
        return state


class ClauseInfo(object):

    def __init__(self, number: int):
        self.expr_num = defaultdict(int)
        self.clause_expr_num = defaultdict(object)
        for kind in info_kinds:
            self.clause_expr_num[kind] = np.zeros(number, dtype=int)


class StatsType(Enum):
    DEFAULT = 0
    TRANSITIONS = 1
    STATES = 2
    ALL = 3


stats_type = StatsType.DEFAULT
with_formula_heur = False


def set_stats_type(heuristics: defaultdict):
    """Set the type of statistics based on heuristics."""
    global stats_type, with_formula_heur

    if heuristics['transitions'] and heuristics['states']:
        stats_type = StatsType.ALL
    elif heuristics['transitions']:
        stats_type = StatsType.TRANSITIONS
    elif heuristics['states']:
        stats_type = StatsType.STATES

    if heuristics['difficulty'] or heuristics['simplicity']:
        with_formula_heur = True


class TraceStats(object):

    def __init__(self):
        self.hash = 0

        if stats_type in {StatsType.TRANSITIONS, StatsType.ALL}:
            self.matrix = dok_matrix((1, 1), dtype=int)

        if stats_type in {StatsType.STATES, StatsType.ALL}:
            self.states_num = defaultdict(int)

    def __add__(self, other):
        """Return the sum of two transition matrices."""
        if stats_type == StatsType.DEFAULT:
            return self

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

    def add_trans(self, i: State, j: State):
        """Add transition to matrix."""
        global trace_states
        i_ind = trace_states[i]
        j_ind = trace_states[j]
        self.matrix[i_ind, j_ind] += 1

    def read_from_trace(self, is_seed: bool = False):
        """Read z3-trace from last read line."""
        with open(TRACE_FILE, 'r') as trace:
            trace.seek(trace_offset)
            lines = trace.readlines()
        states = [State(line) for line in lines]
        self.load_states(states)
        if is_seed:
            self.states = states

    def reset_trace_offset(self):
        global trace_offset
        with open(TRACE_FILE, 'r') as trace:
            trace_offset = trace.seek(0, io.SEEK_END)

    def load_states(self, states: List[State]):
        hash_builder = hashlib.sha512()
        prev_state = None
        for state in states:
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


def find_term(clause: QuantifierRef, term_kind: int, trans_num: int, is_removing: bool, is_quantifier: bool):
    ctx_ref = current_ctx.ref()
    path = ctypes.c_ulonglong(Z3_mk_int_vector(ctx_ref))
    term = to_expr_ref(Z3_find_term(ctx_ref,
                                    clause.as_ast(),
                                    term_kind,
                                    trans_num,
                                    is_removing,
                                    is_quantifier,
                                    path),
                       current_ctx)
    return term, path


def set_term(clause: QuantifierRef, new_term, path):
    result = to_expr_ref(Z3_set_term(current_ctx.ref(),
                                     clause.as_ast(),
                                     new_term.as_ast(),
                                     path),
                         current_ctx)
    Z3_free_int_vector(current_ctx.ref(), path)
    return result


def update_quantifier(expr, children, vars: list = None):
    """Return the expression with new children."""
    if vars is None:
        vars, _ = get_vars_and_body(expr)
    try:
        if expr.is_forall():
            upd_expr = ForAll(vars, children[0])
        else:
            upd_expr = Exists(vars, children[0])
    except Exception:
        print(expr)
        raise
    return upd_expr


def count_expr(chc, kinds: list, is_unique=False):
    """Return the number of subexpressions of the specific kind."""

    assert chc is not None, "Empty chc-system"
    expr_num = defaultdict(int)

    goal = Goal(ctx=current_ctx)
    goal.append(chc)
    tactic = Tactic('collect-statistics', ctx=current_ctx)
    tactic.apply(goal, 'to_file', True)

    with open(".collect_stats.json") as file:
        stats = json.load(file)

    for kind in kinds:
        decl = info_kinds[kind]
        if decl in stats:
            if kind == Z3_OP_UNINTERPRETED and not is_unique:
                decl = decl[:-1] + "-occurrences"
            expr_num[kind] = stats[decl]

    return expr_num


def check_ast_kind(expr, kind) -> bool:
    ctx_ref = current_ctx.ref()
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
    new_system = AstVector(ctx=current_ctx)
    for i, clause in enumerate(chc_system):
        if i not in ind:
            new_system.push(clause)
    return new_system


def get_predicates(chc) -> set:
    pred_set = set()
    length = len(chc) if isinstance(chc, AstVector) else 1
    for i in range(length):
        expr = chc[i] if isinstance(chc, AstVector) else chc
        expr_set = {expr} if not is_var(expr) and not is_const(expr) else {}
        while len(expr_set):
            cur_expr = expr_set.pop()
            if is_app_of(cur_expr, Z3_OP_UNINTERPRETED):
                pred_set.add(cur_expr.decl())
                continue
            for child in cur_expr.children():
                expr_set.add(child)
    return pred_set


def take_pred_from_clause(clause: AstVector, with_term=False):
    uninter_pred = get_predicates(clause)
    assert uninter_pred, "Uninterpreted predicate not found" + clause.sexpr()
    upred = random.sample(uninter_pred, 1)[0]

    vars = []
    for i in range(upred.arity()):
        sort = upred.domain(i)
        vars.append(FreshConst(sort, prefix='x'))
    upred_value = upred.__call__(vars)
    if with_term:
        return upred_value, vars, upred
    else:
        return upred_value, vars


def equivalence_check(seed: AstVector, mutant: AstVector) -> bool:
    solver = Solver(ctx=current_ctx)

    for i, clause in enumerate(seed):
        solver.reset()
        mut_clause = mutant[i]
        expr = Xor(clause, mut_clause, ctx=current_ctx)
        solver.add(expr)
        result = solver.check()

        if result != unsat:
            return False
    return True


def get_vars_and_body(clause):
    def get_vars(expr):
        vars = []
        for i in range(expr.num_vars()):
            name = expr.var_name(i)
            sort = expr.var_sort(i)
            var = Const(name, sort)
            vars.append(var)
        return vars

    expr = clause
    vars = []
    child = clause.children()[0] if clause.children() else None
    expr = remove_dup_not(expr)

    while is_quantifier(expr) or is_quantifier(child):
        if is_quantifier(expr):
            vars += get_vars(expr)
            expr = expr.body()

        elif is_not(expr):
            vars += get_vars(child)
            expr = Not(child.body(), ctx=current_ctx)
        else:
            break
        child = expr.children()[0] if expr.children() else None
        expr = remove_dup_not(expr)

    return vars, expr


def remove_dup_not(expr):
    if not expr.children():
        return expr
    child = expr.children()[0]

    while is_not(expr) and is_not(child):
        expr = child.children()[0]
        if not expr.children():
            break
        child = expr.children()[0]
    return expr


def get_chc_body(clause):
    _, expr = get_vars_and_body(clause)
    child = expr.children()[0] if expr.children() else None
    body = expr

    if is_implies(expr):
        body = expr.children()[0]
    elif is_or(expr) or (is_not(expr) and is_and(child)):
        body_expr = []
        expr = child if is_not(expr) else expr
        for subexpr in expr.children():
            if not is_not(subexpr):
                # it is not necessary to take the negation of
                # and-subexpressions, since we are counting the
                # number of predicates
                body_expr.append(subexpr)
        body = Or(body_expr, current_ctx)
    elif (is_not(expr) and child.decl().kind() == Z3_OP_UNINTERPRETED) or \
            expr.decl().kind() == Z3_OP_UNINTERPRETED:
        body = None
    else:
        pass

    return body


def reverse_dict(initial_dict: dict):
    new_dict = defaultdict(set)
    for key in initial_dict:
        value = initial_dict[key]
        if isinstance(value, int):
            new_dict[value].add(key)
        else:
            for v in value:
                new_dict[v].add(key)
    return new_dict
