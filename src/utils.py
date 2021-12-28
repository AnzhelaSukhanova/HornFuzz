import hashlib
import random
import traceback
from collections import defaultdict
from copy import deepcopy
from enum import Enum
from typing import List

import numpy as np
from scipy.sparse import dok_matrix
from from_z3 import *

TRACE_FILE = '.z3-trace'

trace_states = defaultdict(int)
trace_offset = 0
info_kinds = [Z3_OP_AND, Z3_OP_OR, Z3_QUANTIFIER_AST,
              Z3_OP_LE, Z3_OP_GE, Z3_OP_LT, Z3_OP_GT,
              Z3_OP_UNINTERPRETED, None]


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
        self.expr_exists = defaultdict(bool)
        self.is_expr_in_clause = np.zeros((len(info_kinds), number),
                                          dtype=bool)


class StatsType(Enum):
    DEFAULT = 0
    TRANSITIONS = 1
    STATES = 2
    ALL = 3


stats_type = StatsType.DEFAULT
with_difficulty_heur = False


def set_stats_type(heuristics: defaultdict):
    """Set the type of statistics based on heuristics."""
    global stats_type, with_difficulty_heur

    if heuristics['transitions'] and heuristics['states']:
        stats_type = StatsType.ALL
    elif heuristics['transitions']:
        stats_type = StatsType.TRANSITIONS
    elif heuristics['states']:
        stats_type = StatsType.STATES

    if heuristics['difficulty']:
        with_difficulty_heur = True


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


def mk_app_builders():
    builders = {}
    OP_PREFIX = 'Z3_OP_'
    for c in dir(z3consts):
        if not c.startswith(OP_PREFIX):
            continue
        kind_name = str(c).removeprefix('Z3_OP_').lower()
        kind_value = getattr(z3consts, c)
        mk_function = getattr(z3core, f'Z3_mk_{kind_name}', None)
        if mk_function is not None:
            builders[kind_value] = mk_function
    return builders


Z3_APP_BUILDERS = mk_app_builders()


def update_expr(expr, children, vars: list = None):
    """Return the expression with new children."""

    if not is_quantifier(expr):
        decl = expr.decl()
        kind = decl.kind()
        mk_function = Z3_APP_BUILDERS.get(kind)
        if mk_function is None:
            return expr

        ctx = expr.ctx
        ctx_ref = ctx.ref()
        cast_children = []
        for child in children:
            cast_children.append(coerce_exprs(child, ctx))
        ast_children = to_ast_list(cast_children)

        try:
            if kind in {Z3_OP_IMPLIES, Z3_OP_XOR, Z3_OP_ARRAY_EXT,
                        Z3_OP_SET_DIFFERENCE, Z3_OP_SET_SUBSET,
                        Z3_OP_GE, Z3_OP_GT, Z3_OP_LE, Z3_OP_LT,
                        Z3_OP_MOD, Z3_OP_DIV, Z3_OP_EQ, Z3_OP_POWER,
                        Z3_OP_SELECT}:
                upd_expr = mk_function(ctx_ref, ast_children[0],
                                       ast_children[1])

            elif kind in {Z3_OP_NOT, Z3_OP_TO_REAL, Z3_OP_TO_INT,
                          Z3_OP_IS_INT, Z3_OP_FPA_ABS, Z3_OP_FPA_ABS}:
                upd_expr = mk_function(ctx_ref, ast_children[0])

            elif kind in {Z3_OP_ITE}:
                upd_expr = mk_function(ctx_ref, ast_children[0], ast_children[1], ast_children[2])

            else:
                arity = len(children)
                upd_expr = mk_function(ctx_ref, arity, ast_children)

            upd_expr = to_expr_ref(upd_expr, ctx)

        except Exception:
            print(traceback.format_exc())
            print('Expression kind:', kind)
            return expr
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


def take_pred_from_clause(clause: AstVector, with_term=False):
    _, uninter_pred = count_expr(clause,
                                 [Z3_OP_UNINTERPRETED],
                                 is_unique=True)
    assert uninter_pred, "Uninterpreted predicate not found" + clause.sexpr()
    upred = random.sample(uninter_pred[0], 1)[0]


    vars = []
    for i in range(upred.arity()):
        sort = upred.domain(i)
        vars.append(FreshConst(sort, prefix='x'))
    upred_value = upred.__call__(vars)
    if with_term:
        return upred_value, vars, upred
    else:
        return upred_value, vars


def equivalence_check(seed: AstVector, mutant: AstVector, ctx: Context) -> bool:
    solver = Solver(ctx=ctx)

    for i, clause in enumerate(seed):
        solver.reset()
        mut_clause = mutant[i]
        expr = Xor(clause, mut_clause, ctx=ctx)
        solver.add(expr)
        result = solver.check()

        del expr
        if result != unsat:
            return False
    return True
