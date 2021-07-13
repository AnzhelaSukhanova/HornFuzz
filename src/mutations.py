import random
from enum import Enum
from collections import defaultdict
from z3 import *


class MutType(Enum):
    # no mutations yet
    ID = 1
    CONNECT = 2
    SWAP_AND = 3
    SWAP_OR = 4
    DUPL_AND = 5
    DUPL_OR = 6
    #TODO


class Mutation(object):

    def __init__(self):
        self.type_seq = []
        self.number = 0
        self.is_final = False

    def cur_type(self):
        return self.type_seq[-1]

    def apply(self, seeds):
        """Return mutated seeds"""
        self.next_mutation(seeds)
        cur_type = self.cur_type()
        if cur_type == MutType.ID:
            self.is_final = True
            return seeds

        elif cur_type == MutType.CONNECT:
            return self.connect_chc(seeds)

        elif cur_type == MutType.SWAP_AND or cur_type == MutType.SWAP_OR or \
                cur_type == MutType.DUPL_AND or cur_type == MutType.DUPL_OR:
            return self.transform_rand(seeds[0])

        else:
            assert False

    def next_mutation(self, seeds):
        """Return the next mutation based on the seeds, type of the previous mutation etc"""
        self.number += 1
        if len(seeds) > 1:
            self.type_seq.append(MutType.CONNECT)
        else:
            # the choice of the next mutation is random yet
            value = random.randint(1, len(MutType))
            next_type = MutType(value)
            self.type_seq.append(next_type)

    def transform_rand(self, seed):
        """Transform random and/or-expression"""
        mut_seed = []
        num = 0

        for clause in seed:
            expr = clause.body()
            cur_type = self.cur_type()
            if cur_type == MutType.SWAP_AND or cur_type == MutType.DUPL_AND:
                num += count_expr(expr, Z3_OP_AND)
            else:
                num += count_expr(expr, Z3_OP_OR)
        if num > 0:
            app_num = random.randint(1, num)

        for clause in seed:
            vars = get_bound_vars(clause)
            is_forall = False
            if is_quantifier(clause) and clause.is_forall():
                is_forall = True
                expr = clause.body()
            elif is_not(clause):
                child = clause.children()[0]
                if is_quantifier(child) and child.is_exists():
                    expr = child.body()
                else:
                    assert False, 'Invalid input (not CHC): ' + clause.sexpr()
            else:
                assert False, 'Invalid input (not CHC): ' + clause.sexpr()

            if num > 0:
                mut_body = self.transform_nth(expr, app_num)
                if is_forall:
                    mut_clause = ForAll(vars, mut_body)
                else:
                    mut_clause = Not(Exists(vars, mut_body))
            else:
                mut_clause = clause
            mut_seed.append(mut_clause)
        return mut_seed

    def transform_nth(self, expr, n):
        """Transform nth and/or-expression in dfs-order"""
        if len(expr.children()) == 0:
            return expr
        children = []
        for child in expr.children():
            mut_child = self.transform_nth(child, n)
            cur_type = self.cur_type()
            is_and_expr = (cur_type == MutType.SWAP_AND or cur_type == MutType.DUPL_AND) and is_and(mut_child)
            is_or_expr = (cur_type == MutType.SWAP_OR or cur_type == MutType.DUPL_OR) and is_or(mut_child)
            if is_and_expr or is_or_expr:
                n -= 1
                if n == 0:
                    subexpr = mut_child.children()
                    if cur_type == MutType.SWAP_AND or cur_type == MutType.SWAP_OR:
                        subexpr = subexpr[1:] + subexpr[:1]
                    elif cur_type == MutType.DUPL_AND or cur_type == MutType.DUPL_OR:
                        subexpr.append(subexpr[0])
                    if is_and_expr:
                        mut_child = And(subexpr)
                    else:
                        mut_child = Or(subexpr)
            children.append(mut_child)
        return update_expr(expr, children)

    def connect_chc(self, seeds):
        """Return connected seeds if they don't depend on each other"""
        vars = defaultdict(set)
        mut_seeds = AstVector()
        can_be_conn = True

        if len(seeds) == 1:
            return seeds
        for i, seed in enumerate(seeds):
            clause = seed[0]
            for j in range(clause.num_vars()):
                var = clause.var_name(j)
                vars[i].add(var)

            for j in range(i):
                if not vars[i].isdisjoint(vars[j]):
                    can_be_conn = False
                    break
                # TODO
            if not can_be_conn:
                mut_seeds = seeds
                break
            else:
                for clause in seed:
                    mut_seeds.push(clause)
        return mut_seeds

    def print_chain(self, mut_num):
        """Return the mutation chain that caused the satisfiability mismatch."""
        for i in range(mut_num):
            print(self.type_seq[i].name, end='')
            if i is not mut_num - 1:
                print('->', end='')
            else:
                print()


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
    for i in range(len(children)):
        upd_expr = substitute(upd_expr, (upd_expr.children()[i], children[i]))
    return upd_expr


def count_expr(expr, kind):
    """Return the number of subexpressions of the specific kind"""

    if is_var(expr) or is_const(expr):
        return 0
    num = 1 if expr.decl().kind() == kind else 0
    for child in expr.children():
        num += count_expr(child, kind)
    return num
