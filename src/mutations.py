import random
from enum import Enum
from collections import defaultdict
from z3 import *


class MutType(Enum):
    ID = 1
    """And(a, b) -> And(b, a)"""
    SWAP_AND = 2
    """And(a, b) -> And(a, b, a)"""
    DUPL_AND = 3
    """
    And(a, b, c) -> And(a, And(b, c))
    And(a, b) -> And(a, And(a, b))
    """
    BREAK_AND = 4

    SWAP_OR = 5
    DUPL_OR = 6
    BREAK_OR = 7

    # TODO
    # CONNECT = 8


class Mutation(object):

    def __init__(self):
        self.type_seq = []
        self.number = 0
        self.is_final = False
        self.and_num = 0
        self.or_num = 0
        self.trans_n = 0

    def cur_type(self):
        return self.type_seq[-1]

    def apply(self, examples):
        """Return mutated examples"""
        self.next_mutation(examples)
        cur_type = self.cur_type()
        if cur_type == MutType.ID:
            self.is_final = True
            return examples

        elif cur_type == MutType.SWAP_AND or cur_type == MutType.SWAP_OR or \
                cur_type == MutType.DUPL_AND or cur_type == MutType.DUPL_OR or \
                cur_type == MutType.BREAK_AND or cur_type == MutType.BREAK_OR:
            return self.transform_rand(examples)

        # TODO
        # elif cur_type == MutType.CONNECT:
        #     return self.connect_chc(examples)

        else:
            assert False

    def next_mutation(self, example):
        """Return the next mutation based on the example, type of the previous mutation etc"""
        self.number += 1
        self.and_num = self.or_num = 0
        for clause in example:
            if is_quantifier(clause) and clause.is_forall():
                expr = clause.body()
            elif is_not(clause):
                child = clause.children()[0]
                if is_quantifier(child) and child.is_exists():
                    expr = child.body()
                else:
                    assert False, 'Invalid input (not CHC): ' + clause.sexpr()
            else:
                assert False, 'Invalid input (not CHC): ' + clause.sexpr()

            self.and_num += count_expr(expr, Z3_OP_AND)
            self.or_num += count_expr(expr, Z3_OP_OR)
        if self.and_num > 0 and self.or_num > 0:
            value = random.randint(2, len(MutType))
        elif self.and_num > 0:
            value = random.randint(2, 4)
        elif self.or_num > 0:
            value = random.randint(5, len(MutType))
        else:
            value = 1
        next_type = MutType(value)
        self.type_seq.append(next_type)

    def transform_rand(self, example):
        """Transform random and/or-expression"""
        mut_example = []
        is_and_mut = False
        cur_type = self.cur_type()
        if cur_type == MutType.SWAP_AND or \
                cur_type == MutType.DUPL_AND or \
                cur_type == MutType.BREAK_AND:
            is_and_mut = True
            num = self.and_num
        else:
            num = self.or_num
        if num > 0:
            self.trans_n = random.randint(1, num)

        for clause in example:
            vars = get_bound_vars(clause)
            is_forall = False
            if is_quantifier(clause):
                is_forall = True
                expr = clause.body()
            else:
                child = clause.children()[0]
                expr = child.body()

            if num > 0:
                mut_body = self.transform_nth(expr, is_and_mut)
                if is_forall:
                    mut_clause = ForAll(vars, mut_body)
                else:
                    mut_clause = Not(Exists(vars, mut_body))
            else:
                mut_clause = clause
            mut_example.append(mut_clause)
        return mut_example

    def transform_nth(self, expr, is_and_mut):
        """Transform nth and/or-expression in dfs-order"""
        if len(expr.children()) == 0:
            return expr
        children = []
        for child in expr.children():
            mut_child = self.transform_nth(child, is_and_mut)
            cur_type = self.cur_type()
            is_and_expr = is_and_mut and is_and(mut_child)
            is_or_expr = (not is_and_mut) and is_or(mut_child)
            if is_and_expr or is_or_expr:
                self.trans_n -= 1
                if self.trans_n == 0:
                    subexpr = mut_child.children()
                    if cur_type == MutType.SWAP_AND or cur_type == MutType.SWAP_OR:
                        subexpr = subexpr[1:] + subexpr[:1]
                    elif cur_type == MutType.DUPL_AND or cur_type == MutType.DUPL_OR:
                        subexpr.append(subexpr[0])
                    elif cur_type == MutType.BREAK_AND or cur_type == MutType.BREAK_OR:
                        if len(subexpr) == 2:
                            subexpr.pop()
                            subexpr.append(mut_child)
                        else:
                            subexpr_children = subexpr[-2:]
                            subexpr = subexpr[:-2]
                            if is_and_expr:
                                subexpr.append(And(subexpr_children))
                            else:
                                subexpr.append(Or(subexpr_children))
                    if is_and_expr:
                        mut_child = And(subexpr)
                    else:
                        mut_child = Or(subexpr)
            children.append(mut_child)
        return update_expr(expr, children)

    # TODO
    def connect_chc(self, examples):
        """Return connected examples if they don't depend on each other"""
        vars = defaultdict(set)
        mut_examples = AstVector()
        can_be_conn = True

        if len(examples) == 1:
            return examples
        for i, example in enumerate(examples):
            clause = example[0]
            for j in range(clause.num_vars()):
                var = clause.var_name(j)
                vars[i].add(var)

            for j in range(i):
                if not vars[i].isdisjoint(vars[j]):
                    can_be_conn = False
                    break
            if not can_be_conn:
                mut_examples = examples
                break
            else:
                for clause in example:
                    mut_examples.push(clause)
        return mut_examples

    def print_chain(self):
        """Return the mutation chain that caused the satisfiability mismatch."""
        for i in range(self.number - 1):
            print(self.type_seq[i].name, end='')
            print('->', end='')
        print(self.type_seq[self.number - 1].name)


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


def count_expr(expr, kind):
    """Return the number of subexpressions of the specific kind"""

    if is_var(expr) or is_const(expr):
        return 0
    num = 1 if expr.decl().kind() == kind else 0
    for child in expr.children():
        num += count_expr(child, kind)
    return num
