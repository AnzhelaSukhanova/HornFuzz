import random
import time
from enum import Enum

from utils import *

MUT_APPLY_TIME_LIMIT = 10


class MutType(Enum):
    ID = 1
    """And(a, b) -> And(b, a)"""
    SWAP_AND = 2
    """And(a, b) -> And(a, b, a)"""
    DUP_AND = 3
    """
    And(a, b, c) -> And(a, And(b, c))
    And(a, b) -> And(a, And(a, b))
    """
    BREAK_AND = 4

    SWAP_OR = 5
    DUP_OR = 6
    BREAK_OR = 7

    MIX_BOUND_VARS = 8


class MutGroup(Enum):
    AND = 1
    OR = 2
    QUANTIFIER = 3


class Mutation(object):

    def __init__(self):
        self.type_seq = []
        self.number = 0
        self.trans_n = 0
        self.trans_clause_ind = 0
        self.is_applied = False

    def cur_type(self):
        return self.type_seq[-1]

    def apply(self, instances):
        """Return mutated instances"""
        self.is_applied = False
        self.next_mutation(instances)
        cur_type = self.cur_type()
        if cur_type == MutType.ID:
            assert False, 'Failed to apply mutation'

        elif cur_type == MutType.SWAP_AND or cur_type == MutType.SWAP_OR or \
                cur_type == MutType.DUP_AND or cur_type == MutType.DUP_OR or \
                cur_type == MutType.BREAK_AND or cur_type == MutType.BREAK_OR or \
                cur_type == MutType.MIX_BOUND_VARS:
            mut_instances = self.transform_rand(instances)

        else:
            assert False
        self.is_applied = True
        return mut_instances

    def next_mutation(self, instance):
        """Return the next mutation based on the instance, type of the previous mutation etc"""
        self.number += 1
        is_there_and = False
        is_there_or = False
        is_there_quant = False
        for clause in instance:
            if is_quantifier(clause) and clause.is_forall():
                expr = clause.body()
                is_there_quant = True
            elif is_not(clause):
                child = clause.children()[0]
                if is_quantifier(child) and child.is_exists():
                    expr = child.body()
                    is_there_quant = True
                else:
                    expr = clause
            else:
                expr = clause

            is_there_and |= is_there_expr(expr, Z3_OP_AND)
            is_there_or |= is_there_expr(expr, Z3_OP_OR)
            is_there_quant |= is_there_expr(expr, Z3_QUANTIFIER_AST)
        if is_there_and and is_there_or:
            value = random.randint(2, 7)
        elif is_there_and:
            value = random.randint(2, 4)
        elif is_there_or:
            value = random.randint(5, 7)
        else:
            value = 1
        if is_there_quant:
            value = random.choice([value, 8]) if value > 1 else 8
        next_type = MutType(value)
        self.type_seq.append(next_type)

    def transform_rand(self, instance):
        """Transform random and/or-expression"""
        mut_instance = []
        mut_group = MutGroup.AND
        cur_type = self.cur_type()
        if cur_type == MutType.SWAP_AND or \
                cur_type == MutType.DUP_AND or \
                cur_type == MutType.BREAK_AND:
            kind = Z3_OP_AND
        elif cur_type == MutType.MIX_BOUND_VARS:
            kind = Z3_QUANTIFIER_AST
            mut_group = MutGroup.QUANTIFIER
        else:
            kind = Z3_OP_OR
            mut_group = MutGroup.OR

        clause_num = len(instance)
        ind = [i for i in range(clause_num)]
        i = random.choice(ind)
        while not is_there_expr(instance[i], kind):
            ind.remove(i)
            i = random.choice(ind)
        clause = instance[i]

        num = count_expr(clause, kind)
        self.trans_n = random.randint(1, num)
        mut_clause = self.transform_nth(clause, mut_group, time.perf_counter())
        self.trans_clause_ind = i
        for j, clause in enumerate(instance):
            if j == i:
                mut_instance.append(mut_clause)
            else:
                mut_instance.append(instance[j])
        # print(instance[self.trans_clause_ind], '\n->\n', mut_instance[self.trans_clause_ind])
        return mut_instance

    def transform_nth(self, expr, mut_group, st_time):
        """Transform nth and/or-expression in dfs-order"""
        if time.perf_counter() - st_time >= MUT_APPLY_TIME_LIMIT:
            raise TimeoutError('Timeout of applying mutation')
        if len(expr.children()) == 0:
            return expr
        mut_children = []
        for child in expr.children():
            mut_children.append(self.transform_nth(child, mut_group, st_time))
        cur_type = self.cur_type()
        is_and_expr = mut_group == MutGroup.AND and is_and(expr)
        is_or_expr = mut_group == MutGroup.OR and is_or(expr)
        is_quant_expr = mut_group == MutGroup.QUANTIFIER and is_quantifier(expr)
        if is_and_expr or is_or_expr or is_quant_expr:
            self.trans_n -= 1
            if self.trans_n == 0:
                if cur_type == MutType.SWAP_AND or cur_type == MutType.SWAP_OR:
                    mut_children = mut_children[1:] + mut_children[:1]
                elif cur_type == MutType.DUP_AND or cur_type == MutType.DUP_OR:
                    mut_children.append(mut_children[0])
                elif cur_type == MutType.BREAK_AND or cur_type == MutType.BREAK_OR:
                    if len(mut_children) == 2:
                        mut_children.pop()
                        mut_children.append(expr)
                    else:
                        subchildren = mut_children[-2:]
                        mut_children = mut_children[:-2]
                        if is_and_expr:
                            mut_children.append(And(subchildren))
                        else:
                            mut_children.append(Or(subchildren))
                if is_and_expr:
                    mut_expr = And(mut_children)
                elif is_or_expr:
                    mut_expr = Or(mut_children)
                else:
                    vars = get_bound_vars(expr)
                    random.shuffle(vars)
                    mut_expr = update_expr(expr, mut_children, vars)
                return mut_expr
        return update_expr(expr, mut_children)

    def get_chain(self):
        """Return the full mutation chain."""
        chain = ''
        for i in range(self.number - 1):
            chain += self.type_seq[i].name
            chain += '->'
        chain += self.type_seq[self.number - 1].name
        return chain
