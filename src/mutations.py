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


class Mutation(object):

    def __init__(self):
        self.type_seq = []
        self.number = 0
        self.trans_n = 0
        self.trans_clause_ind = 0

    def cur_type(self):
        return self.type_seq[-1]

    def apply(self, instance):
        """Return mutated instances."""
        self.next_mutation(instance.chc, instance.info)
        cur_type = self.cur_type()
        if cur_type == MutType.ID:
            assert False, 'Failed to apply mutation'

        elif cur_type in {MutType.SWAP_AND, MutType.SWAP_OR,
                          MutType.DUP_AND, MutType.DUP_OR,
                          MutType.BREAK_AND, MutType.BREAK_OR,
                          MutType.MIX_BOUND_VARS}:
            mut_instances = self.transform_rand(instance.chc, instance.info)

        else:
            assert False
        return mut_instances

    def next_mutation(self, instance, info):
        """
        Return the next mutation based on the instance,
        type of the previous mutation etc.
        """
        self.number += 1
        if self.number == 1:
            for clause in instance:
                info.expr_exists[Z3_OP_AND] |= expr_exists(clause, Z3_OP_AND)
                info.expr_exists[Z3_OP_OR] |= expr_exists(clause, Z3_OP_OR)
                info.expr_exists[Z3_QUANTIFIER_AST] |= \
                    expr_exists(clause, Z3_QUANTIFIER_AST)
        if info.expr_exists[Z3_OP_AND] and info.expr_exists[Z3_OP_OR]:
            value = random.randint(2, 7)
        elif info.expr_exists[Z3_OP_AND]:
            value = random.randint(2, 4)
        elif info.expr_exists[Z3_OP_OR]:
            value = random.randint(5, 7)
        else:
            value = 1
        if info.expr_exists[Z3_QUANTIFIER_AST]:
            value = random.choice([value, 8]) if value > 1 else 8
        next_type = MutType(value)
        self.type_seq.append(next_type)

    def transform_rand(self, instance, info):
        """Transform random and/or-expression."""
        mut_instance = []
        kinds = {0: Z3_OP_AND, 1: Z3_OP_OR, 2: Z3_QUANTIFIER_AST}
        cur_type = self.cur_type()
        if cur_type == MutType.SWAP_AND or \
                cur_type == MutType.DUP_AND or \
                cur_type == MutType.BREAK_AND:
            kind_ind = 0
        elif cur_type == MutType.MIX_BOUND_VARS:
            kind_ind = 2
        else:
            kind_ind = 1
        kind = kinds[kind_ind]

        clause_num = len(instance)
        if self.number == 1:
            for j in range(3):
                if info.expr_exists[kinds[j]]:
                    for i in range(clause_num):
                        if expr_exists(instance[i], kinds[j]):
                            info.expr_num[j][i] += \
                                count_expr(instance[i], kinds[j])

        ind = np.where(info.expr_num[kind_ind] != 0)[0]
        i = int(random.choice(ind))
        if cur_type == MutType.BREAK_AND or cur_type == MutType.BREAK_OR:
            info.expr_num[kind_ind][i] += 1
        clause = instance[i]
        num = info.expr_num[kind_ind][i]
        self.trans_n = random.randint(1, num)
        mut_clause = self.transform_nth(clause, kind, time.perf_counter())
        self.trans_clause_ind = i
        for j, clause in enumerate(instance):
            if j == i:
                mut_instance.append(mut_clause)
            else:
                mut_instance.append(instance[j])
        # print(instance[self.trans_clause_ind], '\n->\n',
        #       mut_instance[self.trans_clause_ind])
        return mut_instance

    def transform_nth(self, expr, expr_kind, st_time):
        """Transform nth and/or-expression in dfs-order."""
        if time.perf_counter() - st_time >= MUT_APPLY_TIME_LIMIT:
            raise TimeoutError('Timeout of applying mutation')
        if len(expr.children()) == 0:
            return expr
        mut_children = []
        for child in expr.children():
            mut_children.append(self.transform_nth(child, expr_kind, st_time))
        cur_type = self.cur_type()
        is_and_expr = expr_kind == Z3_OP_AND and is_and(expr)
        is_or_expr = expr_kind == Z3_OP_OR and is_or(expr)
        is_quant_expr = expr_kind == Z3_QUANTIFIER_AST and is_quantifier(expr)
        if is_and_expr or is_or_expr or is_quant_expr:
            self.trans_n -= 1
            if self.trans_n == 0:
                if cur_type == MutType.SWAP_AND or cur_type == MutType.SWAP_OR:
                    mut_children = mut_children[1:] + mut_children[:1]
                elif cur_type == MutType.DUP_AND or cur_type == MutType.DUP_OR:
                    mut_children.append(mut_children[0])
                elif cur_type == MutType.BREAK_AND or \
                        cur_type == MutType.BREAK_OR:
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
