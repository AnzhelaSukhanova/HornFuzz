import random
from enum import Enum
from collections import defaultdict
from utils import *


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
        self.trans_n = 0
        self.trans_clause_ind = 0

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
        is_there_and = False
        is_there_or = False
        for clause in example:
            if is_quantifier(clause) and clause.is_forall():
                expr = clause.body()
            elif is_not(clause):
                child = clause.children()[0]
                if is_quantifier(child) and child.is_exists():
                    expr = child.body()
                else:
                    expr = clause
            else:
                expr = clause

            is_there_and |= is_there_expr(expr, Z3_OP_AND)
            is_there_or |= is_there_expr(expr, Z3_OP_OR)
        if is_there_and and is_there_or:
            value = random.randint(2, len(MutType))
        elif is_there_and:
            value = random.randint(2, 4)
        elif is_there_or:
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
            kind = Z3_OP_AND
        else:
            kind = Z3_OP_OR

        clause_num = len(example)
        ind = [i for i in range(clause_num)]
        i = random.choice(ind)
        while not is_there_expr(example[i], kind):
            ind.remove(i)
            i = random.choice(ind)
        clause = example[i]
        vars = get_bound_vars(clause)
        is_forall = False
        is_not_exists = False
        if is_quantifier(clause) and clause.is_forall():
            is_forall = True
            expr = clause.body()
        elif is_not(clause):
            child = clause.children()[0]
            if is_quantifier(child) and child.is_exists():
                is_not_exists = True
                child = clause.children()[0]
                expr = child.body()
            else:
                expr = clause
        else:
            expr = clause

        num = count_expr(expr, kind)
        self.trans_n = random.randint(1, num)
        mut_body = self.transform_nth(expr, is_and_mut)
        if is_forall:
            mut_clause = ForAll(vars, mut_body)
        elif is_not_exists:
            mut_clause = Not(Exists(vars, mut_body))
        else:
            mut_clause = update_expr(expr, mut_body)
        self.trans_clause_ind = i
        for j, clause in enumerate(example):
            if j == i:
                mut_example.append(mut_clause)
            else:
                mut_example.append(example[j])
        # print(example[self.trans_clause_ind], '\n->\n', mut_example[self.trans_clause_ind])
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

    def get_chain(self):
        """Return the full mutation chain."""
        chain = ''
        for i in range(self.number - 1):
            chain += self.type_seq[i].name
            chain += '->'
        chain += self.type_seq[self.number - 1].name
        return chain
