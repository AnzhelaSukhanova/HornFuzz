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

        elif cur_type == MutType.SWAP_AND or cur_type == MutType.SWAP_OR:
            return self.swap_subexpr(seeds[0])

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

    def swap_subexpr(self, seed):
        """Swap the subexpressions of the and/or-expression"""
        vars = get_bound_vars(seed)
        mut_seed = []

        for clause in seed:
            expr = clause.body()
            children = []
            for child in expr.children():
                is_and_expr = self.cur_type() == MutType.SWAP_AND and is_and(child)
                is_or_expr = self.cur_type() == MutType.SWAP_OR and is_or(child)
                if is_and_expr or is_or_expr:
                    subexpr = child.children()
                    subexpr = subexpr[1:] + subexpr[:1]
                    if is_and_expr:
                        children.append(And(subexpr))
                    else:
                        children.append(Or(subexpr))
                else:
                    children.append(child)
            if len(children) == 2:
                mut_body = Implies(children[0], children[1])
            else:
                mut_body = Not(children[0])
            mut_clause = ForAll(vars, mut_body)
            mut_seed.append(mut_clause)
        return mut_seed

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


def get_bound_vars(seed):
    """Return bound variables"""

    vars = set()
    for expr in seed:
        assert expr.is_forall() or expr.is_exists(), 'А quantifier-free expression is given'
        for i in range(expr.num_vars()):
            name = expr.var_name(i)
            sort = expr.var_sort(i)
            method_name = str(sort)
            if method_name[:5] == 'Array':
                constr = getattr(z3, 'Array')
                vars.add(constr(name, sort.domain(), sort.range()))
            else:
                constr = getattr(z3, method_name)
                vars.add(constr(name))
    return list(vars)
