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
        self.type = []
        self.number = 0
        self.is_final = False

    def apply(self, seeds):
        """Return mutated seeds"""
        self.next_mutation(seeds)
        cur_type = self.type[-1]
        if cur_type == MutType.ID:
            self.is_final = True
            return seeds
        elif cur_type == MutType.CONNECT:
            return self.connect_chc(seeds)
        elif cur_type == MutType.SWAP_AND:
            #TODO
            return seeds
        elif cur_type == MutType.SWAP_OR:
            #TODO
            return seeds
        else:
            #TODO
            assert False

    def next_mutation(self, seeds):
        """Return the next mutation based on the seeds, type of the previous mutation etc"""
        self.number += 1
        if len(seeds) > 1:
            self.type.append(MutType.CONNECT)
        else:
            # the choice of the next mutation is random yet
            value = random.randint(1, len(MutType))
            next_type = MutType(value)
            self.type.append(next_type)

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
            print(self.type[i].name, end='')
            if i is not mut_num - 1:
                print('->', end='')
            else:
                print()
