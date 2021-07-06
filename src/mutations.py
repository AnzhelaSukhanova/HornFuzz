import random
from enum import Enum
from z3 import *


class MutType(Enum):
    # no mutations yet
    ID = 1
    CONNECT = 2
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
        if cur_type == 1:
            self.is_final = True
            return seeds
        elif cur_type == 2:
            self.is_final = True
            return self.connect_chc(seeds)
        else:
            #TODO
            assert False

    def next_mutation(self, seeds):
        """Return the next mutation based on the seeds, type of the previous mutation etc"""
        self.number += 1
        if len(seeds) > 1:
            self.type.append(2)
        else:
            # the choice of the next mutation is random yet
            next_type = random.randint(1, len(MutType))
            self.type.append(next_type)

    def connect_chc(self, seeds):
        """Return connected seeds if they don't depend on each other"""
        vars = dict()
        mut_seeds = AstVector()
        can_be_conn = True

        for i, seed in enumerate(seeds):
            vars.update({i: set()})
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

    def print_chain(self, fr, to):
        """
        Return the mutation chain that caused the satisfiability mismatch.
        Highlight the mutation on which the mismatch occurs.
        """
        print('[', end='')
        for i in range(to):
            if i == fr:
                print(MutType(self.type[i]).name + ']', end='')
            else:
                print(MutType(self.type[i]).name, end='')
            if i is not to - 1:
                print('->')
            else:
                print()
