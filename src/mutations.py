import random
from enum import Enum


class MutType(Enum):
    # no mutations yet
    ID = 1
    #TODO


class Mutation(object):

    def __init__(self):
        self.type = list()
        self.number = 0
        self.is_final = False

    def apply(self, seeds):
        """Return mutated seeds"""
        self.next_mutation(seeds)
        if self.type[-1] == 1:
            self.is_final = True
            return seeds
        else:
            #TODO
            return seeds

    def next_mutation(self, seeds):
        """Return the next mutation based on the seeds, type of the previous mutation etc"""
        # the choice of the next mutation is random yet
        self.number += 1
        next_type = random.randint(1, len(MutType))
        self.type.append(next_type)

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
