
from collections import deque

from .lextable import Lextable

class DFAState(object):

    def __init__(self):
        self._transitions = []
        self.action = None
        self.number = None

    def __iter__(self):
        return iter(self._transitions)

    def move(self, chr):
        """
        Get the transition on character for a DFA.
        """
        return self._transitions[ord(chr)]

    def move_numeric(self, num):
        return self._transitions[num]

    def add_transition(self, state):
        self._transitions.append(state)


class OptimizerPartition(object):
    def __init__(self):
        self._groups = []
        self._forward = {}

    def __len__(self):
        return len(self._groups)

    def new_group(self):
        num = len(self._groups)
        self._groups.append([])
        return num

    def group_of_state(self, state):
        return self._forward[state]

    def add(self, group, state):
        self._forward[state] = group
        self._groups[group].append(state)

    def generate_partition_transition_table(self, state):
        # efficiency hack for:
        # return tuple(self.group_of_state(target) for target in state)
        return tuple(map(self._forward.__getitem__, state))

    def partition(self):
        partition = OptimizerPartition()
        for group in self._groups:
            patterns = {}
            for entry in group:
                pattern = self.generate_partition_transition_table(entry)

                if pattern not in patterns:
                    patterns[pattern] = partition.new_group()

                partition.add(patterns[pattern], entry)

        if len(partition) == len(self):
            return self
        else:
            return partition.partition()

    def reconstruct(self, start):
        newstates = []
        newstart = None

        # create the new states
        for group in self._groups:
            newstates.append(DFAState())

            if start in group:
                newstart = newstates[-1]

        # link the new states
        for newstate, group in zip(newstates, self._groups):
            representative = group[0]
            newstate.action = representative.action
            for target in representative:
                newstate.add_transition(newstates[self.group_of_state(target)])

        return newstart, newstates

class LexingDFA(object):

    def __init__(self, start, states, alphabetizer):
        self.start = start
        self.states = list(states)
        self._alphabetizer = alphabetizer

    def optimize(self):
        # construct the initial partition
        partition = OptimizerPartition()
        actions   = {}

        for state in self.states:
            if state.action not in actions:
                actions[state.action] = partition.new_group()

            partition.add(actions[state.action], state)

        # run the optimizing algorithm
        partition = partition.partition()

        # construct a new DFA from the partition
        self.start, self.states = partition.reconstruct(self.start)

    def create_lex_table(self):
        """
        Create a numeric table representation of the DFA.
        """
        lextable = []
        actions = []

        queue = deque([self.start])
        self.start.number = 0
        cnt = 1

        while queue:
            cur = queue.pop()
            assert cur.number == len(lextable)
            newline = []
            for target in cur:
                if target.number is None:
                    queue.appendleft(target)
                    target.number = cnt
                    cnt += 1
                newline.append(target.number)
            actions.append(cur.action)
            lextable.append(newline)

        return Lextable(lextable, self.start.number, actions,
                        self._alphabetizer)
