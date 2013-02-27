
from collections import deque

from .lextable import Lextable

class DFAState(object):

    def __init__(self):
        self.transitions = []
        self.action = None
        self.number = None

    def __iter__(self):
        return iter(self.transitions)

    def Move(self, chr):
        """
        Get the transition on character for a DFA.
        """
        return self.transitions[ord(chr)]

    def MoveNumeric(self, num):
        return self.transitions[num]

    def AddTransition(self, state):
        self.transitions.append(state)

    def SetAction(self, action):
        self.action = action

    def GetAction(self):
        return self.action


class OptimizerPartition(object):
    def __init__(self):
        self.groups = []
        self.forward = {}

    def __len__(self):
        return len(self.groups)

    def NewGroup(self):
        num = len(self.groups)
        self.groups.append([])
        return num

    def GroupOfState(self, state):
        return self.forward[state]

    def Add(self, group, state):
        self.forward[state] = group
        self.groups[group].append(state)

    def GeneratePartitionTransitionTable(self, state):
        # efficiency hack for:
        # return tuple(self.GroupOfState(target) for target in state)
        return tuple(map(self.forward.__getitem__, state))

    def Partition(self):
        partition = OptimizerPartition()
        for group in self.groups:
            patterns = {}
            for entry in group:
                pattern = self.GeneratePartitionTransitionTable(entry)

                if pattern not in patterns:
                    patterns[pattern] = partition.NewGroup()

                partition.Add(patterns[pattern], entry)

        if len(partition) == len(self):
            return self
        else:
            return partition.Partition()

    def Reconstruct(self, start):
        newstates = []
        newstart = None

        # create the new states
        for group in self.groups:
            newstates.append(DFAState())

            if start in group:
                newstart = newstates[-1]

        # link the new states
        for newstate, group in zip(newstates, self.groups):
            representative = group[0]
            newstate.SetAction(representative.GetAction())
            for target in representative:
                newstate.AddTransition(newstates[self.GroupOfState(target)])

        return newstart, newstates

class LexingDFA(object):

    def __init__(self, start, states):
        self.start = start
        self.states = list(states)

    def Optimize(self):
        # construct the initial partition
        partition = OptimizerPartition()
        actions   = {}

        for state in self.states:
            if state.action not in actions:
                actions[state.action] = partition.NewGroup()

            partition.Add(actions[state.action], state)

        # run the optimizing algorithm
        partition = partition.Partition()

        # construct a new DFA from the partition
        self.start, self.states = partition.Reconstruct(self.start)

    def CreateLexTable(self):
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
            actions.append(cur.GetAction())
            lextable.append(newline)

        return Lextable(lextable, self.start.number, actions)
