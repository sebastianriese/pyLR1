
from .dfa import DFAState, LexingDFA
from .lexactions import GetMatch

class NFAState(object):

    def __init__(self):
        self.transitions = {}
        self.action = None
        self.priority = None
        self.closure = None

    def __iter__(self):
        return iter(self.transitions.items())

    def Move(self, char):
        """
        Get the set of states reached by the transition on char.
        """
        return self.transitions.get(char, set())

    def EpsilonClosure(self, visited=None):

        if self.closure is not None:
            return self.closure

        closure = set([self])

        if visited is None:
            visited = frozenset()

        if self in visited:
            return closure

        closure |= self.transitions.get('', set())

        nc = set(closure)
        for elem in closure:
            nc |= elem.EpsilonClosure(visited | frozenset([self]))

        if visited == frozenset():
            self.closure = frozenset(nc)

        return nc

    def AddTransitions(self, chrs, state):
        for chr in chrs:
            self.AddTransition(chr, state)

    def AddTransition(self, char, state):
        if char not in self.transitions:
            self.transitions[char] = set()

        self.transitions[char].add(state)

    def SetAction(self, priority, action):
        self.action = action
        self.priority = priority

    def GetAction(self):
        return self.action

    def Priority(self):
        return self.priority


class LexingNFA(object):

    def __init__(self, lexingRules, condition, inlineTokenNFA, logger):
        self.logger = logger
        self.start = NFAState()

        if condition.IncludesSToken():
            self.start.AddTransition('', inlineTokenNFA)

        self.nullmatch = False
        if condition.Nullmatch():
            self.nullmatch = True

        i = -1
        for lexingRule in lexingRules:
            if condition.Match(lexingRule.Conditions()):
                start, end = lexingRule.Regex().NFA()

                self.start.AddTransition('', start)
                end.SetAction(i, lexingRule.Action())
            i -= 1

    def CreateDFA(self):

        def SelectAction(nfaStates):
            curpri = float('-inf')
            curaction = None
            for state in nfaStates:
                pri = state.Priority()
                if pri is not None and pri > curpri:
                    curaction = state.GetAction()
                    curpri = pri
            return curaction

        si = frozenset(self.start.EpsilonClosure())
        dfaStates = {si : DFAState()}
        todo = [si]


        # XXX: add feature to warn when there are nullmatches
        # but they are ignored
        if self.nullmatch:
            dfaStates[si].action = SelectAction(si)

        while todo:
            cur = todo.pop()

            for i in range(0,256):
                char = chr(i)

                move = set()
                for c in cur:
                    for m in c.Move(char):
                        move |= m.EpsilonClosure()
                newState = frozenset(move)

                if newState not in dfaStates:

                    todo.append(newState)
                    dfaStates[newState] = DFAState()
                    dfaStates[newState].action = SelectAction(newState)

                    if len(newState) == 0:
                        # this is the error state (empty set of NFA states)
                        # if we get here nothing can match anymore, therefore
                        # we can retrieve our longest match
                        dfaStates[newState].action = GetMatch()

                dfaStates[cur].add_transition(dfaStates[newState])

        return LexingDFA(dfaStates[si], dfaStates.values())
