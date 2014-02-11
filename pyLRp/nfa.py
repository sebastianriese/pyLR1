
from .dfa import DFAState, LexingDFA
from .lexactions import GetMatch
from .alphabet import Epsilon

class NFAState(object):

    def __init__(self):
        self._transitions = {}
        self.action = None
        self.priority = None
        self._closure = None

    def __iter__(self):
        return iter(self._transitions.items())

    def move(self, char):
        """
        Get the set of states reached by the transition on char.
        """
        return self._transitions.get(char, frozenset())

    def traverse(self, f):
        """
        Do a depth-first, in-order search through the NFA.
        """
        self._traverse(f, set())

    def _traverse(self, f, visited):
        if self in visited:
            return

        visited.add(self)
        for cond, nodes in self._transitions.items():
            for node in nodes:
                f(self, cond, node)
                node._traverse(f, visited)

    def map_labels(self, f):
        """
        Create a structure equivalent NFA with mapped edge labels.
        ``f`` maps each original label to an iterable of new labels.
        """
        root_node = NFAState()
        root_node.action = self.action
        root_node.priority = self.priority
        node_map = {self: root_node}

        def traverse_function(from_, cond, to):
            # map the symbol by the mapper, preserving epsilon
            # transitions
            mapped_symbol = f(cond) if cond != Epsilon() else [Epsilon()]

            # from node is guaranteed to be there, as
            # we traverse in-order
            from_node = node_map[from_]

            if to not in node_map:
                to_node = NFAState()
                to_node.action = to.action
                to_node.priority = to.priority
                node_map[to] = to_node
            else:
                to_node = node_map[to]

            from_node.add_transitions(mapped_symbol, to_node)

        self.traverse(traverse_function)

        return root_node

    def epsilon_closure(self, visited=None):
        """
        Return the epsilon closure of the state.

        CAVEAT: The epsilon closure is cached. Therefore this must not
        be called before the NFA is fully constructed. Adding any
        non-epsilon transitions or inbound epsilon from another NFA to
        the NFA reachable when the epsilon closure was constructed is
        safe. Adding epsilon transitions from the reachable NFA will
        cause trouble.

        TODO: calculate the epsilon closures once and efficiently (for
        example by using a typical iterative algorithm).
        """

        if self._closure is not None:
            return self._closure

        closure = set([self])

        if visited is None:
            visited = frozenset()

        if self in visited:
            return closure

        closure |= self._transitions.get(Epsilon(), set())

        nc = set(closure)
        for elem in closure:
            nc |= elem.epsilon_closure(visited | frozenset([self]))
        nc = frozenset(nc)

        if not visited:
            self._closure = nc

        return nc

    def add_transitions(self, chrs, state):
        """
        Add transitions on all elements of the iterable `chrs` to
        `state`.
        """
        for chr in chrs:
            self.add_transition(chr, state)

    def add_epsilon_transition(self, state):
        self.add_transition(Epsilon(), state)

    def add_transition(self, char, state):
        """
        Add a transition of `char` to `state.
        """
        if char not in self._transitions:
            self._transitions[char] = set()

        self._transitions[char].add(state)


class LexingNFA(object):

    def __init__(self, lexing_rules, condition, alphabetizer,
                 inline_token_NFA, logger):
        """
        A NFA annotated with actions and with rules selected according
        to `condition`.
        """
        self._logger = logger
        self._start = NFAState()
        self._alphabetizer = alphabetizer

        # XXX: move the selection and NFA assembly code to an
        # appropriate place
        if condition.includes_s_token:
            self._start.add_epsilon_transition(inline_token_NFA)

        self.nullmatch = False
        if condition.nullmatch:
            self.nullmatch = True

        i = -1
        for lexing_rule in lexing_rules:
            if condition.match(lexing_rule.conditions):
                start, end = lexing_rule.regex.NFA()

                self._start.add_epsilon_transition(start)
                end.priority = i
                end.action = lexing_rule.action
            i -= 1

        self._start = alphabetizer.alphabetize(self._start)

    def create_DFA(self):
        """
        Create a DFA from the NFA.
        """

        def select_action(nfa_states):
            curpri = float('-inf')
            curaction = None
            for state in nfa_states:
                pri = state.priority
                if pri is not None and pri > curpri:
                    curaction = state.action
                    curpri = pri
            return curaction

        si = frozenset(self._start.epsilon_closure())
        dfa_states = {si: DFAState()}
        todo = [si]

        # XXX: add feature to warn when there are nullmatches possible
        # but they are ignored (?)
        if self.nullmatch:
            dfa_states[si].action = select_action(si)

        alphabet = self._alphabetizer.alphabet
        while todo:
            cur = todo.pop()
            for char in alphabet:
                move = set()
                for c in cur:
                    for m in c.move(char):
                        move |= m.epsilon_closure()
                new_state = frozenset(move)

                if new_state not in dfa_states:
                    todo.append(new_state)
                    dfa_states[new_state] = DFAState()
                    dfa_states[new_state].action = select_action(new_state)
                    if not new_state:
                        # this is the error state (empty set of NFA states)
                        # if we get here nothing can match anymore, therefore
                        # we can retrieve our longest match
                        dfa_states[new_state].action = GetMatch()

                dfa_states[cur].add_transition(dfa_states[new_state])

        return LexingDFA(dfa_states[si], dfa_states.values(),
                         self._alphabetizer)
