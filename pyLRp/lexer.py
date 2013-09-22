
from .nfa import *
from .lexactions import Token
from .alphabet import ByteAlphabet

class LexingRule(object):

    def __init__(self, conditions, regex, action):
        self._conditions = frozenset(conditions)
        self._regex = regex
        self._action = action

    @property
    def regex(self):
        return self._regex

    @property
    def action(self):
        return self._action

    @property
    def conditions(self):
        return self._conditions


class InitialCondition(object):
    def __init__(self, name, number):
        self._name = name
        self._number = number
        self._nullmatch = False

    @property
    def includes_s_token(self):
        return False

    @property
    def nullmatch(self):
        return self._nullmatch

    def declare_nullmatch(self):
        self._nullmatch = True

    def match(self, conditions):
        raise NotImplementedError()

    @property
    def name(self):
        return self._name

    @property
    def number(self):
        return self._number

class InclusiveInitialCondition(InitialCondition):

    def __init__(self, name, number, *included_conditions):
        super().__init__(name, number)
        self._included_conditions = included_conditions

    @property
    def includes_s_token(self):
        return True

    def match(self, conditions):
        if not conditions or \
                self in conditions or \
                any(cond.match(conditions)
                    for cond in self._included_conditions):
            return True
        return False

class ExclusiveInitialCondition(InitialCondition):

    def match(self, conditions):
        if self in conditions:
            return True
        return False


class LexerConstructor(object):
    """
    Manages the steps of constructing the lexer, taking care of
    constructing the lextables for the different states and then
    applying the further manipulations to all of them.
    """

    def __init__(self, lexer_spec, logger):
        self.logger = logger

        self._alphabet = ByteAlphabet()

        # sort initial conditions by number to create a reference
        # order for the other item lists
        self._initial_conditions = list(sorted(lexer_spec.initial_conditions.values(),
                                               key=lambda x: x.number))
        self._nfas = []
        self._dfas = []
        self._lextables = []
        self._mapping = False

        inline_tokens = self._make_inline_token_NFA(lexer_spec.inline_tokens())

        # construct the NFAs for the initial conditions
        for condition in self._initial_conditions:
            self._nfas.append(LexingNFA(lexer_spec,
                                        condition,
                                        inline_tokens,
                                        logger))

    def _make_inline_token_NFA(self, inline_token_list):
        inline_tokens = NFAState()
        for name, text in inline_token_list:

            previous = NFAState()
            inline_tokens.add_epsilon_transition(previous)

            for char in text:
                new = NFAState()
                previous.add_transition(char, new)
                previous = new

            previous.priority = 0
            previous.action = Token(name)

        return inline_tokens

    def construct_DFAs(self):
        self._dfas = []
        for nfa in self._nfas:
            self._dfas.append(nfa.create_DFA(self._alphabet))

    def drop_NFA(self):
        """
        Drop the nfas if they are no longer needed to spare memory
        """
        self._nfas = None


    def optimize(self):
        for dfa in self._dfas:
            dfa.optimize()

    def create_lex_tables(self):
        self._lextables = []
        for dfa in self._dfas:
            self._lextables.append(dfa.create_lex_table())

    def drop_DFA(self):
        """
        Drop the dfas if they are no longer needed to spare memory
        """
        self._dfas = None

    def construct_equivalence_classes(self):
        self._mapping = True
        for lextable in self._lextables:
            lextable.construct_equivalence_classes(self._alphabet)

    @property
    def mapping(self):
        return self._mapping

    def get(self):
        for cond, lextable in zip(self._initial_conditions, self._lextables):
            yield tuple([cond] + list(lextable.get()))

    def print_tables(self):
        for key, table in self._lextables.items():
            print("-----------------", key.Name(), "--------------------")
            table.print()

