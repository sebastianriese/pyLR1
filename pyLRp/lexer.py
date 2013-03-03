
from .nfa import *
from .lexactions import Token

class LexingRule(object):

    def __init__(self, conditions, regex, action):
        self.conditions = conditions
        self.regex = regex
        self.action = action

    def Regex(self):
        return self.regex

    def Action(self):
        return self.action

    def Conditions(self):
        return self.conditions



class InitialCondition(object):
    def __init__(self, name, number):
        self.name = name
        self.number = number
        self.nullmatch = False

    def IncludesSToken(self): return False

    def Nullmatch(self):
        return self.nullmatch

    def DeclareNullmatch(self):
        self.nullmatch = True

    def Match(self, conditions):
        raise NotImplementedError()

    def Name(self):
        return self.name

    def Number(self):
        return self.number

class InclusiveInitialCondition(InitialCondition):
    def IncludesSToken(self): return True

    def __init__(self, name, number, *conditions):
        super().__init__(name, number)
        self.conditions = conditions

    def Match(self, conditions):
        if not conditions or \
                self in conditions or \
                any(cond.Match(conditions) for cond in self.conditions):
            return True
        return False

class ExclusiveInitialCondition(InitialCondition):

    def Match(self, conditions):
        if self in conditions:
            return True
        return False


class LexerConstructor(object):
    """
    Manages the steps of constructing the lexer, taking care of
    constructing the lextables for the different states and then
    applying the further manipulations to all of them.
    """

    def __init__(self, lexerSpec, logger):
        self.logger = logger

        # sort initial conditions by number to create a reference
        # order for the other item lists
        self.initial_conditions = list(sorted(lexerSpec.InitialConditions(),
                                              key=lambda x: x.Number()))
        self.nfas = []
        self.dfas = []
        self.lextables = []
        self.mapping = False

        # construct the automaton for matching the inline tokens
        inlineTokens = NFAState()
        for token in lexerSpec.InlineTokens():

            previous = NFAState()
            inlineTokens.AddTransition('', previous)

            for char in token:
                new = NFAState()
                previous.AddTransition(char, new)
                previous = new

            previous.SetAction(0, Token('"' + token + '"'))

        # construct the NFAs for the initial conditions
        for condition in self.initial_conditions:
            self.nfas.append(LexingNFA(lexerSpec.Lexer(),
                                       condition,
                                       inlineTokens,
                                       logger))

    def ConstructDFAs(self):
        self.dfas = []
        for nfa in self.nfas:
            self.dfas.append(nfa.CreateDFA())

    def DropNFA(self):
        """
        Drop the nfas if they are no longer needed to spare memory
        """
        self.nfas = None


    def Optimize(self):
        for dfa in self.dfas:
            dfa.optimize()

    def CreateLexTables(self):
        self.lextables = []
        for dfa in self.dfas:
            self.lextables.append(dfa.create_lex_table())

    def DropDFA(self):
        """
        Drop the dfas if they are no longer needed to spare memory
        """
        self.dfas = None

    def ConstructEquivalenceClasses(self):
        self.mapping = True
        for lextable in self.lextables:
            lextable.ConstructEquivalenceClasses()

    def Mapping(self):
        return self.mapping

    def Get(self):
        for cond, lextable in zip(self.initial_conditions, self.lextables):
            yield tuple([cond] + list(lextable.Get()))

    def PrintTables(self):
        for key, table in self.lextables.items():
            print("-----------------", key.Name(), "--------------------")
            table.Print()

