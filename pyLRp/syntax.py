"""
Representation of a grammar file
"""
from .symbol import *
from .lexer import *

class SyntaxNameError(Exception):
    pass

class ASTInformation(object):

    def set_used(self):
        """
        Call this method in the parser when there is a `%ast` section.
        """
        self.used_ = True

    @property
    def used(self):
        return self.used_

    def list(self, symbol):
        """
        Register a meta symbol for automatic list action creation.
        """
        self.lists.add(symbol)

    def bind(self, production, name):
        """
        Bind a production to a AST class name.
        """
        self.bindings[production] = name

    def __init__(self):
        """
        Automatic AST creation data.
        """
        self.used_  = False
        self.lists   = set()
        self.visitor = 'ASTVisitor'
        self.bindings = {}

class Syntax(object):

    TERMINAL = 0
    META = 1
    EOF = 2
    UNDEF = 3
    ERROR = 4


    class SymbolTableEntry(object):

        def __init__(self, symbol, symbol_number, symtype):
            self.symbol = symbol
            self.symbol_number = symbol_number
            self.symtype = symtype

        def SymType(self):
            return self.symtype

        def Symbol(self):
            return self.symbol

        def Number(self):
            return self.symbol_number

    def __init__(self):
        self.metacounter = 0
        self.termcounter = 0

        self.start = None
        self.symbols = {}
        self.lexer_defs = {}
        self.ast_info = ASTInformation()
        self.header = []
        self.footer = []
        self.lexer = []
        self.inline_tokens = set()

        self.initial_conditions = {}
        # the condition $INITIAL is the default condition
        # $SOL is the start of line condition
        # $SOF is the start of file condition
        initial = self.initial_conditions["$INITIAL"] = \
            InclusiveInitialCondition("$INITIAL", 0)
        sol = self.initial_conditions["$SOL"] = \
            InclusiveInitialCondition("$SOL", 1, initial)
        self.initial_conditions["$SOF"] = \
            InclusiveInitialCondition("$SOF", 2, sol)

        # require the error symbol
        self.RequireError()

    def InlineTokens(self):
        return self.inline_tokens

    def ASTInfo(self):
        return self.ast_info

    def Lexer(self):
        return self.lexer

    def Start(self):
        return self.start

    def SetStart(self, start):
        self.start = start

    def AddFooter(self, line):
        self.footer.append(line)

    def Footer(self):
        return self.footer

    def AddLexingRule(self, lexingrule):
        self.lexer.append(lexingrule)

    def AddInlineLexingRule(self, token):
        self.inline_tokens.add(token)

    def AddNamedPattern(self, name, regex):
        if name in self.lexer_defs:
            raise SyntaxNameError("Pattern name {} already in use".format(name))
        self.lexer_defs[name] = regex

    def NamedPatterns(self):
        return self.lexer_defs

    def InitialConditions(self):
        return self.initial_conditions.values()

    def InitialCondition(self, name):
        try:
            return self.initial_conditions[name]
        except KeyError:
            errmsg = "Initial condition {} not defined".format(name)
            raise SyntaxNameError(errmsg)

    def AddInclusiveInitialCondition(self, name):
        if name in self.initial_conditions:
            errmsg = "Initial condition name {} already in use".format(name)
            raise SyntaxNameError(errmsg)

        self.initial_conditions[name] = \
            InclusiveInitialCondition(name,
                                      len(self.initial_conditions),
                                      self.InitialCondition('$INITIAL'))

    def AddExclusiveInitialCondition(self, name):
        if name in self.initial_conditions:
            errmsg = "Initial condition name {} already in use".format(name)
            raise SyntaxNameError(errmsg)

        self.initial_conditions[name] = \
            ExclusiveInitialCondition(name, len(self.initial_conditions))

    def RequireEOF(self):
        if "$EOF" not in self.symbols:
            self.symbols['$EOF'] = \
                Syntax.SymbolTableEntry(EOF(), self.termcounter, self.EOF)
            self.termcounter += 1

        return self.symbols["$EOF"].Symbol()

    def RequireError(self):
        if "$ERROR" not in self.symbols:
            self.symbols['$ERROR'] = \
                Syntax.SymbolTableEntry(Error(), self.termcounter, self.ERROR)
            self.termcounter += 1

        return self.symbols["$ERROR"].Symbol()


    def RequireUndef(self):
        if "$UNDEF" not in self.symbols:
            self.symbols['$UNDEF'] = \
                Syntax.SymbolTableEntry(Undef(), None, self.UNDEF)

        return self.symbols["$UNDEF"].Symbol()

    def RequireTerminal(self, name, stoken=False):
        if name not in self.symbols:
            self.symbols[name] = \
                Syntax.SymbolTableEntry(Terminal(name, stoken),
                                        self.termcounter, self.TERMINAL)
            self.termcounter += 1

        return self.symbols[name].Symbol()

    def RequireMeta(self, name):
        if name not in self.symbols:
            self.symbols[name] = \
                Syntax.SymbolTableEntry(Meta(name), self.metacounter, self.META)
            self.metacounter += 1

        return self.symbols[name].Symbol()

    def AddHeader(self, line):
        self.header.append(line)

    def SymTable(self):
        return self.symbols

    def Header(self):
        return iter(self.header)

    def SymTableMap(self, key=None, value=None, filt=None):
        """
        map/filter on the symtable
        """
        if key is None:
            key = lambda x: x.Symbol()

        if value is None:
            value = lambda x: x

        if filt is None:
            filt = lambda x: True

        return {key(symbol): value(symbol)
                for symbol in self.symbols.values()
                if filt(symbol)}
