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


class Symtable:

    TERMINAL = 0
    META = 1
    EOF = 2
    UNDEF = 3
    ERROR = 4

    class SymbolTableEntry(object):

        def __init__(self, symbol, symbol_number, symtype):
            self._symbol = symbol
            self._number = symbol_number
            self._symtype = symtype

        @property
        def symtype(self):
            return self._symtype

        @property
        def symbol(self):
            return self._symbol

        @property
        def number(self):
            return self._number

    def __init__(self):
        self._meta_counter = 0
        self._term_counter = 0

        self._symbols = {}
        self._metas = {}
        self._terminals = {}

        self._undef = {}

        # require the error symbol
        self.require_error()

    def __iter__(self):
        return iter(self._symbols)

    def __getitem__(self, index):
        return self._symbols[index]

    def metas(self):
        return {value.symbol: value.number for value in self._symbols.values()
                                           if value.symtype == Symtable.META}

    def terminals(self):
        termsyms = frozenset([Symtable.TERMINAL, Symtable.EOF, Symtable.ERROR])
        return {value.symbol: value.number for value in self._symbols.values()
                                           if value.symtype in termsyms}

    def undef(self):
        return self._undef.items()

    def require_EOF(self):
        if "$EOF" not in self._symbols:
            self._symbols['$EOF'] = \
                Symtable.SymbolTableEntry(EOF(), self._term_counter, self.EOF)

            self._term_counter += 1

        return self._symbols["$EOF"].symbol

    def require_recover(self):
        if "$RECOVER" not in self._symbols:
            self._symbols['$RECOVER'] = \
                Symtable.SymbolTableEntry(Terminal('$RECOVER', False),
                                          self._term_counter, self.TERMINAL)
            self._term_counter += 1

        return self._symbols['$RECOVER'].symbol

    def require_error(self):
        if "$ERROR" not in self._symbols:
            self._symbols['$ERROR'] = \
                Symtable.SymbolTableEntry(Error(), self._term_counter, self.ERROR)
            self._term_counter += 1

        return self._symbols["$ERROR"].symbol


    def require_undef(self):
        if "$UNDEF" not in self._symbols:
            self._symbols['$UNDEF'] = \
                Symtable.SymbolTableEntry(Undef(), None, self.UNDEF)

        return self._symbols["$UNDEF"].symbol

    def define_terminal(self, name, stoken=False):
        """
        Define and return a terminal symbol.
        """
        if name not in self._symbols:
            self._symbols[name] = \
                Symtable.SymbolTableEntry(Terminal(name, stoken),
                                        self._term_counter, self.TERMINAL)
            self._term_counter += 1

        return self._symbols[name].symbol

    def define_meta(self, name):
        """
        Define and return a meta symbol.

        If the symbol does not exist create a new meta symbol with
        that name. If it is marked undefined, remove it from the list
        of undefined symbols.
        """
        if name not in self._symbols:
            self._symbols[name] = \
                Symtable.SymbolTableEntry(Meta(name), self._meta_counter, self.META)
            self._meta_counter += 1

        if name in self._undef:
            del self._undef[name]

        return self._symbols[name].symbol

    def require_symbol(self, name, loc):
        """
        Return symbol identified by *name*.

        If the symbol does not exist create a new meta symbol with
        that name and add it to the list of undefined symbols.
        """

        if name not in self._symbols:
            self._symbols[name] = \
                Symtable.SymbolTableEntry(Meta(name), self._meta_counter, self.META)
            self._meta_counter += 1

            if name not in self._undef:
                self._undef[name] = []
            self._undef[name].append(loc)

        return self._symbols[name].symbol

class Grammar:
    # XXX most of the grammar information is defined as attributes of
    # metasymbols, therfore only few things are defined here

    def __init__(self, symtable):
        self.start_symbol = None
        self._symtable = symtable


class Lexer:
    def __init__(self):
        self._lexer = []
        self._lexer_defs = {}
        self._initial_conditions = {}
        self._inline_tokens = {}

        # the condition $INITIAL is the default condition
        # $SOL is the start of line condition
        # $SOF is the start of file condition
        initial = self._initial_conditions["$INITIAL"] = \
            InclusiveInitialCondition("$INITIAL", 0)
        sol = self._initial_conditions["$SOL"] = \
            InclusiveInitialCondition("$SOL", 1, initial)
        self._initial_conditions["$SOF"] = \
            InclusiveInitialCondition("$SOF", 2, sol)

    @property
    def initial_conditions(self):
        return self._initial_conditions

    def initial_condition(self, name):
        try:
            return self._initial_conditions[name]
        except KeyError:
            errmsg = "undefined initial condition {}".format(name)
            raise SyntaxNameError(errmsg)

    def __iter__(self):
        return iter(self._lexer)

    def inline_tokens(self):
        return self._inline_tokens.items()

    def add_lexing_rule(self, lexingrule):
        self._lexer.append(lexingrule)

    def add_inline_lexing_rule(self, token, text):
        if token in self._inline_tokens:
            assert text == self._inline_tokens[token]
        self._inline_tokens[token] = text

    def add_named_pattern(self, name, regex):
        if name in self._lexer_defs:
            raise SyntaxNameError("redefinition of pattern name {}".format(name))
        self._lexer_defs[name] = regex

    def named_patterns(self):
        return self._lexer_defs

    def add_inclusive_initial_condition(self, name):
        if name in self._initial_conditions:
            errmsg = "redefinition of initial condition {}".format(name)
            raise SyntaxNameError(errmsg)

        self._initial_conditions[name] = \
            InclusiveInitialCondition(name, len(self._initial_conditions),
                                      self.initial_condition('$INITIAL'))

    def add_exclusive_initial_condition(self, name):
        if name in self._initial_conditions:
            errmsg = "redefinition of initial condition {}".format(name)
            raise SyntaxNameError(errmsg)

        self._initial_conditions[name] = \
            ExclusiveInitialCondition(name, len(self._initial_conditions))


class VerbatimSection:

    def __init__(self):
        self._lines = []

    def add(self, line):
        self._lines.append(line)

    def __iter__(self):
        return iter(self._lines)


class Syntax(object):

    def __init__(self):
        self._symtable = Symtable()
        self._grammar = Grammar(self._symtable)
        self._ast_info = ASTInformation()
        self._header = VerbatimSection()
        self._footer = VerbatimSection()
        self._lexer = Lexer()

    @property
    def symtable(self):
        return self._symtable

    @property
    def AST_info(self):
        return self._ast_info

    @property
    def footer(self):
        return self._footer

    @property
    def header(self):
        return self._header

    @property
    def lexer(self):
        return self._lexer

    @property
    def grammar(self):
        return self._grammar

    def normalize_s_token_name(self, stoken):
        text = bytes(stoken[1:-1], "utf-8").decode('unicode-escape')
        normal_name = repr(text)
        return text, normal_name

    def define_s_token(self, stoken):
        text, normal_name = self.normalize_s_token_name(stoken)
        sym = self.symtable.require_terminal(normal_name, stoken=True)
        self.lexer.add_inline_lexing_rule(normal_name, text)

        return sym
