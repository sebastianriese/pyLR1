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

        self.start_symbol = None
        self._symbols = {}
        self._lexer_defs = {}
        self._ast_info = ASTInformation()
        self._header = []
        self._footer = []
        self._lexer = []
        self._inline_tokens = set()

        self._initial_conditions = {}
        # the condition $INITIAL is the default condition
        # $SOL is the start of line condition
        # $SOF is the start of file condition
        initial = self._initial_conditions["$INITIAL"] = \
            InclusiveInitialCondition("$INITIAL", 0)
        sol = self._initial_conditions["$SOL"] = \
            InclusiveInitialCondition("$SOL", 1, initial)
        self._initial_conditions["$SOF"] = \
            InclusiveInitialCondition("$SOF", 2, sol)

        # require the error symbol
        self.require_error()

    def __iter__(self):
        return iter(self._symbols)

    def __getitem__(self, index):
        return self._symbols[index]

    def inline_tokens(self):
        return iter(self._inline_tokens)

    @property
    def AST_info(self):
        return self._ast_info

    def lexer(self):
        return iter(self._lexer)

    def add_footer(self, line):
        self._footer.append(line)

    def footer(self):
        return iter(self._footer)

    def add_lexing_rule(self, lexingrule):
        self._lexer.append(lexingrule)

    def add_inline_lexing_rule(self, token):
        self._inline_tokens.add(token)

    def add_named_pattern(self, name, regex):
        if name in self._lexer_defs:
            raise SyntaxNameError("Pattern name {} already in use".format(name))
        self._lexer_defs[name] = regex

    def named_patterns(self):
        return self._lexer_defs

    @property
    def initial_conditions(self):
        return self._initial_conditions

    def initial_condition(self, name):
        try:
            return self._initial_conditions[name]
        except KeyError:
            errmsg = "Initial condition {} not defined".format(name)
            raise SyntaxNameError(errmsg)

    def add_inclusive_initial_condition(self, name):
        if name in self._initial_conditions:
            errmsg = "Initial condition name {} already in use".format(name)
            raise SyntaxNameError(errmsg)

        self._initial_conditions[name] = \
            InclusiveInitialCondition(name,
                                      len(self._initial_conditions),
                                      self.initial_condition('$INITIAL'))

    def add_exclusive_initial_condition(self, name):
        if name in self._initial_conditions:
            errmsg = "Initial condition name {} already in use".format(name)
            raise SyntaxNameError(errmsg)

        self._initial_conditions[name] = \
            ExclusiveInitialCondition(name, len(self._initial_conditions))

    def require_EOF(self):
        if "$EOF" not in self._symbols:
            self._symbols['$EOF'] = \
                Syntax.SymbolTableEntry(EOF(), self._term_counter, self.EOF)
            self._term_counter += 1

        return self._symbols["$EOF"].symbol

    def require_error(self):
        if "$ERROR" not in self._symbols:
            self._symbols['$ERROR'] = \
                Syntax.SymbolTableEntry(Error(), self._term_counter, self.ERROR)
            self._term_counter += 1

        return self._symbols["$ERROR"].symbol


    def require_undef(self):
        if "$UNDEF" not in self._symbols:
            self._symbols['$UNDEF'] = \
                Syntax.SymbolTableEntry(Undef(), None, self.UNDEF)

        return self._symbols["$UNDEF"].symbol

    def require_terminal(self, name, stoken=False):
        if name not in self._symbols:
            self._symbols[name] = \
                Syntax.SymbolTableEntry(Terminal(name, stoken),
                                        self._term_counter, self.TERMINAL)
            self._term_counter += 1

        return self._symbols[name].symbol

    def require_meta(self, name):
        if name not in self._symbols:
            self._symbols[name] = \
                Syntax.SymbolTableEntry(Meta(name), self._meta_counter, self.META)
            self._meta_counter += 1

        return self._symbols[name].symbol

    def add_header(self, line):
        self._header.append(line)

    def header(self):
        return iter(self._header)

    def sym_table_map(self, key=None, value=None, filt=None):
        """
        map/filter on the symtable
        """
        if key is None:
            key = lambda x: x.symbol

        if value is None:
            value = lambda x: x

        if filt is None:
            filt = lambda x: True

        return {key(symbol): value(symbol)
                for symbol in self._symbols.values()
                if filt(symbol)}
