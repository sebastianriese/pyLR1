#!/usr/bin/env python3
"""
Parse parser and lexer specifications and create DFA lexers
and LR(1) or LALR(1) parsers from them.
"""

# Copyright 2009, 2010, 2012, 2013 Sebastian Riese

# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:

# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.

# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.

import re
import sys
import os
import logging
import argparse
from functools import reduce
import operator
import tempfile
import shutil
import abc

class CantHappen(Exception):
    """
    Exception raised in code branches that should never be reached.
    """
    def __init__(self):
        super().__init__("""It seems you just found a bug

Please report this.""")

class Production(object):
    """A production in a grammar. Productions with left set to None
    may be used as arbitrary symbol strings."""

    NONE = 0
    LEFT = 1
    RIGHT = 2
    NONASSOC = 3

    def __init__(self, left, syms, number = -1):
        self.left = left
        self.syms = list(syms)
        self.numberInFile = number
        self.assoc = Production.NONE, 0
        self.text = ""

        # number in the reduction rules vector
        self.number = None
        # self.first = None

    def __iter__(self):
        return iter(self.syms)

    def __str__(self):
        text =  str(self.left) + " <- "

        for sub in self:
            text += str(sub) + " "

        return text

    def __len__(self):
        return len(self.syms)

    # important note: this number is completely independent of the
    # number used to represent  the production in the parse table!
    # This one is  used  exclusivley to resolve  conflicts in the
    # parse  tables  (earlier  declaration  ->  higer  precedence)
    def NumberInFile(self):
        return self.numberInFile

    def GetAssoc(self):
        return self.assoc

    def SetAssoc(self, assoc):
        self.assoc = assoc

    def AddSym(self, sym):
        self.syms.append(sym)

    def SetAction(self, action):
        self.text = action

    def GetAction(self):
        return self.text

    # this is the number used in the production rule
    def SetNumber(self, num):
        self.number = num

    def GetNumber(self):
        return self.number

    def First(self, visited=None):
        # if self.first is not None:
        #     return self.first

        if visited is None:
            visited = frozenset()

        result = set()

        for sub in self.syms:
            if sub  not in visited:
                result |= sub.First(visited | set([self])) - set([Empty.Instance()])

            if not sub.ReducesToEmpty():
                break

        else:
            result.add(Empty.Instance())

        # if len(visited) == 0:
        #     self.first = result

        return result

    def SetLeft(self, left):
        self.left = left

    def Left(self):
        return self.left

    def AtOrNone(self, index):
        """Return the Symbol in the Production at position index ort
        None if index is out of range."""
        try:
            return self.syms[index]
        except IndexError:
            return None

    def SubProduction(self, index0 = 0, index1 = None):
        """
        Return a production with left=None and
        syms=self.syms[index0:index1]. The main use of this is to
        evaluate the FIRST set of the subproductions.
        """
        return Production(None, self.syms[index0:index1])

    def Concat(self, elem):
        """
        Return a new Production with left=None and
        syms=self.syms+[elem].  The main use of this is to evaluate
        the FIRST set of the concatenation.
        """

        if elem.IsEmpty():
            return Production(None, self)

        return Production(None, self.syms + [elem])


class LR1Item(object):
    """A LR(1) item (production, position, lookahead set)"""

    def __init__(self, prod, pos, la):
        self.prod = prod
        self.pos = pos
        self.la = frozenset(la)

    def __str__(self):
        text =  (self.prod.left.Name() or "None") + " <- "
        count = 0

        for sub in self.prod:
            if count == self.pos:
                text += ". "

            text += (sub.Name() or "None") + " "
            count += 1

        if count == self.pos:
            text += ". "

        text += "{ "

        for sub in self.la:
            text += (sub.Name() or "None") + " "

        text += "}"

        return text

    closure = dict()

    @classmethod
    def FromCore(clazz, lr0, la):
        return clazz(lr0.prod, lr0.pos, la)

    def __hash__(self):
        return hash(self.prod) \
            ^ hash(self.pos) \
            ^ hash(self.la)

    def __eq__(self, other):
        return self.prod == other.prod \
            and self.pos == other.pos \
            and self.la == other.la

    def InKernel(self):
        return self.pos != 0 or (self.prod.left.Name() == "$START")

    def AfterDot(self):
        return self.prod.AtOrNone(self.pos)

    def IsReduce(self):
        return self.prod.AtOrNone(self.pos) is None

    def Prod(self):
        return self.prod

    def Pos(self):
        return self.pos

    def Core(self):
        return LR1Item(self.prod, self.pos, frozenset())

    def SetLookahead(self, la):
        if (self.prod,self.pos,self.la) in self.closure:
            # the buffered closure is no longer valid, once
            # a new lookahead set is assigned
            del self.closure[(self.prod,self.pos,self.la)]

        self.la = frozenset(la)

    def Lookahead(self):
        return self.la

    def Goto(self, symbol):
        afterDot = self.AfterDot()
        result = set()

        if afterDot == symbol:
            result |= LR1Item(self.prod, self.pos+1, self.la).Closure()

        return result

    def Closure(self, visited=None):
        # possibly the buffering is buggy
        if (self.prod,self.pos,self.la) in self.closure:
             return self.closure[(self.prod,self.pos,self.la)]

        if visited is None:
            visited = frozenset()

        closure = set([self])
        afterDot = self.AfterDot()
        recurses = False

        if afterDot:
            laset = set()

            for la in self.la:
                firstconcat = self.prod.SubProduction(self.pos+1, None).Concat(la)
                laset |= firstconcat.First()

            for prod in afterDot.Productions():

                if self not in visited:
                    elem = LR1Item(prod, 0, laset)
                    closure |= elem.Closure(visited | set([self]))
                else:
                    recurses = True

        if not recurses:
            self.closure[(self.prod,self.pos,self.la)] = closure

        return closure

    def TransitionsTo(self, other):
        """
        Determine whether the LR item generates `other` on transition.
        """

        if self.IsReduce():
            return False

        return self.Prod() == other.Prod() and self.Pos() + 1 == other.Pos()

class Symbol(object):
    """Base class for all types symbols in the system (terminal, meta,
    undef and empty)."""

    def __init__(self, name, syntax):
        self.name = name
        self.syntax = syntax

    def __str__(self):
        return self.Name()

    def Name(self):
        return self.name

    def IsSToken(self):
        return False

    def Syntax(self):
        return self.syntax

    def Productions(self):
        """Return an iterator over the list of productions"""
        return iter([])

    def First(self, visited=None):
        """The FIRST-set of the symbol."""
        raise NotImplementedError()

    def ReducesToEmpty(self, visited=None):
        """Return whether the symbol can be reduced to the empty
        symbol."""
        return False

    def Productions(self):
        return iter([])

    def IsEmpty(self):
        """Return whether the symbol is the empty symbol."""
        return False

class EOF(Symbol):
    """
    The EOF symbol.
    """

    def __init__(self):
        super(EOF, self).__init__("$EOF", None)

    def First(self, visited=None):
        return set([self])

class Error(Symbol):
    """
    The Error symbol. This is the terminal symbol emitted on invalid
    lexemes.
    """

    def __init__(self):
        super(Error, self).__init__("$ERROR", None)

    def First(self, visited=None):
        return set([self])

class Undef(Symbol):
    """
    The Undef symbol used in the LALR(1) lookahead
    construction algorithm
    """

    def __init__(self):
        super(Undef, self).__init__("$UNDEF", None)

    def First(self, visited=None):
        return set([self])


class Empty(Symbol):
    """
    The empty terminal symbol.  The class is a singleton, in order to
    make many of the methods of the other classes work you should not
    instanciate it. Use the Instance class method for retrieving the
    singleton instance.
    """

    instance = None

    def __init__(self):
        super(Empty, self).__init__("$Empty", None)

    @classmethod
    def Instance(clazz):
        """Return the singleton instance, create it, if neccessary."""
        if not clazz.instance:
            clazz.instance = Empty()

        return clazz.instance

    def First(self, visited=None):
        return set([self])

    def ReducesToEmpty(self, visited=None):
        # empty is not allowed in productions
        raise CantHappen()

    def IsEmpty(self):
        return True

class Terminal(Symbol):
    """The Terminal symbol class."""

    def __init__(self, name, syntax, stoken):
        super(Terminal, self).__init__(name, syntax)
        self.stoken = stoken

    def First(self, visited=None):
        return set([self])

    def IsSToken(self):
        return self.stoken

class Meta(Symbol):
    """
    The Metasymbol class. This stores the grammar for the symbol.
    """

    def __init__(self, name, syntax):
        super(Meta, self).__init__(name, syntax)
        self.prod = []
        self.first = None
        self.reduces_to_empty = None

    def Productions(self):
        return iter(self.prod)

    def AddProd(self, prod):
        prod.SetLeft(self)
        self.prod.append(prod)

    def Productions(self):
        # the copying is just a safety measure ...
        return self.prod[:]

    def First(self, visited=None):
        # if self.first is not None:
        #     return self.first

        result = set()

        if visited is None: visited = frozenset()

        for prod in self.prod:
            result |= prod.First(visited | set([self]))

        # if len(visited) == 0:
        #     self.first = result

        return result

    def ReducesToEmpty(self, visited=None):

        if self.reduces_to_empty is not None:
            return self.reduces_to_empty

        if visited is None:
            visited = frozenset()

        for prod in self.prod:

            for sub in prod:
                if sub not in visited and not sub.ReducesToEmpty(visited | set([self])):
                    # this production doesn't reduce to empty (because
                    # one subsymbol doesn't)
                    break
            else:
                # all subsymbols in this production reduced to empty,
                # therefore the symbol may reduce to empty

                if len(visited) == 0:
                    self.reduces_to_empty = True

                return True

        # no production for this symbol does reduce to empty
        if len(visited) == 0:
            self.reduces_to_empty = False

        return False

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

class AutoAccept(type):

    def __new__(cls, name, bases, dict):
        """
        Provide automagical VisitorBase and Accept generation with
        completeness checking for subclasses.
        """
        if 'Accept' not in dict:
            dict['Accept'] = cls._make_accept(name)

        # setup portable subclass tracking
        # XXX: maybe this should be weaklist
        # or ordered set
        dict['_subclasses_'] = []

        res = super().__new__(cls, name, bases, dict)

        for base in bases:
            if isinstance(base, AutoAccept):
                base._register_subclass(res)

        return res

    def _register_subclass(self, subclass):
        self._subclasses_.append(subclass)

    @staticmethod
    def _make_accept(name):
        visitor_name = "Visit" + name
        def accept(self, visitor):
            return getattr(visitor, visitor_name)(self)
        return accept

    @staticmethod
    def _make_visit():
        def visit(self, obj):
            pass
        return visit

    @staticmethod
    def _make_visit_any():
        def visit(self, obj):
            return obj.Accept(self)
        return visit

    def base_visitor(self):
        dict = {}
        for subclass in self._subclasses_:
            dict["Visit" + subclass.__name__] = abc.abstractmethod(self._make_visit())
        dict["Visit"] = self._make_visit_any()

        return abc.ABCMeta(self.__name__+"Visitor", (object,), dict)

class LexingAction(object, metaclass=AutoAccept):
    """
    Lexing actions.

    Take care these do not get dictionary keys or set members (or
    anything they are required to have a constant hash for or `==` based
    on `id`) while they might change.

    Rationale: They are compared and hashed for their members because
    we will make them unique, before writing them to the output file.
    """

    def __init__(self):
        pass

    def Accept(self):
        raise NotImplementedError()

    def __eq__(self, other):
        return self.__class__ == other.__class__ \
            and self.__dict__ == other.__dict__

    def __hash__(self):
        # TODO: find better solution than xor, it destroys a lot of
        # the hashes because there will be many hash(x) == id(x)
        # objects and the addresses id(x) will tend to be in a narrow
        # region.
        return reduce(operator.__xor__,
                      map(hash, self.__dict__.items()),
                      id(self.__class__))

class Debug(LexingAction):

    def __init__(self, text):
        super(Debug, self).__init__()
        self.text = text

    def __str__(self):
        return "Debug(" + repr(self.text) + ")"

    def Text(self):
        return self.text

class List(LexingAction):

    def __init__(self, lst = None):
        super(List, self).__init__()
        self.list = lst or []

    def __str__(self):
        return "List([" + ", ".join(map(str, self.list)) + "])"

    def Append(self, action):
        self.list.append(action)

    def List(self):
        return self.list

    # we have to implement this because lists
    # do not hash well
    def __hash__(self):
        return reduce(operator.__xor__,
                      map(hash, self.list),
                      id(self.__class__))

class Begin(LexingAction):

    def __init__(self, state):
        super(Begin, self).__init__()
        self.state = state

    def __repr__(self):
        return "Begin(%s)" % self.state

    def State(self):
        return self.state

class Push(LexingAction):

    def __init__(self, state):
        super(Push, self).__init__()
        self.state = state

    def __repr__(self):
        return "Push(%s)" % self.state

    def State(self):
        return self.state

class Pop(LexingAction):

    def __init__(self):
        super(Pop, self).__init__()

    def __repr__(self):
        return "Pop()"

class Restart(LexingAction):

    def __init__(self):
        super(Restart, self).__init__()

    def __repr__(self):
        return "Restart()"

class Continue(LexingAction):

    def __init__(self):
        super(Continue, self).__init__()

    def __repr__(self):
        return "Continue()"

class Token(LexingAction):

    def __init__(self, name):
        super(Token, self).__init__()
        self.name = name

    def __repr__(self):
        return "Token('%s')" % self.name

    def Name(self):
        return self.name

class Function(LexingAction):

    def __init__(self, name):
        super().__init__()
        self.name = name

    def __repr__(self):
        return "Function('%s')" % self.name

    def Name(self):
        return self.name


class GetMatch(LexingAction):

    def __init__(self):
        super(GetMatch, self).__init__()

    def __repr__(self):
        return "GetMatch()"

LexingActionVisitor = LexingAction.base_visitor()

class Parser(object):
    ast_re = re.compile(r"%ast\s*$")
    parser_re = re.compile(r"%parser\s*$")
    lexer_re = re.compile(r"%lexer\s*$")
    footer_re = re.compile(r"%footer\s*$")
    comment_re = re.compile(r"\s*([^\\]#.*|)(#.*)?\s*$")

    lexing_rule_re = re.compile(r"""
    # the initial condition specifier
    (<(?P<initialNames>([a-zA-Z0-9,_]+|\$SOL|\$SOF|\$INITIAL|\s)*)>|(?P<sol>\^)|)

    # the regex
    (?P<regex>(\S|(\\\ ))+)\s+

    # the action spec
    (%debug\(\s*"(?P<debug>[^\"]*)"\s*\)\s*,\s*)?

    ((?P<beginType>%begin|%push|%pop|%function)
        \(\s*(?P<begin>([A-Za-z0-9_]+|\$INITIAL|))\s*\)\s*,\s*)?

    ((?P<beginType2>%begin|%push|%pop|%function)
        \(\s*(?P<begin2>([A-Za-z0-9_]+|\$INITIAL|))\s*\)\s*,\s*)?

    ((?P<beginType3>%begin|%push|%pop|%function)
        \(\s*(?P<begin3>([A-Za-z0-9_]+|\$INITIAL|))\s*\)\s*,\s*)?

    ((?P<token>[a-zA-Z_][a-zA-Z_0-9]*)
     |(?P<restart>%restart)
     |(?P<continue>%continue))\s*$""",
                                flags=re.X)

    lexing_statedef_re = re.compile(r'(?P<type>%x|%s|%nullmatch) (?P<names>([a-zA-Z_][a-zA-Z0-9_]*(\s*,\s*)?)+)\s*$')
    lexing_named_pattern_def_re = re.compile(r'''%def
    (?P<one>\s+
          (?P<name>[a-zA-Z_][a-zA-Z0-9_]*)\s+
          (?P<regex>(\S|(\\\ ))+)
    )?\s*$''', flags=re.X)
    lexing_named_pattern_line_re = re.compile(r'''
          (?P<name>[a-zA-Z_][a-zA-Z0-9_]*)\s+
          (?P<regex>(\S|(\\\ ))+)\s*
    $''', flags=re.X)

    syntax_rule_re = re.compile(r"([a-zA-Z_][a-zA-Z_0-9]*):\s*$")
    syntax_symbol_re = re.compile(r"([a-zA-Z_][a-zA-Z_0-9]*)")
    syntax_action_re = re.compile(r'\:')
    syntax_stoken_re = re.compile(r'\"((.|\\\")+?)\"')
    syntax_empty_re = re.compile(r'%empty')
    syntax_prec_re = re.compile(r'%prec\s*\(\s*([a-zA-Z_][a-zA-Z_0-9]*)\s*\)')
    syntax_AST_re = re.compile(r'%AST\s*\(\s*([a-zA-Z_][a-zA-Z_0-9]*)\s*\)')
    syntax_binding_re = re.compile(r'%left|%right|%nonassoc')
    syntax_binding_param_re = re.compile(r'(,\s*)?([a-zA-Z_][a-zA-Z_0-9]*|\"(.|\\\")+?\")')

    ast_list_re = re.compile(r'%list\s+([a-zA-Z_][a-zA-Z_0-9]*)')
    ast_visitor_re = re.compile(r'%visitor\s+([a-zA-Z_][a-zA-Z_0-9]*)')

    def __init__(self, grammar_file, logger):
        self.logger = logger

        self.syntax = Syntax()

        self.grammar_file = grammar_file
        self.line = 0

        # ugly state variable available to the subparsers
        self.current = None
        # even more ugly state ... only usable by one subparser
        self.assocDefs = dict()
        self.assocPower = 0
        self.productionNumber = 0
        self.indent = None

        self.undef = {}
        self.defined = set()

        self.state = self.Header

    def Header(self, line, eof=False):
        if eof:
            return

        self.syntax.AddHeader(line)

    def Footer(self, line, eof=False):
        if eof:
            return

        self.syntax.AddFooter(line)

    def AST(self, line, eof=False):
        if eof:
            return

        match = self.ast_list_re.match(line)
        if match:
            self.syntax.ASTInfo().List(match.group(1))
            return

        match = self.ast_visitor_re.match(line)
        if not match:
            self.logger.error("line %i, invalid AST spec" % (self.line,))
            return

        self.syntax.ASTInfo().visitor = match.group(1)

    def LexerDefs(self, line, eof=False):
        if eof:
            return

        indent = self.Indention(line)
        if self.indent is None:
            self.indent = indent

        if indent < self.indent:
            self.indent = None
            self.state = self.Lexer
            return self.Lexer(line)

        match = self.lexing_named_pattern_line_re.match(line.strip())
        if match:
            try:
                self.syntax.AddNamedPattern(match.group('name'),
                                            Regex(match.group('regex'),
                                                  bindings=self.syntax.NamedPatterns()).ast)
            except (RegexSyntaxError, SyntaxNameError) as e:
                self.logger.error("line {}: syntax error in regex def: {}".format(self.line, e.args[0]))
        else:
            self.logger.error("line {}, invalid named pattern spec".format(self.line))


    def Lexer(self, line, eof=False):
         if eof:
             return

         match = self.lexing_statedef_re.match(line)
         if match:
             statenames = [name.strip() for name in match.group('names').split(',')]
             statenames = sum([name.split() for name in statenames], [])
             try:
                 if match.group('type') == '%x':
                     for name in statenames:
                         self.syntax.AddExclusiveInitialCondition(name)
                 elif match.group('type') == '%s':
                     for name in statenames:
                         self.syntax.AddInclusiveInitialCondition(name)
                 elif match.group('type') == '%nullmatch':
                     for name in statenames:
                         self.syntax.InitialCondition(name).DeclareNullmatch()
                 else:
                     raise CantHappen()
             except SyntaxNameError as e:
                 self.logger.error("line {}: {}".format(self.line, str(e)))
             return

         match = self.lexing_named_pattern_def_re.match(line)
         if match:
             if match.group('one'):
                 try:
                     self.syntax.AddNamedPattern(match.group('name'),
                                                 Regex(match.group('regex'),
                                                       bindings=self.syntax.NamedPatterns()).ast)
                 except (RegexSyntaxError, SyntaxNameError) as e:
                     self.logger.error("line {}: syntax error in regex def: {}".format(self.line, e.args[0]))
             else:
                 self.state = self.LexerDefs
                 return


         match = self.lexing_rule_re.match(line)
         state = set()

         if not match:
             self.logger.error("line {}: invalid token spec".format(self.line))
             return

         # determine the inital condtions
         if match.group('sol'):
             state.add(self.syntax.InitialCondition("$SOL"))

         if match.group('initialNames'):
             names = [name.strip() for name in match.group('initialNames').split(',')]
             for name in names:
                 try:
                     state.add(self.syntax.InitialCondition(name))
                 except  SyntaxNameError as e:
                     self.logger.error("line {}: error in start condition list: {}".format(self.line, e.args[0]))

         # print('SOL match:', match.group('sol'), 'inital names match:', match.group('initialNames'))

         # collect actions
         action = List()

         if match.group('debug'):
             action.Append(Debug(match.group('debug')))

         def beginMatcher(head, args):
             if match.group(head):
                 if match.group(head) == '%begin':
                     action.Append(Begin(self.syntax.InitialCondition(match.group(args))))
                 elif match.group(head) == '%push':
                     action.Append(Push(self.syntax.InitialCondition(match.group(args))))
                 elif match.group(head) == '%pop':
                     if match.group(args):
                         self.logger.error("line {}: state argument for %pop".format(self.line))
                     action.Append(Pop())
                 elif match.group(head) == '%function':
                     action.Append(Function(match.group(args)))
                 else:
                     self.logger.error("line {}: invalid lexing action".format(self.line))
                     return True
             return False

         try:
             if beginMatcher('beginType', 'begin'): return
             if beginMatcher('beginType2', 'begin2'): return
             if beginMatcher('beginType3', 'begin3'): return
         except SyntaxNameError as e:
             self.logger.error("line {}: error in lexaction: {}".format(self.line, e.args[0]))

         if match.group('restart'):
             action.Append(Restart())

         elif match.group('token'):
             self.syntax.RequireTerminal(match.group('token'))
             action.Append(Token(match.group('token')))

         elif match.group('continue'):
             action.Append(Continue())

         # put it all together, add a lexing rule
         try:
             regex = Regex(match.group('regex'), bindings=self.syntax.NamedPatterns())
         except RegexSyntaxError as e:
             self.logger.error("line {}: syntax error in regex: {}".format(self.line, e.args[0]))
         else:
             self.syntax.AddLexingRule(LexingRule(state, regex, action))

    def Parser(self, line, eof=False):
        if eof:
            return

        if self.current is None:
            match = self.syntax_binding_re.match(line)
            obj = None

            if match:
                if match.group(0) == '%left':
                    obj = Production.LEFT, self.assocPower
                elif match.group(0) == '%right':
                    obj = Production.RIGHT, self.assocPower
                elif match.group(0) == '%nonassoc':
                    obj = Production.NONASSOC, self.assocPower

                line = line[len(match.group(0)):]
                line = line.strip()

                while line:
                    match = self.syntax_binding_param_re.match(line)
                    if match:
                        self.assocDefs[match.group(2)] = obj

                        line = line[len(match.group(0)):]
                        line = line.strip()
                    else:
                        self.logger.error("line {}: Syntax error in associativity definition".format(self.line))
                        return

                self.assocPower += 1
                return

        match = self.syntax_rule_re.match(line)
        if match:
            symbol = self.syntax.RequireMeta(match.group(1))
            if symbol in self.undef:
                del self.undef[symbol]
            self.defined.add(symbol)

            if self.current is None:
                self.syntax.SetStart(symbol)

            self.current = symbol

        else:
            prod = Production(self.current, [], self.productionNumber)
            self.productionNumber += 1
            line = line.strip()

            while line:
                match = self.syntax_stoken_re.match(line)
                elem = None

                # this loop is broken
                # not beautiful, but more readable than all other solutions (I don't want to nest ifs to thirty levels)
                # effectively this simulates goto to common code
                while True:
                    if match:
                        elem = self.syntax.RequireTerminal(match.group(0), stoken=True)
                        self.syntax.AddInlineLexingRule(match.group(1))
                        break

                    match = self.syntax_symbol_re.match(line)

                    if match:
                        elem = self.syntax.RequireMeta(match.group(1))
                        # terminal symbols are already defined, and returned
                        # as such
                        if self.syntax.SymTable()[elem.Name()].SymType() == Syntax.META and \
                                elem not in self.defined:
                            self.undef.setdefault(elem, []).append(self.line)

                        break

                    match = self.syntax_empty_re.match(line)

                    if match:
                        break

                    match = self.syntax_prec_re.match(line)
                    if match:
                        try:
                            prod.SetAssoc(self.assocDefs[match.group(1)])
                        except KeyError:
                            self.logger.warning("%d: Erroneous precedence declaration" % self.line)

                        break

                    match = self.syntax_AST_re.match(line)
                    if match:
                        self.syntax.ASTInfo().Bind(prod, match.group(1))
                        break

                    match = self.syntax_action_re.match(line)

                    if match:
                        line = line[len(match.group(0)):]
                        line = line.strip()

                        if line:
                            prod.SetAction(line)
                            self.current.AddProd(prod)
                        else:
                            self.state = self.Action
                            self.current = prod

                        return

                    self.logger.error("line %d syntax error (%s)" % (self.line,line))
                    return

                line = line[len(match.group(0)):]
                line = line.strip()

                if elem:
                    prod.SetAssoc(self.assocDefs.get(elem.Name(), prod.GetAssoc()))
                    prod.AddSym(elem)

            self.current.AddProd(prod)

    @staticmethod
    def Indention(line):
        ind = 0

        for char in line:
            if char == ' ':
               ind += 1
            elif char == '\t':
                self.logger.warning("Tab used for significant indention!")
                ind += 8
            else:
                break

        return ind

    def Action(self, line, eof=False):
        if eof:
            self.current.Left().AddProd(self.current)
            return

        indent = self.Indention(line)
        if self.indent is None:
            self.indent = indent

        if indent < self.indent:
            self.state = self.Parser
            self.current.Left().AddProd(self.current)
            self.current = self.current.Left()
            self.indent = None
            return self.state(line)

        def Unindent(line):
            ind = self.Indention(line)
            line = line.strip()

            return " " * (ind - self.indent) + line

        self.current.SetAction(self.current.GetAction() + "\n" + Unindent(line))

    def Parse(self):
        self.line = 0

        for line in self.grammar_file:
            self.line += 1

            if self.comment_re.match(line):
                pass
            elif self.ast_re.match(line):
                self.state = self.AST
                self.syntax.ASTInfo().Used()
            elif self.parser_re.match(line):
                self.state = self.Parser
            elif self.lexer_re.match(line):
                self.state = self.Lexer
            elif self.footer_re.match(line):
                self.state = self.Footer
            else:
                self.state(line)

        # notify the current state of eof
        # apply any pending state
        self.state('', eof=True)

        if self.undef:
            for symbol, lines in sorted(self.undef.items(), key=lambda x: x[0].Name()):
                usedinlines = "used in lines"
                if len(lines) == 1: usedinlines = "used in line"
                self.logger.error(' '.join(["Undefined symbol", symbol.Name(), usedinlines,
                                  ', '.join(str(line) for line in lines)]))
            self.logger.error("Undefined meta symbols found")

        return self.syntax

class ASTInformation(object):

    def Used(self):
        self.used = True

    def List(self, symbol):
        self.lists.add(symbol)

    def Bind(self, production, name):
        self.bindings[production] = name

    def __init__(self):
        self.used    = False
        self.lists   = set()
        self.visitor = 'ASTVisitor'
        self.bindings = {}

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

class SyntaxNameError(Exception):
    pass

class Syntax(object):

    TERMINAL = 0
    META = 1
    EOF = 2
    UNDEF = 3
    ERROR = 4


    class SymbolTableEntry(object):

        def __init__(self, symbol, symbolNumber, symtype):
            self.symbol = symbol
            self.symbolNumber = symbolNumber
            self.symtype = symtype

        def SymType(self):
            return self.symtype

        def Symbol(self):
            return self.symbol

        def Number(self):
            return self.symbolNumber

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

        self.initialConditions = {}
        # the condition $INITIAL is the default condition
        # $SOL is the start of line condition
        # $SOF is the start of file condition
        initial = self.initialConditions["$INITIAL"] = InclusiveInitialCondition("$INITIAL", 0)
        sol = self.initialConditions["$SOL"] = InclusiveInitialCondition("$SOL", 1, initial)
        self.initialConditions["$SOF"] = InclusiveInitialCondition("$SOF", 2, sol)

        # require the error symbol
        self.RequireError()

    def InlineTokens(self):
        return self.inline_tokens

    def ASTInfo(self):
        return self.ast_info

    def Lexer(self):
        return self.lexer

    def SetStart(self, start):
        self.start = start

    def Start(self):
        return self.start

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
        return self.initialConditions.values()

    def InitialCondition(self, name):
        try:
            return self.initialConditions[name]
        except KeyError:
            raise SyntaxNameError("Initial condition {} not defined".format(name))

    def AddInclusiveInitialCondition(self, name):
        if name in self.initialConditions:
            raise SyntaxNameError("Initial condition name {} already in use".format(name))

        self.initialConditions[name] = InclusiveInitialCondition(name, len(self.initialConditions))

    def AddExclusiveInitialCondition(self, name):
        if name in self.initialConditions:
            raise SyntaxNameError("Initial condition name {} already in use".format(name))

        self.initialConditions[name] = ExclusiveInitialCondition(name, len(self.initialConditions))

    def RequireEOF(self):
        if "$EOF" not in self.symbols:
            self.symbols['$EOF'] = Syntax.SymbolTableEntry(EOF(), self.termcounter, self.EOF)
            self.termcounter += 1

        return self.symbols["$EOF"].Symbol()

    def RequireError(self):
        if "$ERROR" not in self.symbols:
            self.symbols['$ERROR'] = Syntax.SymbolTableEntry(Error(), self.termcounter, self.ERROR)
            self.termcounter += 1

        return self.symbols["$ERROR"].Symbol()


    def RequireUndef(self):
        if "$UNDEF" not in self.symbols:
            self.symbols['$UNDEF'] = Syntax.SymbolTableEntry(Undef(), None, self.UNDEF)

        return self.symbols["$UNDEF"].Symbol()

    def RequireTerminal(self, name, stoken=False):
        if name not in self.symbols:
            self.symbols[name] = Syntax.SymbolTableEntry(Terminal(name, self, stoken), self.termcounter, self.TERMINAL)
            self.termcounter += 1

        return self.symbols[name].Symbol()

    def RequireMeta(self, name):
        if name not in self.symbols:
            self.symbols[name] = Syntax.SymbolTableEntry(Meta(name, self), self.metacounter, self.META)
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

class ParseTable(object):
    """
    A LR parse table.
    """

    def __init__(self, actiontable, gototable, start, rules):
        self.start = start
        self.actiontable = actiontable
        self.gototable = gototable
        self.rules = rules

    def Actiontable(self):
        return self.actiontable

    def Gototable(self):
        return self.gototable

    def Start(self):
        return self.start

    def Rules(self):
        return self.rules

    def Print(self):

        i = 0

        for rule in self.rules:
            print("(%d) %s" % (i, str(rule)))
            i += 1



        giter = iter(self.gototable)
        aiter = iter(self.actiontable)
        try:
            while True:
                gline = next(giter)
                aline = next(aiter)
                for entry in aline:
                    entrystr = ""
                    first = True


                    entrystr += str(entry)
                    print(entrystr.center(5), end=' ')

                for entry in gline:
                    print(str(entry).center(5), end=' ')
                print("")

        except StopIteration:
                pass


class LRAction(metaclass=AutoAccept):

    def IsShift(self): return False
    def IsReduce(self): return False

    def __init__(self, prec, numInFile):
        self.prec = prec
        self.numInFile = numInFile

    def GetAssoc(self): return self.prec
    def NumberInFile(self): return self.numInFile

    def Accept(self, visitor):
        raise NotImplementedError()

class Shift(LRAction):
    def IsShift(self): return True

    def __init__(self, newstate, prec, n):
        super(Shift, self).__init__(prec, n)
        self.newstate = newstate

    def __str__(self):
        return "s%d" % self.newstate

    def Next(self):
        return self.newstate

class Reduce(LRAction):
    def IsReduce(self): return True

    def __init__(self, reduction, prec, n):
        super(Reduce, self).__init__(prec, n)
        self.reduction = reduction

    def __str__(self):
        return "r%d" % self.reduction

    def Red(self):
        return self.reduction

LRActionVisitor = LRAction.base_visitor()

class StateTransition(object):
    """
    A transition from a LR state to another LR state
    """

    def __init__(self, symbol, state):
        self.symbol = symbol
        self.state = state

    def __eq__(self, other):
        return self.symbol == other.symbol \
            and self.state == other.state

    def __hash__(self):
        return hash(self.symbol) ^ hash(self.state)

    def Symbol(self):
        return self.symbol

    def State(self):
        return self.state

class StateTransitionGraph(object, metaclass=abc.ABCMeta):

    def __init__(self, grammar, logger):
        """
        An *LR(1) state transition graph, this has the behaviour
        common to LALR(1), LR(1), SLR(1), ... transition graphs.
        """

        self.logger = logger

        self.grammar = grammar
        self.states = []

        self.conflicts = 0

        self.start = None

    def ReportNumOfConflicts(self):
        if self.conflicts:
            self.logger.warning(str(self.conflicts) + " conflict(s) found!")

    @abc.abstractmethod
    def Construct(self):
        """
        Construct the *LR(1) automaton.
        """
        pass

    def NormalizeItemSet(self, elements):
        """
        Normalize the item set.

        Normal means:

        * each core occurs only once
        * the lookahead set assigned to a core is the union of the
          ones assigned to the occurences of core before

        Returns the normalized item set.
        """
        cores = {}
        for elem in elements:
            if elem.Core() not in cores:
                cores[elem.Core()] = set()

            cores[elem.Core()] |= elem.Lookahead()

        elements = set()
        for core in cores:
            elements.add(LR1Item.FromCore(core, cores[core]))
        cores = None

        return elements

    def RequireState(self, elements):
        """
        Check whether a state having the given elements already
        exists. If it does exist return it, otherwise create the new
        state and recursively determine its sub states.
        """

        elements = self.NormalizeItemSet(elements)

        # do we already have this state?
        for state in self.states:
            if state.elements == elements:
                return state

        # instanciate the new state
        state = self.GenerateState(len(self.states), elements)
        self.states.append(state)
        state.GenerateSubStates()
        return state

    @abc.abstractmethod
    def GenerateState(self, number, elements):
        """
        Generate an appropriate `LR1StateGraphElement`. Where `number`
        is the assigned id number and `elements` is the associated set
        of LR1Items.
        """
        pass

    def ResolveConflict(self, state, old, new):
        """
        Resolve a parse table conflict.

        The `state` argument is the LR(1) graph state causing the
        conflict, `old` and `new` are the action already in the table
        respective the proposed action.

        For reduce/reduce-conflicts the production later in file takes
        precedence and a warning is issued.

        For shift/reduce-conflicts the precedence declarations are
        used to resolve the conflict. If no precedence is declared
        a warning is issued and the shift action is chosen.

        Returns the preceding action.
        """
        if old is None:
            return new

        if old.IsReduce():
            self.logger.info(str(state))
            self.logger.warning("Default to the first reduce for reduce/reduce-conflict")
            self.conflicts += 1
            if old.NumberInFile() > new.NumberInFile():
                return new
            else:
                return old

        elif old.IsShift():
            assoc, prec = old.GetAssoc()
            associ, preci = new.GetAssoc()

            # shift wins over reduce by default
            if assoc == Production.NONE:
                self.logger.info(str(state))
                self.logger.warning("Default to shift for shift/reduce-conflict")
                self.conflicts += 1
                return old

            elif assoc == Production.NONASSOC:
                # generate an error entry for nonassoc
                if preci > prec:
                    return new
                elif preci == prec:
                    # XXX: can there be a situation where this None is
                    # mistaken for: nothing so far and then an action
                    # is written though there are three nonassoc
                    # productions of equal precedence
                    return None
                else:
                    return old

            elif assoc == Production.LEFT:
                if preci >= prec:
                    return new
                else:
                    return old

            elif assoc == Production.RIGHT:
                if preci > prec:
                    return new
                else:
                    return old
            else:
                raise CantHappen()


    def Kernels(self):
        """
        Reduce the item sets to their kernels
        (needed for LALR lookahead generation)
        """
        for state in self.states:
            state.Kernel()

    def CloseKernels(self):
        """
        Complete the sets to their closure again
        after they where reduced to their kernels
        """

        for state in self.states:
            state.Close()

    def CreateParseTable(self, terminals, metas):
        """
        Create the parse table from the LR graph. Requires two mappings
        from `Symbol` objects to their respective numbers: One of them
        for the terminals and another for the meta-symbols.

        They can be created from the `Syntax` object by calling:

            termsyms = frozenset([Syntax.TERMINAL, Syntax.EOF, Syntax.ERROR])
            syn.SymTableMap(filt=lambda x: x.SymType() in termsyms,
                            value=lambda x: x.Number())

            syn.SymTableMap(filt=lambda x: x.SymType() == Syntax.META,
                            value=lambda x: x.Number())

        The function returns a `Parsetable` object.
        """
        atable = []
        jtable = []

        rules = []

        # populate the rules vector
        for meta in metas:
            for rule in meta.Productions():
                rule.SetNumber(len(rules))
                rules.append(rule)

        for state in self.states:
            # append the current row to the action- and jumptables
            acur = [None] * len(terminals)
            jcur = [None] * len(metas)

            atable.append(acur)
            jtable.append(jcur)

            # fill goto table and write shifts to the action table
            for trans, prods in state.Transitions().items():
                symb = trans.Symbol()
                tstate = trans.State()

                if symb in metas:
                    jcur[metas[symb]] = tstate.Number()

                elif symb in terminals:
                    assoc = Production.NONE, -1
                    prec = -1

                    for item in prods:
                        nprec = item.Prod().NumberInFile()
                        if nprec > prec:
                            prec = nprec
                            assoc = item.Prod().GetAssoc()

                    acur[terminals[symb]] = Shift(tstate.Number(),
                                                  assoc, prec)
                else:
                    print(state, file=sys.stderr)
                    print(str(symb), file=sys.stderr)
                    raise CantHappen()

            # write reductions to the action table
            for item in state.Reductions():
                prod = item.Prod()
                reduceAction = Reduce(prod.GetNumber(),
                                      prod.GetAssoc(),
                                      prod.NumberInFile())

                for la in item.Lookahead():
                    acur[terminals[la]] = \
                        self.ResolveConflict(state,
                                             acur[terminals[la]],
                                             reduceAction)

        return ParseTable(atable, jtable, self.start.Number(), rules)

class LALR1StateTransitionGraph(StateTransitionGraph):

    def __init__(self, grammar, logger):
        """
        The LALR(1) State Transition Graph.
        """
        super(LALR1StateTransitionGraph, self).__init__(grammar, logger)

    def Propagate(self):
        """
        Generate the lookahead sets.

        The other parts of this computation are done in the
        `LALR1StateTransitionGraphElement`.

        For details on the algorithm see the Dragon Book.
        """

        self.Kernels()

        # determine token generation and propagation
        for state in self.states:
            state.DeterminePropagationAndGeneration()

        # add EOF to the "$START <- start ." lookahead set
        for item in self.start.Elements():
            if item.Prod().left == self.grammar.RequireMeta("$START"):
                item.SetLookahead(set([self.grammar.RequireEOF()]))

        # set the spontaneously generated lookahead tokens
        for state in self.states:
            state.Generate()

        # propagate the lookahead tokens
        propagated = True
        while propagated:
            propagated = False

            for state in self.states:
                propagated = state.Propagate() or propagated

        self.CloseKernels()

    def GenerateState(self, number, elements):
        return LALR1StateTransitionGraphElement(self, number, elements)

    def Construct(self):

        # construct the starting point (virtual starting node) and use
        # the RequireElement-method to build up the tree

        prod = Production(self.grammar.RequireMeta("$START"),
                          [self.grammar.Start()], -1)

        prod.SetAction("raise Accept()")

        self.grammar.RequireMeta("$START").AddProd(prod)

        # we use an empty lookahead set to generate the LR(0) automaton
        start = LR1Item(prod,0,set([]))

        self.start = self.RequireState(start.Closure())

        # calculate the LALR(1) lookahead sets
        self.Propagate()


class LR1StateTransitionGraph(StateTransitionGraph):
    """
    The LR(1) State Transition Graph.
    """

    def __init__(self, grammar, logger):
        super(LR1StateTransitionGraph, self).__init__(grammar, logger)

    def Construct(self):

        prod = Production(self.grammar.RequireMeta("$START"),
                          [self.grammar.Start()], -1)
        prod.SetAction("raise Accept()")

        self.grammar.RequireMeta("$START").AddProd(prod)

        start = LR1Item(prod,0,set([self.grammar.RequireEOF()])).Closure()

        self.start = self.RequireState(start)

    def GenerateState(self, number, elements):
        return LR1StateTransitionGraphElement(self, number, elements)

class LR1StateTransitionGraphElement(object):

    def __init__(self, graph, number, elements):
        self.number = number
        self.graph = graph
        self.elements = elements
        self.transitions = dict()

    def __str__(self):
        lines = []
        lines.append("state: " + str(self.number))

        lines.append("elements:")

        for elem in self.elements:
            lines.append(str(elem))

        lines.append("transitions:")
        for trans in self.transitions:
            lines.append((trans.Symbol().Name() or "None") + " -> " + str(trans.State().number))

        return '\n'.join(lines)

    def Elements(self):
        return self.elements

    def Reductions(self):
        """
        A generator yielding the reduction items in this LR state.
        """
        for elem in self.elements:
            if elem.IsReduce():
                yield elem

    def Transitions(self):
        """
        Return the state transitions.
        """
        return self.transitions

    def Number(self):
        """
        Return the number.
        """
        return self.number

    def Kernel(self):
        """
        Reduce the item set to the Kernel items
        """
        res = set()

        for elem in self.elements:
            if elem.InKernel():
                res.add(elem)

        self.elements = res

    def Close(self):
        """
        Complete the item set to its closure
        """
        res = set()

        for elem in self.elements:
            res |= elem.Closure()

        self.elements = self.graph.NormalizeItemSet(res)

    def GenerateSubStates(self):
        """
        Determine the substates of this state and add them to the
        transition graph.
        """

        for elem in self.elements:

            if elem.AfterDot():
                goto = set()

                for cur in self.elements:
                    goto |= cur.Goto(elem.AfterDot())

                trans = StateTransition(elem.AfterDot(), self.graph.RequireState(goto))
                if trans not in self.transitions:
                    self.transitions[trans] = set()

                self.transitions[trans].add(elem.Core())

class LALR1StateTransitionGraphElement(LR1StateTransitionGraphElement):

    def __init__(self, graph, number, elements):
        """
        A State in a LALR(1) automaton.
        """
        super(LALR1StateTransitionGraphElement, self).__init__(graph, number, elements)

        self.lapropagation = []
        self.lageneration = []

    def DeterminePropagationAndGeneration(self):
        """
        Determine where and how the LA entries are generated or
        propagate.

        For a detailed explanation of the algorithm see the Dragon
        Book.
        """

        undef = self.graph.grammar.RequireUndef()

        for item in self.elements:

            item.SetLookahead(frozenset([undef]))
            cls = item.Closure()

            for other in cls:
                symb = other.AfterDot()
                if symb is not None:

                    for trans in self.transitions:
                        if trans.Symbol() == symb:
                            stateTo = trans.State()

                            for itemTo in stateTo.Elements():

                                if other.TransitionsTo(itemTo):

                                    for la in other.Lookahead():

                                        if la is undef:
                                            # print "Propagate", self.Number(), stateTo.Number(), item, "->", itemTo
                                            self.lapropagation.append((item, itemTo))

                                        else:
                                            # print "Generate", itemTo, ":", la, "(", item, ")"
                                            stateTo.lageneration.append((itemTo, la))

            item.SetLookahead(frozenset())

    def Generate(self):
        """
        Do the LA entry generation.
        """
        for item, symb in self.lageneration:
            newLa = set(item.Lookahead())
            newLa.add(symb)
            item.SetLookahead(newLa)

    def Propagate(self):
        """
        Do the LA entry propagation.
        """
        propagated = False
        for item, to in self.lapropagation:
            newLa = to.Lookahead() | item.Lookahead()

            if newLa != to.Lookahead():
                to.SetLookahead(newLa)
                propagated = True

        return propagated

class LexingAutomatonState(metaclass=abc.ABCMeta):

    def __init__(self):
        self.transitions = {}
        self.action = None
        self.priority = None

    @abc.abstractmethod
    def Move(self, chr):
        """
        Get the states reached.
        """
        pass

    @abc.abstractmethod
    def AddTransition(self, chr, state):
        pass

    def AddTransitions(self, chrs, state):
        for chr in chrs:
            self.AddTransition(chr, state)

    def Transitions(self):
        return self.transitions.items()

    def SetAction(self, priority, action):
        self.action = action
        self.priority = priority

    def GetAction(self):
        return self.action

    def Priority(self):
        return self.priority

class NFAState(LexingAutomatonState):


    def Move(self, char):
        """
        Get the set of states reached by the transition on char.
        """
        return self.transitions.get(char, set())

    def EpsilonClosure(self, visited=None):
        closure = set([self])

        if visited is None:
            visited = frozenset()

        if self in visited:
            return closure

        closure |= self.transitions.get('', set())

        nc = set()
        for elem in closure:
            nc |= elem.EpsilonClosure(visited | frozenset([self]))

        return closure | nc

    def AddTransition(self, char, state):
        if char not in self.transitions:
            self.transitions[char] = set()

        self.transitions[char].add(state)

class DFAState(LexingAutomatonState):

    def Move(self, chr):
        """
        Get the transition on character for a DFA.
        """
        return self.transitions[chr]

    def AddTransition(self, char, state):
        if char in self.transitions:
            raise CantHappen()

        self.transitions[char] = state

class RegexAST(object):
    """An AST representing a regular expression."""

    def NFA(self):
        raise NotImplementedError()

class CharacterRegex(RegexAST):

    def __init__(self, chars):
        self.chars = frozenset(chars)

    def __str__(self):
        return "CharacterRegex({})".format(list(self.chars))

    def NFA(self):
        start = NFAState()
        end = NFAState()

        start.AddTransitions(self.chars, end)

        return start, end

class SequenceRegex(RegexAST):

    def __init__(self, regex1, regex2):
        self.regex1, self.regex2 = regex1, regex2

    def __str__(self):
        return "SequenceRegex(%s, %s)" % (str(self.regex1), str(self.regex2))

    def NFA(self):
        nfa1s, nfa1e = self.regex1.NFA()
        nfa2s, nfa2e = self.regex2.NFA()

        # chain the end of the first automaton to the start of the
        # second one with an epsilon transition
        nfa1e.AddTransition('', nfa2s)

        return nfa1s, nfa2e

class OptionRegex(RegexAST):

    def __init__(self, regex):
        self.regex = regex

    def __str__(self):
        return "OptionRegex(%s)" % str(self.regex)

    def NFA(self):

        nfas, nfae = self.regex.NFA()

        nfas.AddTransition('', nfae)

        return nfas, nfae

class RepeatorRegex(RegexAST):

    def __init__(self, regex):
        self.regex = regex

    def __str__(self):
        return "RepeatorRegex(%s)" % str(self.regex)

    def NFA(self):
        nfas, nfae = NFAState(), NFAState()
        nfars, nfare = self.regex.NFA()

        nfas.AddTransition('', nfae)
        nfas.AddTransition('', nfars)
        nfare.AddTransition('', nfars)
        nfare.AddTransition('', nfae)

        return nfas, nfae

class OrRegex(RegexAST):

    def __init__(self, regex1, regex2):
        self.regex1, self.regex2 = regex1, regex2

    def __str__(self):
        return "OrRegex(%s, %s)" % (str(self.regex1), str(self.regex2))

    def NFA(self):

        nfa1s, nfa1e = self.regex1.NFA()
        nfa2s, nfa2e = self.regex2.NFA()
        start, end = NFAState(), NFAState()

        start.AddTransition('', nfa1s)
        start.AddTransition('', nfa2s)

        nfa1e.AddTransition('', end)
        nfa2e.AddTransition('', end)

        return start, end

class RegexSyntaxError(Exception):
    pass

class Regex(object):
    """A regular expression with an NFA representation."""

    ESCAPES = {
        'n' : '\n',
        't' : '\t',
        'f' : '\f',
        'v' : '\v',
        's' : ' \n\t\v\r\f',
        'd' : '0123456789',
        'w' : 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ013456789_'
        }

    def ParseEscape(self, iterator):
        char = next(iterator)

        if char == 'x':
            string = ''
            string += next(iterator)
            string += next(iterator)
            return set(chr(int(string, base=16)))

        return set(self.ESCAPES.get(char, char))

    def ParseChrClass(self, iterator):
        try:
            first = True
            chars = set()
            prev = None
            group = False
            negate = False

            while True:
                char = next(iterator)
                if first:
                    first = False
                    if char == '^':
                        negate = True
                        chars = set(chr(i) for i in range(256))
                        continue

                if char == ']':
                    return chars

                elif char == '-':
                    if prev is None:
                        raise StopIteration()
                    else:
                        group = True
                    continue

                cset = set()
                if char == '\\':
                    cset |= self.ParseEscape(iterator)
                else:
                    cset |= set(char)

                if group:
                    if len(cset) != 1:
                        raise StopIteration()

                    if len(prev) != 1:
                        raise StopIteration()

                    # use tuple unpacking to elegantly extract the
                    # single values from the sets
                    c, = cset
                    p, = prev

                    for char in range(ord(p) + 1, ord(c)):
                        cset.add(chr(char))

                    group = False

                prev = cset

                if negate:
                    chars -= cset
                else:
                    chars |= cset

        except StopIteration:
            raise RegexSyntaxError("unclosed character class")

    def ParseBrace(self, iterator):
        res = ['']
        # we rely on the fact, that (iter(iterator) is iterator)
        # which is specified in the python stdlib docs
        for chr in iterator:
            if chr == '}':
                res[-1] = res[-1].strip()
                try:
                    res = [int(entry) if entry else None for entry in res]
                except ValueError:
                    if len(res) != 1:
                        raise RegexSyntaxError("comma in named regex reference")
                    return (6, res[0])
                else:
                    return (7, res)
            elif chr == ',':
                res[-1] = res[-1].strip()
                res.append('')
            else:
                res[-1] += chr

        raise RegexSyntaxError("unclosed brace expression")

    def lex(self):
        # tokens: CHR ([...], \...,.) - 0, OP (+ ? *) - 1, ( - 2, | - 3, ) - 4
        tokens = []

        iterator = iter(self.regex)
        try:
            while True:
                char = next(iterator)
                if char == '\\':
                    tokens.append((0, self.ParseEscape(iterator)))
                elif char == '[':
                    tokens.append((0, self.ParseChrClass(iterator)))
                elif char == ']':
                    raise RegexSyntaxError("single closing bracket")
                elif char in ('+', '?', '*'):
                    tokens.append((1, char))
                elif char == '|':
                    tokens.append((3, '|'))
                elif char == '(':
                    tokens.append((2, '('))
                elif char == ')':
                    tokens.append((4, ')'))
                elif char == '.':
                    tokens.append((0, set(chr(i) for i in range(0,256)) - set('\n')))
                elif char == '{':
                    tokens.append(self.ParseBrace(iterator))
                elif char == '}':
                    raise RegexSyntaxError("single closing brace")
                else:
                    tokens.append((0, set(char)))

        except StopIteration:
            tokens.append((5, ''))
            return tokens

    def Parse(self, bindings):

        tokens = iter(self.lex())
        current_token = next(tokens)

        def ParseOr():
            nonlocal current_token

            first = ParseChain()
            if first is None:
                first = CharacterRegex([''])

            if current_token[0] == 3:
                current_token = next(tokens)
                second = ParseOr()
                return OrRegex(first, second)

            return first


        def ParseChain():
            first = ParseOp()
            if first is None:
                return None
            else:
                second = ParseChain()
                if second is None:
                    return first
                else:
                    return SequenceRegex(first, second)

        def ParseOp():
            nonlocal current_token

            basic = ParseBasic()
            if basic is None:
                return None

            token, lexeme = current_token
            if token == 1:
                if lexeme == '+':
                    res = SequenceRegex(basic, RepeatorRegex(basic))

                elif lexeme == '*':
                    res = RepeatorRegex(basic)

                elif lexeme == '?':
                    res = OptionRegex(basic)

                else:
                    # this is a bug in the implementation!
                    raise CantHappen()
                current_token = next(tokens)
            elif token == 7:
                try:
                    start = lexeme[0]
                    if start <= 0:
                        raise ValueError

                    if len(lexeme) == 1:
                        # exactly {n} times
                        res = basic
                        for i in range(1, start):
                            res = SequenceRegex(basic, res)
                    elif len(lexeme) == 2:
                        stop = lexeme[1]

                        if stop is not None:
                            # between {n, m} times
                            if stop <= 0:
                                raise ValueError

                            res = basic
                            for i in range(1, start):
                                res = SequenceRegex(basic, res)

                            if stop > start:
                                opt_basic = OrRegex(basic, CharacterRegex(['']))
                                for i in range(start, stop):
                                    res = SequenceRegex(res, opt_basic)
                            elif start == stop:
                                res = res1
                            else:
                                raise RegexSyntaxError("m greater than n in {m,n}-style repeator")

                        else:
                            # more than {n, } times
                            res = RepeatorRegex(basic)
                            for i in range(start):
                                res = SequenceRegex(basic, res)
                    else:
                        raise RegexSyntaxError("too many numbers in repetition operator")
                except ValueError:
                    raise RegexSyntaxError("item in brace repitition operator not a positive integer")
                current_token = next(tokens)
            else:
                res = basic

            return res

        def ParseBasic():
            nonlocal current_token
            token, lexeme = current_token

            if token == 0:
                res = CharacterRegex(lexeme)
                current_token = next(tokens)
                return res

            elif token == 2:
                current_token = next(tokens)
                res = ParseOr()
                if current_token[0] != 4:
                    raise RegexSyntaxError("missing closing paren")

                current_token = next(tokens)
                return res
            elif token == 6:
                try:
                    res = bindings[lexeme]
                except KeyError:
                    raise RegexSyntaxError("unbound named pattern {{{}}}".format(lexeme))
                current_token = next(tokens)
                return res
            else:
                return None

        res = ParseOr()

        token, lexeme = current_token
        if token == 1:
            raise RegexSyntaxError("missing argument for '{}' operator".format(lexeme))
        elif token == 4:
            raise RegexSyntaxError("superfluous closing paren")
        elif token == 5: # parsed up to EOF, we are happy
            return res
        else:
            raise CantHappen()

    def __init__(self, regex, bindings=None):
        self.regex = regex
        self.ast = self.Parse(bindings or {})

    def NFA(self):
        return self.ast.NFA()

class LexerConstructor(object):
    """
    Manages the steps of constructing the lexer, taking care of
    constructing the lextables for the different states and then
    applying the further manipulations to all of them.
    """

    def __init__(self, lexerSpec, logger):
        self.logger = logger

        self.nfas = {}
        self.dfas = {}
        self.lextables = {}

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
        for condition in lexerSpec.InitialConditions():
            self.nfas[condition] = LexingNFA(lexerSpec.Lexer(), condition, inlineTokens, logger)

    def ConstructDFAs(self):
        for condition, nfa in self.nfas.items():
            self.dfas[condition] = nfa.CreateDFA()

    def DropNFA(self):
        """
        Drop the nfas if they are no longer needed to spare memory
        """
        self.nfas = None


    def Optimize(self):
        for dfa in self.dfas.values():
            dfa.Optimize()

    def CreateLexTables(self):
        for cond, dfa in self.dfas.items():
            self.lextables[cond] = dfa.CreateLexTable()

    def DropDFA(self):
        """
        Drop the dfas if they are no longer needed to spare memory
        """
        self.dfas = None

    def ConstructEquivalenceClasses(self):
        for lextable in self.lextables.values():
            lextable.ConstructEquivalenceClasses()

    def Get(self):
        for cond, lextable in self.lextables.items():
            yield tuple([cond] + list(lextable.Get()))

    def PrintTables(self):
        for key, table in self.lextables.items():
            print("-----------------", key.Name(), "--------------------")
            table.Print()



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
            dfaStates[si].SetAction(None, SelectAction(si))

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
                    dfaStates[newState].SetAction(None, SelectAction(newState))

                    if len(newState) == 0:
                        # this is the error state (empty set of NFA states)
                        # if we get here nothing can match anymore, therefore
                        # we can retrieve our longest match
                        dfaStates[newState].SetAction(None, GetMatch())

                dfaStates[cur].AddTransition(char, dfaStates[newState])

        return LexingDFA(dfaStates, si)


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
        return tuple(self.GroupOfState(state.Move(chr(char))) for char in range(0,256))

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
        states = []
        newstates= {}
        newstart = None

        # create the new states
        for i in range(0, len(self.groups)):
            states.append(DFAState())
            newstates[states[-1]] = i

            if start in self.groups[i]:
                newstart = states[i]

        # link the new states
        for i in range(0, len(self.groups)):

            representative = self.groups[i][0]

            states[i].SetAction(None, representative.GetAction())

            for char in range(256):
                states[i].AddTransition(chr(char), states[self.GroupOfState(representative.Move(chr(char)))])

        return newstart, newstates

class LexingDFA(object):

    def __init__(self, states, start):
        self.states = dict()

        # remove the unnecassary NFA state information
        i = 0
        for state in states.values():
            self.states[state] = i
            i += 1

        self.start = states[start]

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
        lextable = [tuple([] for i in range(0,256)) for i in range(len(self.states))]
        actions = [None for i in range(len(self.states))]
        for state in self.states:

            actions[self.states[state]] = state.GetAction()

            mylist = lextable[self.states[state]]

            for char, nstate in state.Transitions():
                mylist[ord(char)].append(self.states[nstate])

        return Lextable(lextable, self.states[self.start], actions)

class Lextable(object):

    def __init__(self, table, start, actionlist):
        self.table = table
        self.start = start
        self.actions = actionlist
        self.mapping = None


    def Get(self):
        return self.table, self.start, self.actions, self.mapping

    def ConstructEquivalenceClasses(self):
        i = 0
        classes = [[char for char in range(0,256)]]

        for line in self.table:

            newclasslist = []
            for cls in classes:
                newclasses = dict()
                for char in cls:
                    state = line[char][0]
                    if state not in newclasses:
                        newclasses[state] = []

                    newclasses[state].append(char)
                newclasslist += list(newclasses.values())

            classes = newclasslist

        self.mapping = [None for j in range(0,256)]
        mapping = self.mapping
        i = 0
        for cls in classes:
            for terminal in cls:
                mapping[terminal] = i
            i += 1

        newtable = []
        for line in self.table:
            newtable.append([])
            my = newtable[-1]
            for cls in classes:
                my.append(line[cls[0]])
        self.table = newtable


    def Print(self):
        print("start: %d\n" % self.start)

        for num, action in enumerate(self.actions):
            print(num, str(action))

        if not self.mapping:
            print("\n    ", end=' ')

        # print the characters
        for i in range(32, 128):
            if self.mapping:
                print(chr(i), str(self.mapping[i]))
            else:
                print(chr(i).center(2), end=' ')

        if self.mapping:
            print("\n    ", end=' ')


        printRange = range(32, 128)

        if self.mapping:
            printRange = range(len(self.table[0]))
            for i in printRange:
                print(str(i).center(2), end=' ')

        print("")
        i = 0
        for state in self.table:
            print(str(i).center(2), "-", end=' ')
            for a in printRange:
                print(str(state[a][0]).center(2), end=' ')
            print("")
            i+=1


class LexActionToCode(LexingActionVisitor):

    def __init__(self, symtable):
        super(LexActionToCode, self).__init__()
        self.symtable = symtable

    def VisitDebug(self, action):
        return "print(%s, repr(text))" % repr(action.Text())

    def VisitRestart(self, action):
        return "return None"

    def VisitToken(self, action):
        return "return {:d}".format(self.symtable[action.Name()].Number())

    def VisitGetMatch(self, action):
        # this is never actually called!
        assert False
        return "pass"

    def VisitBegin(self, action):
        return "self.nextCond[-1] = {:d}".format(action.State().Number())

    def VisitPush(self, action):
        return "self.nextCond.append({:d})".format(action.State().Number())

    def VisitPop(self, action):
        return "self.nextCond.pop()"

    def VisitList(self, actionList):
        if actionList.List():
            res = ''
            for action in actionList.List():
                res += action.Accept(self)
                res += '\n'
            return res[:-1]
        else:
            return 'pass'

    def VisitContinue(self, action):
        return 'self.state = self.start'

    def VisitFunction(self, action):
        return '{}(self, text, position)'.format(action.name)

class LRActionToLRTableEntry(LRActionVisitor):

    def __init__(self, symtable):
        self.symtable = symtable

    def VisitShift(self, shift):
        return (0, shift.Next())

    def VisitReduce(self, red):
        return (1, red.Red())


class Writer(object):

    def Deduplicate(self, iterable):
        ded = []
        indices = []
        mapping = {}

        for entry in iterable:
            if entry not in mapping:
                var = len(ded)
                ded.append(entry)
                mapping[entry] = var

            indices.append(mapping[entry])

        return ded, indices

    def __init__(self, parser_file, logger, lines, trace, deduplicate, python3, debug=False):
        self.logger = logger

        self.parser_file = parser_file
        self.lines = lines
        self.trace = trace
        self.deduplicate = deduplicate
        self.python3 = python3
        self.debug = debug

    def WriteHeader(self, header):
        self.parser_file.write("""# this file was generated automagically by pyLR1
# do not edit, if you want to modify the parser, adapt the grammar file

import mmap
""")

        for headline in header:
            self.parser_file.write(headline + "\n")

    def TableStrings(self, helper, tableTuple):
        tablehelper = ""
        tablestr = "("

        if self.deduplicate:
            ded, indices = self.Deduplicate(tableTuple)

            tablehelper = helper + ' = (' + ',\n'.join(str(entry).replace(' ', '') for entry in ded) + (',)' if len(ded) == 1 else ')')
            tablestr += ','.join(helper + '[%d]' % i for i in indices)
            if len(indices) == 1:
                tablestr += ','
        else:
            for state in tableTuple:
                tablestr += str(state).replace(' ', '')
                tablestr += ",\n"

        tablestr += ")"

        return tablehelper, tablestr

    def WriteAST(self, ast, symtable):
        if not ast.used:
            return

        classes = {}

        # collect information on the classes
        # and attach the actions
        for symbol in symtable.values():
            if symbol.SymType() == Syntax.META:
                if symbol.Symbol().Name() in ast.lists:
                    # trivial list creation ... could be more intelligent
                    # at guessing how to do this
                    for prod in symbol.Symbol().Productions():
                        if prod.GetAction():
                            continue
                        positions = []
                        i = 0
                        for symb in prod:
                            i += 1
                            if not symb.IsSToken():
                                positions.append(i)

                        if len(positions) == 0:
                            prod.SetAction('$$.sem = []')
                        elif len(positions) == 1:
                            prod.SetAction('$$.sem = [$%d.sem]' % tuple(positions))
                        elif len(positions) == 2:
                            prod.SetAction('$$.sem = $%d.sem; $$.sem.append($%d.sem)' % tuple(positions))
                        else:
                            self.logger.error("Erroneous %list target: more items than can be enlisted")
                            raise Exception()
                else:
                    for prod in symbol.Symbol().Productions():
                        if prod in ast.bindings:
                            args = []
                            i = 0
                            action = "$$.sem = " + ast.bindings[prod] + "("
                            if self.lines:
                                action += "$$.pos, "

                            for symb in prod:
                                i += 1
                                if not symb.IsSToken():
                                    action += '$%d.sem, ' % i
                                    if symb.Name() in args:
                                        args.append('%s%d' % (symb.Name(), args.count(symb.Name())))
                                    else:
                                        args.append(symb.Name())
                            action += ")"
                            classes[ast.bindings[prod]] = args
                            prod.SetAction(action)

        self.parser_file.write("""
class AST(object):
    def Accept(self, visitor):
        raise NotImplementedError()
""")

        if self.lines:
            self.parser_file.write("""
    def Pos(self):
        return self.pos
""")

        self.parser_file.write("""
class %s(object):
    def Visit(self, ast):
        return ast.Accept(self)
""" % (ast.visitor,))

        for name in classes:
            self.parser_file.write("""
    def Visit%s(self, node):
        raise NotImplementedError()
""" % (name,))

        basearg = ['self']
        if self.lines:
            basearg.append('pos')

        for name, args in classes.items():
            self.parser_file.write("""
class %s(AST):
    def __init__(""" % (name,) + ", ".join(basearg + args))

            self.parser_file.write("):")
            if len(args) == 0:
                self.parser_file.write("""
        pass""")

            if self.lines:
                self.parser_file.write("""
        self.pos = pos""")

            for arg in args:
                self.parser_file.write("""
        self.%s = %s""" % (arg, arg))

            for arg in args:
                self.parser_file.write("""
    def get_%s(self):
        return self.%s
""" % (arg, arg))

            self.parser_file.write("""
    def Accept(self, visitor):
        return visitor.Visit%s(self)
""" % (name,))

    def WriteLexer(self, lexer, symtable):

        if self.python3:
            extract = '.decode("UTF-8")'
            baccess = "buffer[cur_pos]"
        else:
            extract = ''
            baccess = "ord(buffer[cur_pos])"


        data = []
        action_table = {}

        for cond, table, start, actions, mapping in lexer.Get():

            lextablehelper, lextablestr = \
                self.TableStrings("ltd%d" % cond.Number(),
                  tuple(tuple(a[0] for a in state)for state in table))

            # create the string representing the actions
            action_vector = []
            for action in actions:
                if action is None:
                    action_vector.append('None')
                elif action == GetMatch():
                    action_vector.append('-1')
                else:
                    if action not in action_table:
                        action_table[action] = len(action_table)
                    action_vector.append('{}'.format(action_table[action]))
            actionmapstr = "({})".format(','.join(action_vector))

            mappingstr = ""
            if mapping:
                # create the string mapping
                lookup = "mapping[" + baccess + "]"
                mappingstr = '({})'.format(','.join(map(str, mapping)))

            data.append((cond, start, actionmapstr, mappingstr, lextablehelper, lextablestr))
        data.sort(key=lambda x: x[0].Number())

        actionstr = ','.join('self.action{:d}'.format(i) for i in range(len(action_table)))
        actionstr = ('({},)' if len(action_table) == 1 else '({})').format(actionstr)

        startstr = '('
        mappingstr = '('
        actionmapstr = '('
        lextablestr = '('
        lextablehelper = ''

        for cond, start, astr, mstr, lthstr, ltstr in data:
            startstr += str(start) + ','
            mappingstr += mstr + ',\n'
            actionmapstr += astr + ',\n'
            lextablestr +=   ltstr + ',\n'
            lextablehelper += '    ' + lthstr + '\n'

        lextablestr += ')'
        actionmapstr += ')'
        mappingstr += ')'
        startstr += ')'

        linesPositionClass = ''
        linesCount = "position = None"
        eofPosition = "None"

        lexerDebugData = ""
        if self.debug:
            token_names = []
            token_numbers = []
            symtypes = frozenset([Syntax.TERMINAL, Syntax.EOF, Syntax.ERROR])
            for key, value in symtable.items():
                if value.SymType() in symtypes:
                    token_names.append("{token}: {key}".format(key=repr(key),
                                                               token=value.Number()))
                    token_numbers.append("{key}: {token}".format(key=repr(key),
                                                                 token=value.Number()))

            lexerDebugData = r"""
    TOKEN_NAMES = {{{}}}
    TOKEN_NUMBERS = {{{}}}
""".format(','.join(token_names), ','.join(token_numbers))

        if self.lines:
            linesPositionClass = """class Position(object):
    def __init__(self, file, line0, col0, line1, col1):
        self.file  = file
        self.line0 = line0
        self.col0  = col0
        self.line1 = line1
        self.col1  = col1

    def Add(self, oth):
        return Position(self.file, self.line0, self.col0, oth.line1, oth.col1)

    def __str__(self):
        return "%s Line %d:%d - %d:%d" % (self.file, self.line0, self.col0, self.line1, self.col1)
"""

            linesCount = r"""
            line0 = self.line
            sol0 = self.start_of_line
            self.line += text.count('\n')
            sol1 = text.rfind('\n')
            if sol1 != -1:
                self.start_of_line = self.root + sol1 + 1
            position = Position(self.filename,
                                line0,
                                self.root - sol0,
                                self.line,
                                pos - self.start_of_line)
"""
            eofPosition = r"""Position(self.filename, self.line, 0, self.line, 0)"""

        self.parser_file.write(r"""class GotToken(Exception):
    pass

""" + linesPositionClass + r"""

class Lexer(object):

    starts = """ + startstr + r"""
    mappings = """ + mappingstr + r"""
""" + lextablehelper + r"""
    tables  = """ + lextablestr + lexerDebugData + r"""
    actionmap = """ + actionmapstr + """

    @classmethod
    def from_filename(cls, codefile, **kwargs):
        code = open(codefile, 'rb')
        res = cls(code, filename=codefile, **kwargs)
        code.close()
        return res

    def __init__(self, code, mmap_file=True, filename='<>', string=False):
        '''
        A DFA-based Lexer.

        The `lex` method returns the tokens from `code`, if
        `mmap_file` is *True* (the default) the lexer will try to
        `mmap` the file for lexing.

        `filename` gives the file name to display on errors.

        If `string` is *True* `code` is considered to be the string of
        input to parse. (py3 note: this should be a buffer)
        '''

        self.filename = filename

        if string:
            self.buffer = code
            self.size = len(self.buffer)
        else:
            if mmap_file:
                try:
                    self.buffer = mmap.mmap(code.fileno(), 0, access=mmap.ACCESS_READ)
                    self.size = self.buffer.size()
                except mmap.error:
                    # we could not mmap the file: perhaps warn, but open it
                    # through a FileBuffer
                    mmap_file = False

            if not mmap_file:
                # for now: just slurp the file, sorry if it is large,
                # a tty or a pipe -> TODO
                self.buffer = code.read()
                self.size = len(self.buffer)

        self.root = 0
        self.nextCond = [2]
        self.token_push_back = []
        self.line = 1
        self.start_of_line = 0
        self.actions = """ + actionstr + r"""

    def push_back(self, token):
        self.token_push_back.append(token)

    def lexAll(self):
        tokens = []
        while True:
            type, text, pos = self.lex()
            if type == """ + str(symtable["$EOF"].Number()) + r""":
                return tokens
            tokens.append((type, text, pos))

    def lex(self):
        if self.token_push_back:
            return self.token_push_back.pop()

        cond = self.nextCond[-1]
        state = self.starts[cond]
        size, table, cactions, mapping, buffer = self.size, self.tables[cond], self.actionmap[cond], self.mappings[cond], self.buffer
        actionvec = self.actions
        cur_pos = self.root
        if cactions[state] is not None:
            action = cur_pos, actionvec[cactions[state]]
        else:
            action = None
        try:
            while cur_pos != size:
                state = table[state][""" + lookup + """]
                cur_pos += 1
                if cactions[state] is None:
                    pass
                elif cactions[state] < 0:
                    raise GotToken
                else:
                    action = (cur_pos, actionvec[cactions[state]])
            raise GotToken
        except GotToken:
            if action is None:
                if cur_pos == self.root:
                    return ("""
           + "{0}, {1}, {2}".format(symtable["$EOF"].Number(), "''", eofPosition) +
                               r""")
                else:
                    action = cur_pos, self.error_action
            pos, faction = action

            text = self.buffer[self.root:pos]""" + extract + r"""

            """ + linesCount + r"""
            name = faction(text, position)

            if self.nextCond[-1] == 2:
                self.nextCond[-1] = 0

            if self.nextCond[-1] == 0 and text and text[-1] == '\n':
                self.nextCond[-1] = 1
            elif self.nextCond[-1] == 1 and text and text[-1] != '\n':
                self.nextCond[-1] = 0

            self.root = pos

            if name is None:
                return self.lex()
            else:
                return (name, text, position)
""")

        lexActionGen = LexActionToCode(symtable)

        for action, number in action_table.items():
            self.parser_file.write("""
    def action%d(self, text, position):
""" % (number,))

            code = lexActionGen.Visit(action).split('\n')
            for line in code:
                self.parser_file.write("        " + line + "\n")

        self.parser_file.write(r"""
    def error_action(self, text, position):
        return """ + "{}".format(symtable["$ERROR"].Number()) + r"""
""")

    def WriteParser(self, parseTable, symtable):
        # when there is no parser specified parseTable is None
        # and we don't write a parser to the output file
        if parseTable is None:
            return

        linesPosAddition = ""
        linesNullPos = ""

        if self.lines:
            linesPosAddition = """new.pos = stack[-size].pos.Add(stack[-1].pos)"""
            linesNullPos = "stack[-1].pos = Position('', 0,0,0,0)"

        state_trace = ""

        if self.trace:
            if self.python3:
                state_trace = "print(' '.join(str(entry.state) for entry in stack), '#', str((t,d)) ," + ("self.lexer.TOKEN_NAMES[token]" if self.debug else "token") + ", '\"' + lexeme + '\"')"
            else:
                state_trace = "print stack[-1].state, token lexeme"

        self.parser_file.write("""
class Accept(Exception):
    pass

class StackObject(object):
    def __init__(self, state):
        self.state = state
        self.pos = None
        self.sem = None

class SyntaxError(Exception):
    def __init__(self, message='', position=None):
        self.message = message
        self.position = position

    def __str__(self):
        return '{}:{}'.format(str(self.position), self.message)

class Parser(object):
    # actions from the grammar
""")

        translator = LRActionToLRTableEntry(symtable)

        actionTableHelper, actionTableStr = self.TableStrings("atd", tuple(tuple(translator.Visit(a) if a is not None else (2,0) for a in state) for state in parseTable.Actiontable()))

        gotoTableHelper, gotoTableStr = self.TableStrings("gtd", tuple(tuple(a if a else 0 for a in state) for state in parseTable.Gototable()))

        reductionStr = "("
        i = 0
        for red in parseTable.Rules():
            reductionStr += "(%d,%d,self.action%d),\n" % (len(red), symtable[red.Left().Name()].Number(), i)
            i += 1
        reductionStr += ")"

        self.parser_file.write("""
    # tables
    start = %d""" % parseTable.Start() + """
    """ + actionTableHelper + """
    atable = """ + actionTableStr + """
    """ + gotoTableHelper + """
    gtable = """ + gotoTableStr + """

    # auto generated methods
    def __init__(self, lexer):
        self.lexer = lexer
        self.stack = []
        self.reductions = """ + reductionStr + """

    def Parse(self):
        lexer = self.lexer
        atable = self.atable
        gtable = self.gtable
        stack = self.stack
        reductions = self.reductions
        stack.append(StackObject(self.start))
        """ + linesNullPos + """

        try:
            while True:
                token, lexeme, pos = lexer.lex()
                t, d = atable[stack[-1].state][token]
                """ + state_trace + """
                while t == 1:
                    size, sym, action = reductions[d]
                    state = gtable[stack[-size-1].state][sym]
                    new = StackObject(state)
                    """ + linesPosAddition  + r"""
                    action(new)
                    if size > 0:
                        del stack[-size:]
                    stack.append(new)
                    t, d = atable[stack[-1].state][token]
                    """ + state_trace + """
                if t == 0:
                    new = StackObject(d)
                    new.sem = lexeme
                    new.pos = pos
                    stack.append(new)
                    # action, e.g. a lexcal tie-in

                else:
                    raise SyntaxError(position=stack[-1].pos)
        except Accept:
            return stack[-1].sem
""")
        redNum = 0
        for red in parseTable.Rules():
            text = red.GetAction()
            if not text: text = "pass"
            text = text.replace("$$", "result")
            for i in range(1, len(red) + 1):
                text = text.replace("$%d" % i, "self.stack[-%d]" % (len(red) - i + 1))

            self.parser_file.write("""
    def action%d(self, result):""" % (redNum,))

            for char in text:
                self.parser_file.write(char)
                if char == '\n':
                    # indent two levels: Parser class, current function
                    self.parser_file.write("        ")

            self.parser_file.write("\n")
            redNum += 1


    def WriteFooter(self, footer):
        if footer:
            self.parser_file.write("""
# The following code is copied verbatim from the %footer section of
# the parser specification
""")

        for line in footer:
            self.parser_file.write(line)


    def Write(self, syntax, parsetable, lextable):

        self.WriteHeader(syntax.Header())

        self.WriteAST(syntax.ASTInfo(), syntax.SymTable())

        self.WriteLexer(lextable, syntax.SymTable())

        self.WriteParser(parsetable, syntax.SymTable())

        self.WriteFooter(syntax.Footer())

class CountingLogger(logging.getLoggerClass()):

    class ErrorsOccured(Exception):
        pass

    def __init__(self, name):
        """
        A logger that counts errors.

        `name` is passed on.
        """
        super().__init__(name)
        self.errors = 0

    def raiseOnErrors(self):
        """
        Raise the exception `ErrorsOccured` of there were errors.
        """
        if self.errors > 0:
            raise CountingLogger.ErrorsOccured()

    def exitOnErrors(self, exitCode=1):
        """
        Exit if there were errors.
        """
        sys.exit(exitCode)

    def loggedErrors(self):
        """
        Return true if there were errors.
        """
        return bool(self.errors)

    def error(self, msg, *args, **kwargs):
        self.errors += 1
        super().error(msg, *args, **kwargs)

if __name__ == '__main__':

    arg_parser = argparse.ArgumentParser(
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description="A pure python LALR(1)/LR(1) parser generator and lexer generator.")

    arg_parser.add_argument("-o", "--output-file",
                            dest="ofile",
                            help="Set the output file to OFILE [default: derived from infile]")

    arg_parser.add_argument("-l", "--line-tracking",
                            dest="lines",
                            action='store_true',
                            default=False,
                            help="Enable line tracking in the generated parser")

    arg_parser.add_argument("-L", "--lalr",
                            dest="lalr",
                            action='store_true',
                            default=False,
                            help="Generate a LALR(1) parser instead of a LR(1) parser")

    arg_parser.add_argument("-g", "--print-graph",
                            dest="graph",
                            action='store_true',
                            default=False,
                            help="Print the LR state graph to stdout")

    arg_parser.add_argument("--print-lextable",
                            action='store_true',
                            default=False,
                            help="Print the lextables to stdout")

    arg_parser.add_argument("-D", "--not-deduplicate",
                            dest="deduplicate",
                            action='store_false',
                            default=True,
                            help="Compress tables by reusing identical lines")

    arg_parser.add_argument("-d", "--debug",
                            dest='debug',
                            action='store_true',
                            default=False,
                            help="Write debug information to the generated file")

    arg_parser.add_argument("-f", "--fast",
                            dest="fast",
                            action='store_true',
                            default=False,
                            help="Fast run: generates larger and possibly slower parsers, but takes less time")

    arg_parser.add_argument("-q", "--quiet",
                            dest="quiet",
                            action='store_true',
                            default=False,
                            help="Print less info")

    arg_parser.add_argument("-T", "--trace",
                            dest="trace",
                            action='store_true',
                            default=False,
                            help="Generate a parser that prints out a trace of its state")

    py_version = arg_parser.add_mutually_exclusive_group()

    py_version.add_argument("-3", "--python3",
                            dest="python3",
                            action='store_true',
                            default=True,
                            help="Generate python3 compatible parser [default]")

    py_version.add_argument("-2", "--python2",
                            dest="python3",
                            action='store_false',
                            default=True,
                            help="Generate python2 compatible parser")


    arg_parser.add_argument("infile",
                            help="The parser specification to process")

    args = arg_parser.parse_args()

    # determine the name of the output file if it is not given
    # explicitly
    if not args.ofile:
        m = re.match(r'(.*\.py)LRp?$', args.infile)
        if m:
            args.ofile = m.group(1)
        elif '.' not in args.infile:
            args.ofile = args.infile + '.py'

    # setup logging for error reporting
    logging.basicConfig(format="{msg}", style="{")
    logging.setLoggerClass(CountingLogger)
    logger = logging.getLogger('pyLR1')
    logger.setLevel(logging.WARNING if args.quiet else logging.INFO)

    # parse the input file
    try:
        infile = open(args.infile, 'rt')
    except IOError as e:
        print(str(e), file=sys.stderr)
        sys.exit(1)

    p = Parser(infile, logger)
    syn = p.Parse()
    del p
    infile.close()

    if logger.loggedErrors():
        sys.exit(1)

    # construct the parser
    parseTable = None

    # XXX: should we be more strict here and not generate a parser
    # when no %parser section is present but error on an empty
    # %parser section
    if syn.Start() is not None:
        if args.lalr:
            graph = LALR1StateTransitionGraph(syn, logger)
        else:
            graph = LR1StateTransitionGraph(syn, logger)

        graph.Construct()

        if args.graph:
            for state in graph.states:
                print(str(state))

        termsyms = frozenset([Syntax.TERMINAL, Syntax.EOF, Syntax.ERROR])
        parseTable = graph.CreateParseTable(
            syn.SymTableMap(filt=lambda x: x.SymType() in termsyms,
                            value=lambda x: x.Number()),
            syn.SymTableMap(filt=lambda x: x.SymType() == Syntax.META,
                            value=lambda x: x.Number())
            )
        graph.ReportNumOfConflicts()
        del graph
    else:
        # generate the tokens required by the parser
        # and used for special lexer conditions
        syn.RequireEOF()

    # construct the lexer
    lexer = LexerConstructor(syn, logger)

    lexer.ConstructDFAs()
    lexer.DropNFA()

    if not args.fast:
        lexer.Optimize()

    lexer.CreateLexTables()
    lexer.DropDFA()

    if args.print_lextable:
        lexer.PrintTables()

    if not args.fast:
        lexer.ConstructEquivalenceClasses()

    if logger.loggedErrors():
        sys.exit(1)

    # write lexer and parser
    try:
        with tempfile.TemporaryFile(mode="w+t") as temp_gen:
            writer = Writer(temp_gen, logger,
                            lines=args.lines,
                            trace=args.trace,
                            deduplicate=args.deduplicate,
                            debug=args.debug,
                            python3=args.python3)

            writer.Write(syn, parseTable, lexer)

            if logger.loggedErrors():
                print("error: ", e, file=sys.stderr)
                sys.exit(1)

            with open(args.ofile, "wt") as fo:
                temp_gen.seek(0)
                shutil.copyfileobj(temp_gen, fo)
    except Exception as e:
        print("error: ", e, file=sys.stderr)
        sys.exit(1)
