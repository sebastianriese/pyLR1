#!/usr/bin/env python3
"""
Parse parser and lexer specifications and create DFA lexers
and LR(1) or LALR(1) parsers from them.
"""

# Copyright 2009, 2010, 2012 Sebastian Riese

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
        self.number = number
        self.assoc = Production.NONE, 0
        self.text = ""

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

    # important note: this number is completely independet of the
    # number used to represent  the production in the parse table!
    # This one is  used  exclusivley to resolve  conflicts in the
    # parse  tables  (earlier  declaration  ->  higer  precedence)
    def NumberInFile(self):
        return self.number

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

        if self.AfterDot() is None:
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
        raise Exception("Can't happen")

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

class LexingActionVisitor(object):

    def Visit(self, action):
        return action.Accept(self)

    def VisitDebug(self, action):
        pass

    def VisitRestart(self, action):
        pass

    def VisitToken(self, action):
        pass

    def VisitGetMatch(self, action):
        pass

    def VisitList(self, action):
        pass

    def VisitBegin(self, action):
        pass

    def VisitContinue(self, action):
        pass

class LexingAction(object):
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
        return reduce(operator.__xor__,
                      map(hash, self.__dict__),
                      id(self.__class__))

class Debug(LexingAction):

    def __init__(self, text):
        super(Debug, self).__init__()
        self.text = text

    def __str__(self):
        return "Debug(" + repr(self.text) + ")"

    def __eq__(self, other):
        return self.__class__ == other.__class__ \
            and self.text == other.text

    def __hash__(self):
        return hash(self.text)

    def Text(self):
        return self.text

    def Accept(self, visitor):
        return visitor.VisitDebug(self)

class List(LexingAction):

    def __init__(self, lst = None):
        super(List, self).__init__()
        self.list = lst
        if self.list is None:
            self.list = []

    def __str__(self):
        return "List([" + ", ".join(map(str, self.list)) + "])"

    def Append(self, action):
        self.list.append(action)

    def List(self):
        return self.list

    def Accept(self, visitor):
        return visitor.VisitList(self)

class Begin(LexingAction):

    def __init__(self, state):
        super(Begin, self).__init__()
        self.state = state

    def __repr__(self):
        return "Begin(%s)" % self.state

    def Accept(self, visitor):
        return visitor.VisitBegin(self)

    def State(self):
        return self.state

class Restart(LexingAction):

    def __init__(self):
        super(Restart, self).__init__()

    def __repr__(self):
        return "Restart()"

    def Accept(self, visitor):
        return visitor.VisitRestart(self)

class Continue(LexingAction):

    def __init__(self):
        super(Continue, self).__init__()

    def __repr__(self):
        return "Continue()"

    def Accept(self, visitor):
        return visitor.VisitContinue(self)

class Token(LexingAction):

    def __init__(self, name):
        super(Token, self).__init__()
        self.name = name

    def __repr__(self):
        return "Token('%s')" % self.name

    def Name(self):
        return self.name

    def Accept(self, visitor):
        return visitor.VisitToken(self)

class GetMatch(LexingAction):

    def __init__(self):
        super(GetMatch, self).__init__()

    def __repr__(self):
        return "GetMatch()"

    def Accept(self, visitor):
        return visitor.VisitGetMatch(self)

class Parser(object):
    ast_re = re.compile(r"%ast\s*$")
    parser_re = re.compile(r"%parser\s*$")
    lexer_re = re.compile(r"%lexer\s*$")
    footer_re = re.compile(r"%footer\s*$")
    comment_re = re.compile(r"\s*([^\\]#.*|)(#.*)?\s*$")

    lexing_rule_re = re.compile(r"""
    # the initial condition specifier
    (<(?P<initialNames>([a-zA-Z0-9,_]+|\s)*)>|(?P<sol>\^)|(?P<sof><<SOF>>)|)?

    # the regex
    (?P<regex>(\S|(\\ ))+)\s+

    # the action spec
    (%debug\(\s*"(?P<debug>[^\"]*)"\s*\)\s*,\s*)?

    (%begin\(\s*(?P<begin>([A-Za-z0-9]+|\$INITIAL))\s*\)\s*,\s*)?

    ((?P<token>[a-zA-Z_][a-zA-Z_0-9]*)
     |(?P<restart>%restart)
     |(?P<continue>%continue))\s*$""",
                                flags=re.X)

    lexing_statedef_re = re.compile(r'(?P<type>%x|%s) (?P<name>[a-zA-Z_][a-zA-Z0-9_]*)\s*$')

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


    def Lexer(self, line, eof=False):
         if eof:
             return

         match = self.lexing_statedef_re.match(line)
         if match:
             if match.group('type') == '%x':
                 self.syntax.AddExclusiveInitialCondition(match.group('name'))
             elif match.group('type') == '%s':
                 self.syntax.AddInclusiveInitialCondition(match.group('name'))
             else:
                 raise Exception("can't happen")

             return

         match = self.lexing_rule_re.match(line)
         state = set()

         if not match:
             self.logger.error("line %i, invalid token spec" % (self.line,))
             return

         # determine the inital condtions
         if match.group('sol'):
             state.add(self.syntax.InitialCondition("$SOL"))

         if match.group('sof'):
             state.add(self.syntax.InitialCondition("$SOF"))

         if match.group('initialNames'):
             names = [name.strip() for name in match.group('initialNames').split(',')]
             for name in names:
                 state.add(self.syntax.InitialCondition(name))

         # print('SOL match:', match.group('sol'), 'inital names match:', match.group('initialNames'))

         # collect actions
         action = List()

         if match.group('debug'):
             action.Append(Debug(match.group('debug')))

         if match.group('begin'):
             action.Append(Begin(self.syntax.InitialCondition(match.group('begin'))))

         if match.group('restart'):
             action.Append(Restart())

         elif match.group('token'):
             self.syntax.RequireTerminal(match.group('token'))
             action.Append(Token(match.group('token')))

         elif match.group('continue'):
             action.Append(Continue())

         # put it all together, add a lexing rule
         try:
             regex = Regex(match.group('regex'))
         except RegexSyntaxError as e:
             self.logger.error(str(e))
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
                        self.logger.error("Syntax error in associativity definition")
                        raise Exception()

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

    def Action(self, line, eof=False):

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

        indent = Indention(line)
        if self.indent is None:
            self.indent = indent

        # finish the action on unindent eof
        if eof or indent < self.indent:
            self.state = self.Parser
            self.current.Left().AddProd(self.current)
            self.current = self.current.Left()
            self.indent = None
            self.state(line)
            return

        def Unindent(line):
            ind = Indention(line)
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

    def IncludesSToken(self): return False

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
                any(cond in conditions for cond in self.conditions):
            return True
        return False

class ExclusiveInitialCondition(InitialCondition):

    def Match(self, conditions):
        if self in conditions:
            return True
        return False

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
        self.ast_info = ASTInformation()
        self.header = []
        self.footer = []
        self.lexer = []
        self.inline_tokens = set()

        self.initialConditions = {}
        # the condition $INITIAL is the default condition
        # $SOL is the start of line condition
        # $SOF is the start of file condition
        self.initialConditions["$INITIAL"] = InclusiveInitialCondition("$INITIAL", 0)
        sol = self.initialConditions["$SOL"] = InclusiveInitialCondition("$SOL", 1)
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

    def InitialConditions(self):
        return self.initialConditions.values()

    def InitialCondition(self, name):
        return self.initialConditions[name]

    def AddInclusiveInitialCondition(self, name):
        if name in self.initialConditions:
            raise Exception("Initial condition name %s already in use" % name)

        self.initialConditions[name] = InclusiveInitialCondition(name, len(self.initialConditions))

    def AddExclusiveInitialCondition(self, name):
        if name in self.initialConditions:
            raise Exception("Initial condition name %s already in use" % name)

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


class LRAction(object):

    def IsShift(self): return False
    def IsReduce(self): return False
    def IsAccept(self): return False

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

    def Accept(self, visitor):
        return visitor.VisitShift(self)

class Reduce(LRAction):
    def IsReduce(self): return True

    def __init__(self, reduction, prec, n):
        super(Reduce, self).__init__(prec, n)
        self.reduction = reduction

    def __str__(self):
        return "r%d" % self.reduction

    def Red(self):
        return self.reduction

    def Accept(self, visitor):
        return visitor.VisitReduce(self)

class LRActionVisitor(object):

    def Visit(self, action):
        return action.Accept(self)

    def VisitShift(self, shift):
        pass

    def VisitReduce(self, red):
        pass

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

class StateTransitionGraph(object):
    """
    An *LR(1) state transition graph, this has the behaviour
    common to LALR(1), LR(1), SLR(1), ... transition graphs.
    """

    def __init__(self, grammar, logger):
        self.logger = logger

        self.grammar = grammar
        self.states = []

        self.conflicts = 0

        self.start = None

    def ReportNumOfConflicts(self):
        if self.conflicts:
            self.logger.warning(str(self.conflicts) + " conflict(s) found!")

    def Construct(self):
        raise NotImplementedError()

    def NormalizeItemSet(self, elements):
        """
        Normalize the item set (each core shall occur only once, the
        lookahead sets are unified)
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
        Check whether a state having the given elements already exists.
        If it does exist return it else create the new state and determine it's sub states.
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

    def GenerateState(self, number, elements):
        raise NotImplementedError()

    def ResolveConflict(self, state, old, new):

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
                return None

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
                raise Exception("Can't happen")


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

    def CreateParseTable(self, symtable):

        atable = []
        jtable = []

        rules = []

        terminals = dict()
        metas = dict()

        for symbol in symtable.values():
            if symbol.SymType() == Syntax.TERMINAL \
                    or symbol.SymType() == Syntax.EOF \
                    or symbol.SymType() == Syntax.ERROR:
                terminals[symbol.Symbol()] = symbol.Number()
            elif symbol.SymType() == Syntax.META:
                metas[symbol.Symbol()] = symbol.Number()
            elif symbol.SymType() == Syntax.UNDEF:
                pass
            else:
                print(symbol.Symbol(), file=sys.stderr)
                raise Exception("Can't happen")

        prodToRule = dict()

        for meta in metas:
            for rule in meta.Productions():
                prodToRule[rule] = len(rules)
                rules.append(rule)

        stateToIndex = dict()

        k = 0
        for state in self.states:
            stateToIndex[state] = state.Number()

        for state in self.states:
            acur = [None for i in range(len(terminals))]
            jcur = [None for i in range(len(metas))]

            atable.append(acur)
            jtable.append(jcur)

            for trans, prods in state.Transitions().items():
                symb = trans.Symbol()
                tstate = trans.State()

                if symb in metas:
                    jcur[metas[symb]] = stateToIndex[tstate]

                elif symb in terminals:
                    assoc = Production.NONE
                    prec = -1

                    for item in prods:
                        nprec = item.Prod().NumberInFile()
                        if nprec > prec:
                            prec = nprec
                            assoc = item.Prod().GetAssoc()

                    acur[terminals[symb]] = Shift(stateToIndex[tstate],
                                                  assoc, prec)
                else:
                    print(state, file=sys.stderr)
                    print(str(symb), file=sys.stderr)
                    raise Exception("Can't happen")

            for item in state.Elements():
                if item.AfterDot() is None:
                    reduceAction = Reduce(prodToRule[item.Prod()],
                                          item.Prod().GetAssoc(),
                                          item.Prod().NumberInFile())

                    for la in item.Lookahead():
                        if acur[terminals[la]] is not None:
                            acur[terminals[la]] = \
                                self.ResolveConflict(state,
                                                     acur[terminals[la]],
                                                     reduceAction)


                        else:
                            acur[terminals[la]] = reduceAction

        return ParseTable(atable, jtable, stateToIndex[self.start], rules)

class LALR1StateTransitionGraph(StateTransitionGraph):
    """
    The LALR(1) State Transition Graph.
    """

    def __init__(self, grammar, logger):
        super(LALR1StateTransitionGraph, self).__init__(grammar, logger)

    def Propagate(self):
        """
        Generate the lookahead sets
        """

        self.Kernels()

        # determine token generation and propagation
        for state in self.states:
            state.DeterminePropagationAndGeneration()


        for item in self.start.Elements():
            if item.Prod().left == self.grammar.RequireMeta("$START"):
                item.SetLookahead(set([self.grammar.RequireEOF()]))

        # set the spontaneously generated lookahead tokens
        for state in self.states:
            state.Generate()

        # propagate the lookahead tokens
        propagated = True
        while propagated:
            # print "Propagation Round"
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

        text = ""
        for line in lines:
            text += line + "\n"

        return text

    def Elements(self):
        return self.elements

    def Transitions(self):
        return self.transitions

    def Number(self):
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
        Determine the substates of this state and add them to the transition graph.
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
        super(LALR1StateTransitionGraphElement, self).__init__(graph, number, elements)

        self.lapropagation = []
        self.lageneration = []

    def DeterminePropagationAndGeneration(self):
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

                                        if la == undef:
                                            # print "Propagate", self.Number(), stateTo.Number(), item, "->", itemTo
                                            self.lapropagation.append((item, itemTo))

                                        else:
                                            # print "Generate", itemTo, ":", la, "(", item, ")"
                                            stateTo.lageneration.append((itemTo, la))

            item.SetLookahead(frozenset())

    def Generate(self):
        for item, symb in self.lageneration:
            newLa = set(item.Lookahead())
            newLa.add(symb)
            item.SetLookahead(newLa)

    def Propagate(self):
        propagated = False
        for item, to in self.lapropagation:
            newLa = to.Lookahead() | item.Lookahead()

            if newLa != to.Lookahead():
                to.SetLookahead(newLa)
                propagated = True

        return propagated

class AutomatonState(object):

    def __init__(self):
        self.transitions = dict()
        # self.clone = None
        self.action = None
        self.priority = None

    # this was added for one specific debugging task
    # either remove or adapt
    def __repr__(self):
        return "AutomatonState("+repr(id(self))+", "+ repr(self.action) +")"

    def Move(self, char):
        """
        Get the set of states reached by the transition on char.
        """
        return self.transitions.get(char, set())

    def MoveDFA(self, chr):
        """
        Get the transition on character for a DFA (that is, only one
        state, not a set of states).
        """
        res, = self.Move(chr)
        return res

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

    def AddTransitions(self, chars, state):
        for char in chars:
            if char not in self.transitions:
                self.transitions[char] = set()

            self.transitions[char].add(state)

    def AddTransition(self, char, state):
        if char not in self.transitions:
            self.transitions[char] = set()

        self.transitions[char].add(state)

    def Transitions(self):
        return self.transitions.items()

    def SetAction(self, priority, action):
        self.action = action
        self.priority = priority

    def GetAction(self):
        return self.action

    def Priority(self):
        return self.priority

class RegexAST(object):
    """An AST representing a regular expression."""

    def NFA(self):
        raise NotImplementedError()

class CharacterRegex(RegexAST):

    def __init__(self, chars):
        self.chars = frozenset(chars)

    def __str__(self):
        return "CharacterRegex()"

    def NFA(self):
        start = AutomatonState()
        end = AutomatonState()

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
        nfas, nfae = AutomatonState(), AutomatonState()
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
        start, end = AutomatonState(), AutomatonState()

        start.AddTransition('', nfa1s)
        start.AddTransition('', nfa2s)

        nfa1e.AddTransition('', end)
        nfa2e.AddTransition('', end)

        return start, end

class RegexSyntaxError(Exception):
    pass

class Regex(object):
    """A regular expression with an NFA representation."""

    def ParseEscape(self, iterator):
        char = next(iterator)

        if char == 'n':
            return set('\n')

        if char == 't':
            return set('\t')

        if char == 'x':
            string = ''
            string += next(iterator)
            string += next(iterator)
            return set(chr(int(string, base=16)))

        if char == 's':
            return set(' \n\t\v\r\f')

        if char == 'd':
            return set('0123456789')

        if char == 'w':
            return set('abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ013456789_')

        return set(char)


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
            raise RegexSyntaxError("Syntax error in regular expression")

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
                    raise RegexSyntaxError("Syntax error in regular expression")
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
                else:
                    tokens.append((0, set(char)))

        except StopIteration:
            return tokens

    def Parse(self):
        args = []

        tokens = self.lex()
        tokens.append((5,''))

        pos = 0

        # matching yacc grammar:

        # empty : /* empty */
        #       | or
        #       ;

        # or : or '|' chain
        #    | chain
        #    ;

        # chain : chain op
        #       | op
        #       ;

        # op : basic OP
        #    | basic
        #    ;

        # basic : '(' empty ')'
        #       | CHR
        #       ;

        # CHR is a single character, a character class, a dot or an escape
        # OP is one of + * ?
        # see the method lex for more detail

        def ParseEmpty():
            nonlocal pos
            token, lexeme = tokens[pos]

            if token == 0 or token == 2:
                ParseOr()
            else:
                args.append(CharacterRegex(set('')))

        def ParseOr():
            nonlocal pos
            token, lexeme = tokens[pos]

            if token == 0 or token == 2:
                ParseChain()

                token, lexeme = tokens[pos]
                if token == 3:
                    pos += 1
                    ParseOr()
                    a2 = args.pop()
                    a1 = args.pop()
                    args.append(OrRegex(a1,a2))


        def ParseChain():
            nonlocal pos
            token, lexeme = tokens[pos]

            if token == 0 or token == 2:
                ParseOp()
                ParseChain1()

        def ParseChain1():
            nonlocal pos
            token, lexeme = tokens[pos]

            if token == 0 or token == 2:
                ParseOp()

                a2 = args.pop()
                a1 = args.pop()
                args.append(SequenceRegex(a1,a2))
                ParseChain1()

        def ParseOp():
            nonlocal pos
            token, lexeme = tokens[pos]

            if token == 0 or token == 2:
                ParseBasic()

                token, lexeme = tokens[pos]
                if token == 1:
                    arg = args.pop()
                    if lexeme == '+':
                        args.append(SequenceRegex(arg, RepeatorRegex(arg)))

                    elif lexeme == '*':
                        args.append(RepeatorRegex(arg))

                    elif lexeme == '?':
                        args.append(OptionRegex(arg))

                    else:
                        raise RegexSyntaxError("Syntax error in regular expression")

                    pos += 1

        def ParseBasic():
            nonlocal pos
            token, lexeme = tokens[pos]

            if token == 0:
                args.append(CharacterRegex(lexeme))
                pos += 1

            elif token == 2:
                pos += 1
                ParseEmpty()
                token, lexeme = tokens[pos]

                if token != 4:
                    raise RegexSyntaxError("Syntax error in regular expression")
                pos += 1
            else:
                raise RegexSyntaxError("Syntax error in regular expression")

        ParseEmpty()

        if len(args) != 1 or len(tokens) != pos + 1:
            # print([str(x) for x in args])
            raise RegexSyntaxError("Syntax error in regular expression")

        # print args[0]
        return args[0]

    def __init__(self, regex):
        self.regex = regex
        self.ast = self.Parse()

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
        inlineTokens = AutomatonState()
        for token in lexerSpec.InlineTokens():

            previous = AutomatonState()
            inlineTokens.AddTransition('', previous)

            for char in token:
                new = AutomatonState()
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
        self.start = AutomatonState()

        if condition.IncludesSToken():
            self.start.AddTransition('', inlineTokenNFA)

        i = -1
        for lexingRule in lexingRules:
            if condition.Match(lexingRule.Conditions()):
                start, end = lexingRule.Regex().NFA()

                self.start.AddTransition('', start)
                end.SetAction(i, lexingRule.Action())
            i -= 1

    def CreateDFA(self):
        si = frozenset(self.start.EpsilonClosure())
        dfaStates = {si : AutomatonState()}
        todo = [si]

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
                    dfaStates[newState] = AutomatonState()

                    # select the appropriate action
                    curpri = float('-inf')
                    for state in newState:
                        pri = state.Priority()
                        if pri is not None and pri > curpri:
                            dfaStates[newState].SetAction(None, state.GetAction())
                            curpri = pri

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
        return tuple(self.GroupOfState(state.MoveDFA(chr(char))) for char in range(0,256))

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
            states.append(AutomatonState())
            newstates[states[-1]] = i

            if start in self.groups[i]:
                newstart = states[i]

        # link the new states
        for i in range(0, len(self.groups)):

            representative = self.groups[i][0]

            states[i].SetAction(None, representative.GetAction())

            for char in range(256):
                states[i].AddTransition(chr(char), states[self.GroupOfState(representative.MoveDFA(chr(char)))])

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
                for cstate in nstate:
                    mylist[ord(char)].append(self.states[cstate])

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
        return "print(%s)" % repr(action.Text())

    def VisitRestart(self, action):
        return "self.current_token = (None, self.position)"

    def VisitToken(self, action):
        return "self.current_token = (%d, self.position)" % self.symtable[action.Name()].Number()

    def VisitGetMatch(self, action):
        return "raise GotToken()"

    def VisitBegin(self, action):
        return "self.nextCond = %d" % action.State().Number()

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

            tablehelper = helper + ' = (' + ',\n'.join(str(entry).replace(' ', '') for entry in ded) + ')'
            tablestr += ','.join(helper + '[%d]' % i for i in indices)
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
            baccess = "buffer[self.position]"
        else:
            extract = ''
            baccess = "ord(buffer[self.position])"


        data = []
        action_table = {}

        for cond, table, start, actions, mapping in lexer.Get():

            lextablehelper, lextablestr = self.TableStrings("ltd%d" % cond.Number(), tuple(tuple(a[0] for a in state) for state in table))

            # create the string representing the actions
            actionstr = "(\n"
            for action in actions:
                if action not in action_table:
                    action_table[action] = len(action_table)

                actionstr += "            self.action%d" % (action_table[action],) + ", \n"

            actionstr += "        )"

            mappingstr = ""
            if mapping:
                # create the string mapping
                lookup = "mapping[" + baccess + "]"

                mappingstr = "("
                for entry in mapping:
                    mappingstr += str(entry)
                    mappingstr += ","
                mappingstr += ")"

            data.append((cond,start, actionstr, mappingstr, lextablehelper, lextablestr))
        data.sort(key=lambda x: x[0].Number())

        startstr = '('
        mappingstr = '('
        actionstr = '('
        lextablestr = '('
        lextablehelper = ''

        for cond, start, astr, mstr, lthstr, ltstr in data:
            startstr += str(start) + ','
            mappingstr += mstr + ',\n'
            actionstr += astr + ',\n'
            lextablestr +=   ltstr + ',\n'
            lextablehelper += '    ' + lthstr + '\n'

        lextablestr += ')'
        actionstr += ')'
        mappingstr += ')'
        startstr += ')'

        linesPositionClass = ''
        linesCount = "position = None"
        eofPosition = "None"

        lexerDebugData = ""
        if self.debug:
            lexerDebugData = r"""
    TOKEN_NAMES = {"""
            for key, value in symtable.items():
                lexerDebugData += "{token}:{key},".format(key=repr(key), token=value.Number())
            lexerDebugData += r"""}
"""

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
                except mmap.error:
                    # we could not mmap the file: perhaps warn, but open it
                    # through a FileBuffer
                    mmap_file = False

                self.size = self.buffer.size()

            if not mmap_file:
                # for now: just slurp the file, sorry if it is large,
                # a tty or a pipe -> TODO
                self.buffer = """
      + ("codefile.readall()" if self.python3 else "codfile.read()") + r"""
                self.size = len(self.buffer)

        self.root = 0
        self.position = 0
        self.current_token = None
        self.actions = """ + actionstr + """
        self.SetInitialCondition(2)
        self.nextCond = 0
        self.line = 1
        self.start_of_line = 0

    def SetInitialCondition(self, num):
        self.cond = num
        self.start, self.table, self.cactions, self.mapping = self.starts[num], self.tables[num], self.actions[num], self.mappings[num]

    def lexAll(self):
        tokens = []
        while True:
            type, text, pos = self.lex()
            if type == """ + str(symtable["$EOF"].Number()) + r""":
                return tokens
            tokens.append((type, text, pos))

    def lex(self):
        self.current_token = None
        state = self.start
        size, table, cactions, mapping, buffer = self.size, self.table, self.cactions, self.mapping, self.buffer
        try:
            while self.position != size:
                state = table[state][""" + lookup + """]
                self.position += 1
                cactions[state]()
            raise GotToken()
        except GotToken:
            if self.current_token is None:
                if self.position == self.root:
                    return ("""
           + "{0}, {1}, {2}".format(symtable["$EOF"].Number(), "''", eofPosition) +
                               r""")
                else:
                    self.current_token = ("""
            + "{0}, {1}".format(symtable["$ERROR"].Number(), "self.position") +
                               r""")
            name, pos = self.current_token
            text = self.buffer[self.root:pos]""" + extract + r"""
            """ + linesCount + r"""
            if self.nextCond == 0 and text and text[-1] == '\n':
                self.nextCond = 1
            elif self.nextCond == 1 and text and text[-1] != '\n':
                self.nextCond = 0
            self.SetInitialCondition(self.nextCond)
            self.nextCond = self.cond
            self.root = pos
            self.position = self.root

            if name is None:
                return self.lex()
            else:
                return (name, text, position)
""")

        lexActionGen = LexActionToCode(symtable)

        for action, number in action_table.items():
            self.parser_file.write("""
    def action%d(self):
""" % (number,))

            if action is not None:
                code = lexActionGen.Visit(action).split('\n')
                for line in code:
                    self.parser_file.write("        " + line + "\n")
            else:
                self.parser_file.write("        pass\n" )

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
            self.parser_file.write(line + "\n")


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

    def error(self, *args, **kwargs):
        self.errors += 1
        super().error(*args, **kwargs)

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

        parseTable = graph.CreateParseTable(syn.SymTable())
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
