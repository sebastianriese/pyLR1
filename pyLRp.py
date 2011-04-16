#!/usr/bin/env python
"""
Parse parser and lexer specifications and create DFA lexers 
and LR(1) or LALR(1) parsers from them.
"""

# Copyright 2009, 2010 Sebastian Riese

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

import optparse

class Production(object):
    """A production in a grammar. Productions with left set to None may be used as arbitrary symbol strings."""

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

    def First(self, visited):
        # if self.first != None:
        #     return self.first

        result = set()

        for sub in self.syms:
            if sub  not in visited:
                result |= sub.First(visited | set([self])) - set([Empty.Instance()])

            if not sub.ReducesToEmpty(set()):
                break

        else:
            result.add(Empty.Instance())

        # if len(visited) == 0:
        #     self.first = result

        return result

    def Left(self):
        return self.left

    def AtOrNone(self, index):
        """Return the Symbol in the Production at position index ort None if index is out of range."""
        try:
            return self.syms[index]
        except IndexError:
            return None

    def SubProduction(self, index0 = 0, index1 = None):
        """
        Return a production with left=self.left and syms=self.syms[index0:index1].
        The main use of this is to evaluate the FIRST set of the subproductions.
        """
        return Production(None, self.syms[index0:index1])

    def Concat(self, elem):
        """
        Return a new Production with left=None and syms=self.syms+[elem].
        The main use of this is to evaluate the FIRST set of the concatenation.
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

    def IsKernel(self):
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
            del self.closure[(self.prod,self.pos,self.la)]

        self.la = frozenset(la)

    def Lookahead(self):
        return self.la

    def Goto(self, symbol):
        afterDot = self.AfterDot()
        result = set()

        if afterDot == symbol:
            result |= LR1Item(self.prod, self.pos+1, self.la).Closure(frozenset())

        return result
            
    def Closure(self, visited):
        # possibly the buffering is buggy
        if (self.prod,self.pos,self.la) in self.closure:
             return self.closure[(self.prod,self.pos,self.la)]

        closure = set([self])
        afterDot = self.AfterDot()
        recurses = False
        
        if afterDot:
            laset = set()
                
            for la in self.la:
                firstconcat = self.prod.SubProduction(self.pos+1, None).Concat(la)
                laset |= firstconcat.First(frozenset())

            for prod in afterDot.Productions():

                if self not in visited:
                    elem = LR1Item(prod, 0, laset)
                    closure |= elem.Closure(visited | set([self]))
                else:
                    recurses = True

        if not recurses:
            self.closure[(self.prod,self.pos,self.la)] = closure

        return closure

class Symbol(object):
    """Base class of all symbols in the system (terminal, meta and empty)."""

    def __init__(self, name, syntax):
        self.name = name
        self.syntax = syntax

    def __str__(self):
        return self.Name()

    def Name(self):
        return self.name
        
    def Syntax(self):
        return self.syntax

    def Productions(self):
        """Return an iterator over the list of productions"""
        return iter([])

    def First(self, visited):
        """The FIRST-set of the symbol."""
        raise NotImplementedError()

    def ReducesToEmpty(self, visited):
        """Return whether the symbol can be reduced to the empty symbol."""
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

    def First(self, visited):
        return set([self])

class Undef(Symbol):
    """
    The Undef symbol used in the LALR(1) lookahead
    construction algorithm
    """

    def __init__(self):
        super(Undef, self).__init__("$UNDEF", None)

    def First(self, visited):
        return set([self])

class Empty(Symbol):
    """
    The empty terminal symbol.
    The class is a singleton, in order to make many of the methods of the other classes
    work you should not instanciate it. Use the Instance method for retrieving the singleton instance.
    """

    instance = None

    def __init__(self):
        """
        Do not use this method.
        Use Instance() instead.
        """
        super(Empty, self).__init__("$Empty", None)

    @classmethod
    def Instance(clazz):
        """Return the singleton instance, create it, if neccessary."""
        if not clazz.instance:
            clazz.instance = Empty()

        return clazz.instance

    def First(self, visited):
        return set([self])

    def ReducesToEmpty(self, visited):
        # empty is not allowed in productions
        raise Exception()

    def IsEmpty(self):
        return True

class Terminal(Symbol):
    """The Terminal symbol class."""

    def __init__(self, name, syntax):
        super(Terminal, self).__init__(name, syntax)
 
    def First(self, visited):
        return set([self])

class Meta(Symbol):
    """
    The Metasymbol class.
    This stores the grammar for the symbol.
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

    def First(self, visited):
        # if self.first != None:
        #     return self.first

        result = set()

        for prod in self.prod:
            result |= prod.First(visited | set([self]))

        # if len(visited) == 0:
        #     self.first = result

        return result

    def ReducesToEmpty(self, visited):
        
        if self.reduces_to_empty != None:
            return self.reduces_to_empty

        for prod in self.prod:
            
            for sub in prod:
                if sub not in visited and not sub.ReducesToEmpty(visited | set([self])):
                    # the whole production doesn't reduce to empty (because one subsymbol doesn't)
                    break
            else:
                # all subsymbols in the production reduced to empty, break the main loop
                
                if len(visited) == 0:
                    self.reduces_to_empty = True

                return True

        # the loop's execution was broken, one production didn't reduce to empty
        if len(visited) == 0:
            self.reduces_to_empty = False

        return False

class LexingRule(object):
    
    def __init__(self, state, regex, action):
        self.state = state
        self.regex = regex
        self.action = action

    def Regex(self):
        return self.regex

    def Action(self):
        return self.action

class LexingActionVisitor(object):

    def Visit(self, action):
        return action.Accept(self)

    def VisitRestart(self, action):
        pass

    def VisitToken(self, action):
        pass

    def VisitGetMatch(self, action):
        pass

    def VisitList(self, action):
        pass

class LexingAction(object):
    
    def __init__(self):
        pass

    def Accept(self):
        raise NotImplementedError()

class List(LexingAction):
    
    def __init__(self, lst = []):
        super(LexingAction, self).__init__()
        self.list = lst

    def Append(self, action):
        self.list.append(action)

    def Accept(self, visitor):
        return visitor.VisitList(self)


class Restart(LexingAction):
    
    def __init__(self):
        super(LexingAction, self).__init__()

    def __repr__(self):
        return "Restart()"

    def Accept(self, visitor):
        return visitor.VisitRestart(self)

class Token(LexingAction):
    
    def __init__(self, name):
        super(LexingAction, self).__init__()
        self.name = name

    def __repr__(self):
        return "Token('%s')" % self.name

    def Name(self):
        return self.name

    def Accept(self, visitor):
        return visitor.VisitToken(self)

class GetMatch(LexingAction):

    def __init__(self):
        super(LexingAction, self).__init__()

    def __repr__(self):
        return "GetMatch()"

    def Accept(self, visitor):
        return visitor.VisitGetMatch(self)

class Parser(object):
    parser_re = re.compile(r"%parser\s*$")
    lexer_re = re.compile(r"%lexer\s*$")
    comment_re = re.compile(r"\s*([^\\]#.*|)(#.*)?\s*$")

    lexing_rule_re = re.compile(r"((.|(\\ ))+)\s+(([a-zA-Z_][a-zA-Z_0-9]*)|(%restart))\s*$")

    syntax_rule_re = re.compile(r"([a-zA-Z_][a-zA-Z_0-9]*):\s*$")
    syntax_symbol_re = re.compile(r"([a-zA-Z_][a-zA-Z_0-9]*)")
    syntax_action_re = re.compile(r'\:')
    syntax_stoken_re = re.compile(r'\"((.|\\\")+?)\"')
    syntax_empty_re = re.compile(r'%empty')
    syntax_prec_re = re.compile(r'%prec\s*\(\s*([a-zA-Z_][a-zA-Z_0-9]*)\s*\)')
    syntax_binding_re = re.compile(r'%left|%right|%nonassoc')
    syntax_binding_param_re = re.compile(r'(,\s*)?([a-zA-Z_][a-zA-Z_0-9]*|\"(.|\\\")+?\")')

    def __init__(self, grammar_file):
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

        self.state = self.Header

    def Header(self, line):
        self.syntax.AddHeader(line)

    def Lexer(self, line):
         match = self.lexing_rule_re.match(line)

         if not match:
             print "Error: line %i, invalid token spec" % (self.line,)
             return

         if match.group(4) == "%restart":
             self.syntax.AddLexingRule(LexingRule(None, match.group(1), Restart()))

         else:
             self.syntax.RequireTerminal(match.group(4))
             self.syntax.AddLexingRule(LexingRule(None, match.group(1), Token(match.group(4))))

    def Parser(self, line):

        if self.current == None:
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
                        raise Exception()

                self.assocPower += 1
                return

        match = self.syntax_rule_re.match(line)
        if match:
            symbol = self.syntax.RequireMeta(match.group(1))

            if self.current == None:
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
                        elem = self.syntax.RequireTerminal(match.group(0))
                        self.syntax.AddInlineLexingRule(match.group(1))
                        break
                    
                    match = self.syntax_symbol_re.match(line)
                    
                    if match:
                        elem = self.syntax.RequireMeta(match.group(1))
                        break

                    match = self.syntax_empty_re.match(line)
                        
                    if match:
                        break

                    match = self.syntax_prec_re.match(line)
                    if match:
                        try:
                            prod.SetAssoc(self.assocDefs[match.group(1)])
                        except KeyError:
                            print "Warning: %d: Erroneous precedence declaration" % self.line

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

                    print "Syntax error: line %d (%s)" % (self.line,line)
                    return

                line = line[len(match.group(0)):]
                line = line.strip()

                if elem:
                    prod.SetAssoc(self.assocDefs.get(elem.Name(), prod.GetAssoc()))
                    prod.AddSym(elem)
                    
            self.current.AddProd(prod)
    
    def Action(self, line):
        
        def Indent(line):
            ind = 0

            for char in line:
                if char == ' ':
                   ind += 1
                elif char == '\t':
                    ind += 8
                else:
                    break

            return ind            

        indent = Indent(line)
        if self.indent == None:
            self.indent = indent

        if indent < self.indent:
            self.state = self.Parser
            self.current.Left().AddProd(self.current)
            self.current = self.current.Left()
            self.indent = None
            self.state(line)
            return

        def Unindent(line):
            ind = Indent(line)
            line = line.strip()

            return " " * (ind - self.indent) + line

        self.current.SetAction(self.current.GetAction() + "\n" + Unindent(line))

    def Parse(self):
        self.line = 0

        for line in self.grammar_file:
            self.line += 1

            if self.comment_re.match(line):
                pass
            elif self.parser_re.match(line):
                self.state = self.Parser
            elif self.lexer_re.match(line):
                self.state = self.Lexer
            else:
                self.state(line)

        return self.syntax


class Syntax(object):

    TERMINAL = 0
    META = 1
    EOF = 2
    UNDEF = 3

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
        self.header = []

        self.lexer = []
        self.inline_tokens = set()
    
    def InlineTokens(self):
        return self.inline_tokens

    def Lexer(self):
        return self.lexer

    def SetStart(self, start):
        self.start = start

    def Start(self):
        return self.start

    def AddLexingRule(self, lexingrule):
        self.lexer.append(lexingrule)

    def AddInlineLexingRule(self, token):
        self.inline_tokens.add(token)

    def RequireEOF(self):
        if "$EOF" not in self.symbols:
            self.symbols['$EOF'] = Syntax.SymbolTableEntry(EOF(), self.termcounter, self.EOF)
            self.termcounter += 1

        return self.symbols["$EOF"].Symbol()

    def RequireUndef(self):
        if "$UNDEF" not in self.symbols:
            self.symbols['$UNDEF'] = Syntax.SymbolTableEntry(Undef(), None, self.UNDEF)

        return self.symbols["$UNDEF"].Symbol()

    def RequireTerminal(self, name):
        if name not in self.symbols:
            self.symbols[name] = Syntax.SymbolTableEntry(Terminal(name, self), self.termcounter, self.TERMINAL)
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
            print "(%d) %s" % (i, str(rule))
            i += 1

        

        giter = iter(self.gototable)
        aiter = iter(self.actiontable)
        try:
            while True:
                gline = giter.next()
                aline = aiter.next()
                for entry in aline:
                    entrystr = ""
                    first = True

                    
                    entrystr += str(entry)
                    print entrystr.center(5),

                for entry in gline:
                    print str(entry).center(5),
                print ""

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

    def __init__(self, grammar):
        self.grammar = grammar
        self.states = []

        self.conflicts = 0

        self.start = None

    def ReportNumOfConflicts(self):
        if self.conflicts:
            print self.conflicts, "conflicts found!"

    def Construct(self):
        raise NotImplementedError()

    def NormalizeItemSet(self, elements):
        """
        Normalize the item set (each core shall occur only once, the lookahead sets are unified)
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
            print state
            print "Default to the first reduce for reduce/reduce-conflict"
            self.conflicts += 1
            if old.NumberInFile() > new.NumberInFile():
                return new

        elif old.IsShift():
            assoc, prec = old.GetAssoc()
            associ, preci = new.GetAssoc()
                                
            # shift wins over reduce by default
            if assoc == Production.NONE:
                print state
                print "Default to shift for shift/reduce-conflict"
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
                raise Exception()


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

        for symbol  in symtable.itervalues():
            if symbol.SymType() == Syntax.TERMINAL or symbol.SymType() == Syntax.EOF:
                terminals[symbol.Symbol()] = symbol.Number()
            elif symbol.SymType() == Syntax.META:
                metas[symbol.Symbol()] = symbol.Number()
            elif symbol.SymType() == Syntax.UNDEF:
                pass
            else:
                print symbol.Symbol()
                raise Exception()

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
            acur = [None for i in xrange(len(terminals))]
            jcur = [None for i in xrange(len(metas))]

            atable.append(acur)
            jtable.append(jcur)

            for trans, prods in state.Transitions().iteritems():
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
                            
                    acur[terminals[symb]] = Shift(stateToIndex[tstate], assoc, prec)
                else:
                    print state
                    print str(symb)
                    raise Exception()

            for item in state.Elements():
                if item.AfterDot() is None:
                    for la in item.Lookahead():
                        if acur[terminals[la]] != None:
                            acur[terminals[la]] = self.ResolveConflict(state, acur[terminals[la]], Reduce(prodToRule[item.Prod()], item.Prod().GetAssoc(), item.Prod().NumberInFile()))
                                    
                        else:
                            acur[terminals[la]] = Reduce(prodToRule[item.Prod()], item.Prod().GetAssoc(), item.Prod().NumberInFile())

        return ParseTable(atable, jtable, stateToIndex[self.start], rules)

class LALR1StateTransitionGraph(StateTransitionGraph):
    """
    The LALR(1) State Transition Graph.
    """

    def __init__(self, grammar):
        super(LALR1StateTransitionGraph, self).__init__(grammar)
    
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
        # construct the starting point (virtual starting node) and use the RequireElement-method to  build up the tree

        prod = Production(self.grammar.RequireMeta("$START"), [self.grammar.Start()], -1)
        prod.SetAction("raise Accept()")

        self.grammar.RequireMeta("$START").AddProd(prod)

        # we use an empty lookahead set to generate the LR(0) item set
        start = LR1Item(prod,0,set([]))
        
        self.start = self.RequireState(start.Closure(frozenset()))

        # now we have to assign the lookahead sets
        # self.Kernels()

        # detect token generation and propagation
        self.Propagate()

        # self.CloseKernels()

class LR1StateTransitionGraph(StateTransitionGraph):
    """
    The LR(1) State Transition Graph.
    """
    
    def __init__(self, grammar):
        super(LR1StateTransitionGraph, self).__init__(grammar)

    def Construct(self):
        # construct the starting point (virtual starting node) and use the RequireElement-method to  build up the tree

        prod = Production(self.grammar.RequireMeta("$START"), [self.grammar.Start()], -1)
        prod.SetAction("raise Accept()")

        self.grammar.RequireMeta("$START").AddProd(prod)

        start = LR1Item(prod,0,set([self.grammar.RequireEOF()])).Closure(frozenset())
        
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
            if elem.IsKernel():
                res.add(elem)

        self.elements = res

    def Close(self):
        """
        Complete the item set to its closure
        """
        res = set()

        for elem in self.elements:
            res |= elem.Closure(frozenset())
        
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
            cls = item.Closure(frozenset())

            for other in cls:
                symb = other.AfterDot()
                if symb != None:

                    for trans in self.transitions:
                        if trans.Symbol() == symb:
                            stateTo = trans.State()

                            for itemTo in stateTo.Elements():

                                if itemTo.Prod() == other.Prod() and itemTo.Pos() == other.Pos() + 1:

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
        return set(self.transitions.get(char, set()))

    def EpsilonClosure(self, visited):
        closure = set([self])

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
        return self.transitions.iteritems()
                
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

        # chain the end of the first automaton to the start of the second one with an epsilon transition
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

class Regex(object):
    """A regular expression with an NFA representation."""

    def ParseEscape(self, iterator):
        char = iterator.next()
        
        if char == 'n':
            return set('\n')

        if char == 't':
            return set('\t')

        if char == 'x':
            string = ''
            string += iterator.next()
            string += iterator.next()
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
                char = iterator.next()
                if first:
                    first = False
                    if char == '^':
                        negate = True
                        chars = set(chr(i) for i in xrange(256))
                        continue

                if char == ']':
                    return chars

                elif char == '-':
                    if prev == None:
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

                    # use tuple unpacking to elegantly extract the single values from the sets
                    c, = cset
                    p, = prev

                    for char in xrange(ord(p) + 1, ord(c)):
                        cset.add(chr(char))

                    group = False

                prev = cset

                if negate:
                    chars -= cset
                else:
                    chars |= cset

        except StopIteration:
            print "error"
            return None

    def lex(self):
        # tokens: CHR ([...], \...,.) - 0, OP (+ ? *) - 1, ( - 2, | - 3, ) - 4
        tokens = []

        iterator = iter(self.regex)
        try:
            while True:
                char = iterator.next()
                if char == '\\':
                    tokens.append((0, self.ParseEscape(iterator)))
                elif char == '[':
                    tokens.append((0, self.ParseChrClass(iterator)))
                elif char == ']':
                    raise Exception()
                elif char in ('+', '?', '*'):
                    tokens.append((1, char))
                elif char == '|':
                    tokens.append((3, '|'))
                elif char == '(':
                    tokens.append((2, '('))
                elif char == ')':
                    tokens.append((4, ')'))
                elif char == '.':
                    tokens.append((0, set(chr(i) for i in xrange(0,255)) - set('\n')))
                else:
                    tokens.append((0, set(char)))

        except StopIteration:
            return tokens

    def Parse(self):
        args = []
        
        tokens = self.lex()
        tokens.append((5,''))

        # hack to overcome pythons scoping rules
        # this simulates i in proper static scope
        class Pos: pass
        pos = Pos()
        pos.i = 0

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
            token, lexeme = tokens[pos.i]
            
            if token == 0 or token == 2:
                ParseOr()
            else:
                args.append(CharacterRegex(set('')))

        def ParseOr():
            token, lexeme = tokens[pos.i]

            if token == 0 or token == 2:
                ParseChain()

                token, lexeme = tokens[pos.i]
                if token == 3:
                    pos.i += 1
                    ParseOr()
                    a2 = args.pop()
                    a1 = args.pop()
                    args.append(OrRegex(a1,a2))

                    
        def ParseChain():
            token, lexeme = tokens[pos.i]

            if token == 0 or token == 2:
                ParseOp()
                ParseChain1()

        def ParseChain1():
            token, lexeme = tokens[pos.i]
            
            if token == 0 or token == 2:
                ParseOp()

                a2 = args.pop()
                a1 = args.pop()
                args.append(SequenceRegex(a1,a2))
                ParseChain1()
                    
        def ParseOp():
            token, lexeme = tokens[pos.i]

            if token == 0 or token == 2:
                ParseBasic()
            
                token, lexeme = tokens[pos.i]
                if token == 1:
                    arg = args.pop()
                    if lexeme == '+':
                        args.append(SequenceRegex(arg, RepeatorRegex(arg)))

                    elif lexeme == '*':
                        args.append(RepeatorRegex(arg))

                    elif lexeme == '?':
                        args.append(OptionRegex(arg))
                    
                    else:
                        raise Exception()

                    pos.i += 1

        def ParseBasic():
            token, lexeme = tokens[pos.i]
            
            if token == 0:
                args.append(CharacterRegex(lexeme))
                pos.i += 1

            elif token == 2:
                pos.i += 1
                ParseEmpty()
                token, lexeme = tokens[pos.i]

                if token != 4:
                    raise Exception()
                pos.i += 1
            else:
                raise Exception()

        ParseEmpty()

        if len(args) != 1 or len(tokens) != pos.i + 1:
            print map(lambda x: str(x), args)
            raise Exception()

        # print args[0]
        return args[0].NFA()
  
    def __init__(self, regex):
        self.regex = regex
        self.start, self.end = self.Parse()

    def Start(self):
        return self.start

    def End(self):
        return self.end

class LexingNFA(object):
    
    def __init__(self, lexer):
        self.lexer = lexer
        self.states = []
        self.start = None

    def Construct(self):

        self.start = AutomatonState()

        # create the automaton parts for the inline tokens

        for token in self.lexer.InlineTokens():
            # print token
            previous = AutomatonState()
            self.start.AddTransition('', previous)

            # use the same automaton part for common beginnings            
            for char in token:
                new = AutomatonState()
                previous.AddTransition(char, new)
                previous = new
                self.states.append(new)
            
            previous.SetAction(0, Token('"' + token + '"'))

        i = -1
        for lexingRule in self.lexer.Lexer():
            regex = Regex(lexingRule.Regex())

            self.start.AddTransition('', regex.Start())
            regex.End().SetAction(i, lexingRule.Action())
            i -= 1


    def CreateDFA(self):
        si = frozenset(self.start.EpsilonClosure(frozenset()))
        dfaStates = {si : AutomatonState()}
        todo = [si]

        try:
            while True:
                # todo is changing ... iterators don't work therefore
                cur = todo.pop()
            
                for i in xrange(0,255):
                    char = chr(i)

                    move = set()
                    for c in cur:
                        for m in c.Move(char):
                            move |= m.EpsilonClosure(frozenset())
                    newState = frozenset(move)
                    
                    if newState not in dfaStates:
                        # print newState

                        todo.append(newState)
                        dfaStates[newState] = AutomatonState()

                        curpri = -len(self.lexer.Lexer())-1
                        for state in newState:
                            pri = state.Priority()
                            if pri != None and pri > curpri:
                                dfaStates[newState].SetAction(None, state.GetAction())
                                curpri = pri

                        if len(newState) == 0:
                            dfaStates[newState].SetAction(None, GetMatch())

                        # print dfaStates[newState].GetAction()

                    dfaStates[cur].AddTransition(char, dfaStates[newState])
                
        except IndexError:
            return LexingDFA(dfaStates, si)
        
        # unreachable

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
        # this code operates under the assumption, that we handle a DFA
        # so .Move() returns a set containing exactly one element
        # print state
        return tuple(self.GroupOfState(state.Move(chr(char)).pop()) for char in xrange(0,255))

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
        for i in xrange(0, len(self.groups)):
            states.append(AutomatonState())
            newstates[states[-1]] = i

            if start in self.groups[i]:
                newstart = states[i]

        # link the new states
        for i in xrange(0, len(self.groups)):

            representative = self.groups[i][0]

            states[i].SetAction(None, representative.GetAction())

            for char in xrange(255):
                states[i].AddTransition(chr(char), states[self.GroupOfState(representative.Move(chr(char)).pop())])
                
        return newstart, newstates

class LexingDFA(object):

    def __init__(self, states, start):
        self.states = dict()

        # remove the unnecassary NFA state information
        i = 0
        for state in states.itervalues():
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
        lextable = [tuple([] for i in xrange(0,255)) for i in xrange(len(self.states))]
        actions = [None for i in xrange(len(self.states))]
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
        classes = [[char for char in xrange(0,255)]]
        
        for line in self.table:

            newclasslist = []
            for cls in classes:
                newclasses = dict()
                for char in cls:
                    state = line[char][0]
                    if state not in newclasses:
                        newclasses[state] = []
                        
                    newclasses[state].append(char)
                newclasslist += newclasses.values()

            classes = newclasslist

        self.mapping = [None for j in xrange(0,255)]
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
        print "start: %d\n" % self.start

        for action in self.actions:
            print str(action)
        
        if not self.mapping:
            print "\n    ",

        # print the characters
        for i in xrange(32, 128):
            if self.mapping:
                print chr(i), str(self.mapping[i])
            else:
                print chr(i).center(2),

        if self.mapping:
            print "\n    ",


        printRange = xrange(32, 128)

        if self.mapping:
            printRange = xrange(len(self.table[0]))
            for i in printRange:
                print str(i).center(2),
        
        print ""
        i = 0
        for state in self.table:
            print str(i).center(2), "-",
            for a in printRange:
                print str(state[a][0]).center(2),
            print ""
            i+=1


class LexActionToCode(LexingActionVisitor):

    def __init__(self, symtable):
        super(LexActionToCode, self).__init__()
        self.symtable = symtable
    
    def VisitRestart(self, action):
        return "self.root = self.position; self.state = self.start"

    def VisitToken(self, action):
        return "self.current_token = (%d, self.position)" % self.symtable[action.Name()].Number()

    def VisitGetMatch(self, action):
        return """if self.current_token:
            raise GotToken()
        else:
            raise Exception()"""

    def VisitList(self, action):
        pass

class LRActionToLRTableEntry(LRActionVisitor):

    def __init__(self, rulelist, symtable):
        self.rulelist = rulelist
        self.symtable = symtable

    def VisitShift(self, shift):
        return (0,shift.Next())

    def VisitReduce(self, red):
        rule = self.rulelist[red.Red()]        # return (1,len(rule),self.symtable[rule.Left().Name()].Number())
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

    def __init__(self, parser_file, lines, trace, deduplicate, python3):
        self.parser_file = parser_file
        self.lines = lines
        self.trace = trace
        self.deduplicate = deduplicate
        self.python3 = python3

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


    def WriteLexer(self, lextable, symtable):
        table, start, actions, mapping = lextable.Get()
            
        lextablehelper, lextablestr = self.TableStrings("ltd", tuple(tuple(a[0] for a in state) for state in table))
        
        # create the string representing the actions
        actionstr = "(\n"
        action_table = {}
        for action in actions:
            if action not in action_table:
                action_table[action] = len(action_table)
                
            actionstr += "            self.action%d" % action_table[action] + ", \n"

        actionstr += "        )"

        mappingstr = ""
        if self.python3:
            extract = '.decode("UTF-8")'
            baccess = "buffer[self.position]"
        else:
            extract = ''
            baccess = "ord(buffer[self.position])"

        if mapping:
            # create the string mapping
            lookup = "mapping[" + baccess + "]"
            
            mappingstr = "mapping = ("
            for entry in mapping:
                mappingstr += str(entry)
                mappingstr += ","
            mappingstr += ")"

        
        select = "actions[self.state]()"

        linesPositionClass = ""
        linesPositionCalc = "position = 'No Line Tracking'"
        linesStartTrack = ""

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
        return "Line %d:%d - %d:%d" % (self.line0, self.col0, self.line1, self.col1)
"""

            linesStartTrack = "if " + baccess + " == 10: self.linestart = self.position - 1"

            linesPositionCalc = """self.line += self.buffer[self.last_token_end:pos] """ + extract + """ .count('\\n')
            position = Position('', self.line, self.root-self.linestart, self.line, pos - self.linestart)"""

        self.parser_file.write("""class GotToken(Exception):
    pass

""" + linesPositionClass + """

class Lexer(object):

    """ + mappingstr + """
    """ + lextablehelper + """
    table   = """ + lextablestr + """

    def __init__(self, codefile):
        code = open(codefile, 'r')
        self.buffer = mmap.mmap(code.fileno(), 0, access=mmap.ACCESS_READ)
        self.size = self.buffer.size()
        code.close()
        self.root = 0
        self.last_token_end = 0
        self.position = 0
        self.current_token = None
        self.start = %d""" % start + """
        self.actions = """ + actionstr + """
        self.line    = 1
        self.linestart = 0

    def lex(self):
        self.current_token = (%d""" % symtable["$EOF"].Number() +""", self.size)
        self.state = self.start
        table = self.table
        actions = self.actions
        buffer = self.buffer
        mapping = self.mapping
        try:
            while self.position != self.size:
                """ + linesStartTrack + """
                self.state = table[self.state][""" + lookup + """]
                self.position += 1
                """ + select  + """
            raise GotToken()
        except GotToken:
            name, pos = self.current_token
            """ + linesPositionCalc + """
            text = self.buffer[self.root:pos]""" + extract + """
            self.root = pos
            self.last_token_end = pos
            self.position = self.root
            return (name, text, position)
""")

        lexActionGen = LexActionToCode(symtable)

        for action in action_table:
            self.parser_file.write("""
    def action%d(self):
""" % (action_table[action],))

            if action != None:
                self.parser_file.write("        " + lexActionGen.Visit(action) + "\n")
            else:
                self.parser_file.write("        pass\n" )


    def WriteParser(self, graph, symtable):

        parseTable = graph.CreateParseTable(symtable)
        graph.ReportNumOfConflicts()
        # parseTable.Print()

        linesPosAddition = ""
        linesNullPos = ""

        if self.lines:
            linesPosAddition = """new.pos = stack[-size].pos.Add(stack[-1].pos)"""
            linesNullPos = "stack[-1].pos = Position('', 0,0,0,0)"

        state_trace = ""

        if self.trace:
            state_trace = "print stack[-1].state, lexeme"

        self.parser_file.write("""
class Accept(Exception):
    pass

class StackObject(object):
    def __init__(self, state):
        self.state = state
        self.pos = None
        self.sem = None

class Parser(object):
    # actions from the grammar
""")

        translator = LRActionToLRTableEntry(parseTable.Rules(), symtable)

        actionTableHelper, actionTableStr = self.TableStrings("atd", tuple(tuple(translator.Visit(a) if a != None else (2,0) for a in state) for state in parseTable.Actiontable()))

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
                    """ + linesPosAddition  + """
                    action(new)

                    for j in """ + ("range(size)" if self.python3 else "xrange(size)") + """:
                        stack.pop()

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
                    raise Exception("Syntax Error: " + str(stack[-1].pos))
        except Accept:
            return stack[-1].sem
""")
        redNum = 0
        for red in parseTable.Rules():
            text = red.GetAction()
            if not text: text = "pass"
            text = text.replace("$$", "result")
            for i in xrange(1, len(red) + 1):
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


    def Write(self, syntax, graph, lextable):

        self.WriteHeader(syntax.Header())

        self.WriteLexer(lextable, syntax.SymTable())

        self.WriteParser(graph, syntax.SymTable())

if __name__ == '__main__':

    opt_parser = optparse.OptionParser(usage="usage: %prog [options] INFILE", version="%prog 0.1")
    opt_parser.add_option("-o", "--output-file", dest="ofile", help="Set the output file to OFILE")
    opt_parser.add_option("-l", "--line-tracking", dest="lines", action='store_true', default=False, help="Enable line tracking in the generated parser")
    opt_parser.add_option("-L", "--lalr", dest="lalr", action='store_true', default=False, help="Generate a LALR(1) parser instead of a LR(1) parser")
    opt_parser.add_option("-d", "--debug", dest="debug", action='store_true', default=False, help="Print debug information to stdout")
    opt_parser.add_option("-D", "--not-deduplicate", dest="deduplicate", action='store_false', default=True, help="Write out the tables entirely as one big literal")
    opt_parser.add_option("-f", "--fast", dest="fast", action='store_true', default=False, help="Fast run: generates larger and possibly slower parsers, but takes less time")
    opt_parser.add_option("-T", "--trace", dest="trace", action='store_true', default=False, help="Generate a parser that prints out a trace of its state")
    opt_parser.add_option("-3", "--python3", dest="python3", action='store_true', default=False, help="Generate python3 compatible parser")


    options, args = opt_parser.parse_args()

    if len(args) >= 2:
        opt_parser.error("no more than on input file may be specified")
    
    fi = sys.stdin

    if len(args) == 1:
        infile, = args
        fi = file(infile, 'r')
    
    p = Parser(fi)
    
    syn = p.Parse()

    if len(args) == 1:
        fi.close()

    p = None # make it garbage

    # construct the parser
    graph = None
    if options.lalr:
        graph = LALR1StateTransitionGraph(syn)
    else:
        graph = LR1StateTransitionGraph(syn)
        
    graph.Construct()

    # construct the lexer
    lexingNFA = LexingNFA(syn)
    lexingNFA.Construct()
    lexingDFA = lexingNFA.CreateDFA()
    lexingNFA = None # remove the reference to make it garbage
    
    if not options.fast:
        lexingDFA.Optimize()

    lexingTable = lexingDFA.CreateLexTable()
    lexingDFA = None

    if not options.fast:
        lexingTable.ConstructEquivalenceClasses()

    if options.debug:
        # lexingTable.Print()

        # print "Parser States:", len(graph.states)
        # print "Lexer States:", len(lexingDFA.states)

        for state in graph.states:
            print str(state)

    # write lexer and parser

    fo = sys.stdout

    if options.ofile != None:
        fo = open(options.ofile, 'w')

    writer = Writer(fo, options.lines, options.trace, options.deduplicate, options.python3)
    writer.Write(syn, graph, lexingTable)
    
    if options.ofile != None:
        fo.close()
