"""
Parse parser and lexer specifications and create DFA lexers and LR(1) parsers from them.
It is planned to implement LALR(1) parser support in future.
"""

import re

class Production(object):
    """A production in a grammar. Productions with left set to None may be used as arbitrary symbol strings."""

    def __init__(self, left, syms):
        self.left = left
        self.syms = syms
        # self.first = None

    def __iter__(self):
        return iter(self.syms)

    def __str__(self):
        text =  str(self.left) + " <- "

        for sub in self:
            text += str(sub) + " "

        return text


    def AddSym(self, sym):
        self.syms.append(sym)

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
        return Production(None, self.syms + [elem])


class LR1Element(object):
    """A LR(1) element (production, position, lookahead set)"""
    
    def __init__(self, prod, pos, la):
        self.prod = prod
        self.pos = pos
        self.la = frozenset(la)
        self.closure = None

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

    def AfterDot(self):
        return self.prod.AtOrNone(self.pos)

    def Core(self):
        return LR1Element(self.prod, self.pos, set())

    def Lookahead(self):
        return self.la

    def Goto(self, symbol):
        afterDot = self.AfterDot()
        result = set()

        if afterDot == symbol:
            result |= LR1Element(self.prod, self.pos+1, self.la).Closure(frozenset())

        return result
            
    def Closure(self, visited):
        # if self.closure != None:
        #     return self.closure

        closure = set([self])
        afterDot = self.AfterDot()
        
        if afterDot:
            laset = set()
                
            for la in self.la:
                firstconcat = self.prod.SubProduction(self.pos+1, None).Concat(la)
                laset |= firstconcat.First(frozenset())

            for prod in afterDot.Productions():

                elem = LR1Element(prod, 0, laset)

                if self not in visited:
                    closure |= elem.Closure(visited | set([self]))

        # if len(visited) == 0:
        #     self.closure = closure

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
        return True

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

    def Accept(self, visitor):
        return visitor.VisitRestart(self)

class Token(LexingAction):
    
    def __init__(self, name):
        super(LexingAction, self).__init__()
        self.name = name

    def Name(self):
        return self.name

    def Accept(self, visitor):
        return visitor.VisitToken(self)

class GetMatch(LexingAction):

    def __init__(self):
        super(LexingAction, self).__init__()

    def Accept(self, visitor):
        return visitor.VisitGetMatch(self)

class Parser(object):
    parser_re = re.compile(r"%parser\s*$")
    lexer_re = re.compile(r"%lexer\s*$")
    comment_re = re.compile(r"\s*([^\\]|)(#.*)?\s*$")

    lexing_rule_re = re.compile(r"((.|(\\ ))+)\s+(([a-zA-Z_][a-zA-Z_0-9]*)|(%restart))\s*$")

    syntax_rule_re = re.compile(r"([a-zA-Z_][a-zA-Z_0-9]*):\s*$")
    syntax_symbol_re = re.compile(r"([a-zA-Z_][a-zA-Z_0-9]*)")
    syntax_stoken_re = re.compile(r'\"((.|\\\")+?)\"')
    syntax_empty_re = re.compile(r'%empty')

    def __init__(self, grammar_file):
        self.syntax = Syntax()

        self.grammar_file = grammar_file
        self.line = 0

        # ugly state variable available to the subparsers
        self.current = None
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
        match = self.syntax_rule_re.match(line)

        if match:
            symbol = self.syntax.RequireMeta(match.group(1))

            if self.current == None:
                self.syntax.SetStart(symbol)

            self.current = symbol

        else:
            prod = Production(self.current, [])
            line = line.strip()

            while line:
                match = self.syntax_stoken_re.match(line)
                elem = None

                # this loop is used to be broken
                # not beautiful, but more readable than all other solutions
                while True:
                    if match:
                        elem = self.syntax.RequireTerminal(match.group(0))
                        self.syntax.AddInlineTerminalLexingRule(match.group(1))
                        break
                    
                    match = self.syntax_symbol_re.match(line)
                    
                    if match:
                        elem = self.syntax.RequireMeta(match.group(1))
                        break

                    match = self.syntax_empty_re.match(line)
                        
                    if match:
                        # elem = Empty.Instance()
                        break

                    print "Syntax error: line %d (%s)" % (self.line,line)
                    return

                line = line[len(match.group(0)):]
                line = line.strip()

                if elem:
                    prod.AddSym(elem)

            self.current.AddProd(prod)

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

    def __init__(self):
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

    def AddInlineTerminalLexingRule(self, token):
        self.inline_tokens.add(token)

    def RequireTerminal(self, name):
        if name not in self.symbols:
            self.symbols[name] = Terminal(name, self)

        return self.symbols[name]

    def RequireMeta(self, name):
        if name not in self.symbols:
            self.symbols[name] = Meta(name, self)

        return self.symbols[name]

    def AddSymbol(self, symbol):
        self.symbols[symbol.name] = symbol
        
    def AddHeader(self, line):
        self.header.append(line)

    def Header(self):
        return iter(self.header)

# if it has another name in English Compiler Literature I'm sorry
# the only thing I had available for constructing this is a German paper on LR-parsers
class LR1StateTransitionGraph(object):
    """
    The LR(1) State Transition Graph.
    """

    def __init__(self, grammar):
        self.grammar = grammar
        self.states = []

        self.start = None

    def Construct(self):
        # construct the starting point (virtual starting node) and use the RequireElement-method to  build up the tree
        prod = Production(self.grammar.RequireMeta("$START"), [self.grammar.Start()])

        self.grammar.RequireMeta("$START").AddProd(prod)

        start = LR1Element(prod,0,set([EOF()])).Closure(frozenset())
        
        self.start = self.RequireState(start)

    def RequireState(self, elements):
        """
        Check whether a state having the given elements already exists.
        If it does exist return it else create the new state and determine it's sub states.
        """
        
        # Normalize the element set (each shall core occur only once, the lookahead sets are unioned)
        cores = {}
        for elem in elements:
            if elem.Core() not in cores:
                cores[elem.Core()] = set()

            cores[elem.Core()] |= elem.Lookahead()

        elements = set()
        for core in cores:
            elements.add(LR1Element.FromCore(core, cores[core]))

        # do we already have this state?
        for state in self.states:
            if state.elements == elements:
                return state

        # instanciate the new state
        state = LR1StateTransitionGraphElement(self, len(self.states), elements)
        self.states.append(state)
        state.GenerateSubStates()
        return state
        

    def CreateParseTable(self, terminals, metas):
        atable = []
        jtable = []
        for state in self.states:
            acur = tuple([] for i in xrange(len(terminals)))
            jcur = tuple([] for i in xrange(len(metas)))

            atable.append(acur)
            jtable.append(jcur)

            for elem, tstate in state.Transitions():
                if elem.IsMeta():
                    jcur[metas[elem]].append(Shift(tstate.Number()))
                else:
                    acur[terminals[elem]].append(tstate.Number())

            for prod in state.Elements():
                if not prod.AfterDot():
                    for la in prod.Lookahead():
                        acur[self.Num(la)].appen(Reduce(self.Rule(prod)))

        return atable, jtable, # ...

class LR1StateTransitionGraphElement(object):

    def __init__(self, graph, number, elements):
        self.number = number
        self.graph = graph
        self.elements = elements
        self.transitions = set()

    def __str__(self):
        lines = []
        lines.append("state: " + str(self.number))
        
        lines.append("elements:")

        for elem in self.elements:
            lines.append(str(elem))

        lines.append("transitions:")
        for trans in self.transitions:
            token, state = trans
            lines.append((token.Name() or "None") + " -> " + str(state.number))

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

    def GenerateSubStates(self):
        """
        Determine the substates of this state and add them to the transition graph.
        """

        for elem in self.elements:

            if elem.AfterDot():
                goto = set()

                for cur in self.elements:
                    goto |= cur.Goto(elem.AfterDot())

                self.transitions.add((elem.AfterDot(), self.graph.RequireState(goto)))

class AutomatonState(object):
    
    def __init__(self):
        self.transitions = dict()
        # self.clone = None
        self.action = None
        self.priority = None

    def Move(self, char):
        return self.transitions.get(char, set())

    def EpsilonClosure(self, visited):
        closure = set([self])

        if self in visited:
            return closure

        closure |= self.transitions.get('', set())

        nc = set()
        for elem in closure:
            nc |= elem.EpsilonClosure(visited | frozenset([self]))

        return closure | nc

    # def Clone(self):
    #     if self.clone:
    #         return self.clone

    #     new = AutomatonState()
        
    #     self.clone = new
        
    #     for chars, state in self.transitions:
    #         new.AddTransition(chars, state.Clone())

    #     self.clone = None

    #     return new

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

    # def Close(self, state, states):
    #     nt = []

    #     for chars, old_to in self.transitions:
    #         for to_replace in states:
    #             if to_replace == old_to:
    #                 nt.append((chars, state))
    #                 break
    #         else:
    #             nt.append((chars, old_to))

    #     self.transitions = nt
                
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
            return set(chr(int(string), base=16))
        
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
                    if char == '^':
                        negate = True
                        chars = set(chr(i) for i in xrange(256))
                        continue
                    first = False

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

        print args[0]
        return args[0].NFA()

        # tokens = self.lex()
        # tokens.append((5, set()))
        # i = 0
        # while i <= len(tokens):
        #     token, lexeme = tokens[i]
        #     t, d, a = atable[states[-1]][token]
            
        #     # print "new\n", t,d,a,states,args,token

        #     while t == 1:
        #         for j in xrange(d):
        #             states.pop()
        #         sym = a(lexeme)
        #         state = jtable[states[-1]][sym]
        #         if state == -1:
        #             for arg in args:
        #                 print arg
        #             print states
        #             raise Exception()
        #         states.append(state)
        #         t, d, a = atable[states[-1]][token]
        #         # print t,d,a,states,args,token

        #     if t == 0:
        #         states.append(d)
        #         a(lexeme)
        #         i += 1

        #     elif t == 2:
        #         print str(args[0])
        #         return args[0].NFA()

        #     else:
        #         for arg in args:
        #             print arg
        #         print states
        #         raise Exception()

        # for arg in args:
        #     print arg
        # print states
        # raise Exception()
  
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
            
                for char in (chr(i) for i in xrange(0,255)):

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
        # reduce the number of states
        pass

    def CreateLexTable(self):
        lextable = [tuple([] for i in xrange(0,255)) for i in xrange(len(self.states))]
        actions = [None for i in xrange(len(self.states))]
        for state in self.states:

            actions[self.states[state]] = state.GetAction()

            mylist = lextable[self.states[state]]

            for char, nstate in state.Transitions():
                for cstate in nstate:
                    mylist[ord(char)].append(self.states[cstate])

        return lextable, self.states[self.start], actions


class ActionToCode(LexingActionVisitor):
    
    def VisitRestart(self, action):
        return "self.root = self.position; self.state = self.start"

    def VisitToken(self, action):
        return "self.current_token = ('%s', self.position)" % action.Name()

    def VisitGetMatch(self, action):
        return """if self.current_token:
            raise GotToken()
        else:
            raise Exception()"""

    def VisitList(self, action):
        pass

    

class Writer(object):

    def __init__(self, parser_file):
        self.parser_file = parser_file

    def Write(self, syntax, graph, lextable):
        
        self.parser_file.write("""# this file was generated automagically by pyLR1
# do not edit, if you want to modify the parser, adapt the grammar file

import mmap

""")

        for headline in syntax.Header():
            self.parser_file.write(headline + "\n")

        table, start, actions = lextable
            
        # create the string representing the lex-table
        lextablestr = "("
        for state in table:
            lextablestr += str(tuple(a[0] for a in state))
            lextablestr += ",\n"
        lextablestr += ")"

        actionstr = "(\n"
        i = 0
        for action in actions:
            if action:
                actionstr += "            self.action%d" % i + ", \n"
            else:
                actionstr += "            None, \n"
            i += 1
        actionstr += "        )"
         
        self.parser_file.write("""class GotToken(Exception):
    pass

class Lexer(object):
    def __init__(self, codefile):
        code = file(codefile, 'r')
        self.buffer = mmap.mmap(code.fileno(), 0, access=mmap.ACCESS_READ)
        self.size = self.buffer.size()
        code.close()
        self.root = 0
        self.position = 0
        self.current_token = None
        self.start = %d
        self.table = %s
        self.actions = %s

    def lex(self):
        self.current_token = None
        self.state = self.start
        table = self.table
        actions = self.actions
        buffer = self.buffer
        try:
            while True:
                self.state = table[self.state][ord(buffer[self.position])]
                self.position += 1
                if actions[self.state]:
                    actions[self.state]()
        except (GotToken, IndexError):
            if self.current_token:
                name, pos = self.current_token
                text = self.buffer[self.root:pos]
                self.root = pos
                self.position = pos
                return (name, text)
            else:
                return ('$EOF', '')
            
            
""" % (start, lextablestr, actionstr))
        i = 0
        codeGen = ActionToCode()
        for action in actions:
            if action:
                self.parser_file.write("""
    def action%d(self):
""" % (i,))
                self.parser_file.write("        " + codeGen.Visit(action) + "\n")

            i += 1

        self.parser_file.write("""
class StackObject(object):
    def __init__(self, state, text, position):
        self.state = state
        self.text = text
        self.position = position
        self.semantic = semantic

class Parser(object):
    # actions from the grammar
""")
        
        self.parser_file.write("""
    # auto generated methods
    def __init__(self, lexer):
        self.lexer = lexer
        self.stack = []
        self.state = ''
    
    def Parse(self):
        while True:
            token = self.lexer.lex()

            if not token:
                break
            
            
""" % ())

def PrintLexTable(lexingTable, start, actions):
    print "start: %d\n" % start

    for action in actions:
        print action

    print "\n    ",
    for i in xrange(32, 128):
        print chr(i).center(2),

    print ""
    i = 0
    for state in lexingTable:
        print str(i).center(2), "-",
        for a in xrange(32, 128):
            print str(state[a][0]).center(2),
        print ""
        i+=1

  
if __name__ == '__main__':
    fi = file('Syntax', 'r')
    p = Parser(fi)
    syn = p.Parse()
    fi.close()
    p = None # make it garbage

    # construct the parser
    graph = LR1StateTransitionGraph(syn)
    graph.Construct()

    # construct the lexer
    lexingNFA = LexingNFA(syn)
    lexingNFA.Construct()
    lexingDFA = lexingNFA.CreateDFA()
    lexingNFA = None # remove the reference to make it garbage
    
    lexingDFA.Optimize()

    lexingTable = lexingDFA.CreateLexTable()
    
    # PrintLexTable(*lexingTable)
    
    # print "Parser States:", len(graph.states)
    # print "Lexer States:", len(lexingDFA.states)
    # for state in graph.states:
    #     print str(state)

    # write lexer and parser
    fo = file('Syntax.py', 'w')
    writer = Writer(fo)
    writer.Write(syn, graph, lexingTable)
    fo.close()
