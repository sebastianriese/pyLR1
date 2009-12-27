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
        result = set()

        for sub in self.syms:
            if sub  not in visited:
                result |= sub.First(visited | set([self])) - set([Empty.Instance()])

            if not sub.ReducesToEmpty(set()):
                break

        else:
            result.add(Empty.Instance())

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

    def Productions(self):
        return iter(self.prod)

    def AddProd(self, prod):
        self.prod.append(prod)

    def Productions(self):
        # the copying is just a safety measure ...
        return self.prod[:]

    def First(self, visited):
        if self.first != None:
            return self.first

        result = set()

        for prod in self.prod:
            # refactor to the production class
            result |= prod.First(visited | set([self]))

        self.first = result
        return result

    def ReducesToEmpty(self, visited):
        
        # sorry this is a little mess ... but I found no more beautiful way
        # using a list or similar stuff is quite as ugly (though maybe more comprehensible)
        for prod in self.prod:
            
            for sub in prod:
                if sub not in visited and not sub.ReducesToEmpty(visited | set([self])):
                    # the whole production doesn't reduce to empty (because one subsymbol doesn't)
                    break
            else:
                # all subsymbols in the production reduced to empty, break the main loop
                break
            
        else:
            # there wasn't a production for which all subsymbols reduces to empty, i.e. the loop's execution wasn't broken
            return False

        # the loop's execution was broken, one production contained only expressions reducing to empty
        return True

class LexingRule(object):
    
    def __init__(self, state, regex, action):
        self.state = state
        self.regex = regex
        self.action = action

    def Regex(self):
        return self.regex

    def PyAction(self):
        return self.action.Code()

class LexingAction(object):
    
    def __init__(self):
        pass

    def Code(self):
        raise NotImplementedError()

class Restart(LexingAction):
    
    def __init__(self):
        super(LexingAction, self).__init__()

    def Code(self):
        return "return self.lex()"

class Token(LexingAction):
    
    def __init__(self, name):
        super(LexingAction, self).__init__()
        self.name = name

    def Code(self):
        return "return Token('%s', match.group(0))" % self.name 

class Parser(object):
    parser_re = re.compile(r"%parser\s*$")
    lexer_re = re.compile(r"%lexer\s*$")
    comment_re = re.compile(r"\s*(#.*)?\s*$")

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
        

    def CreateParseTable(self):
        # ... generate the parse table
        pass

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
        self.clone = None

    def Move(self, char):
        return self.transitions.get(char)

    def EpsilonClosure(self, visited):
        closure = set()

        if self in visited:
            return closure

        closure |= self.transitions.get('', set())

        nc = set()
        for elem in closure:
            nc += elem.EpsilonClosure(visited | frozenset([self]))

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

    # def Transitions(self):
    #     return self.transitions

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
                

class ActionAutomatonState(AutomatonState):
    
    def __init__(self, lexerAction):
        super(ActionAutomatonState, self).__init__()
        self.action = lexerAction

class RegexAST(object):
    """An AST representing a regular expression."""

    def NFA(self):
        raise NotImplementedError()

class CharacterRegex(RegexAST):
    
    def __init__(self, chars):
        self.chars = chars

    def __str__(self):
        return "CharacterRegex(%s)" % str(self.chars)

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

        nfa1s.Close(nfa2s, [nfa1e])
        return nfa1s, nfa2e

class OptionRegex(RegexAST):

    def __init__(self, regex):
        self.regex = regex

    def __str__(self):
        return "RepeatorRegex(%s)" % str(self.regex)

    def NFA(self):

        nfas, nfae = self.regex.NFA()

        nfas.AddTransition(set(['']), nfae)

        return nfas, nfae

class RepeatorRegex(RegexAST):

    def __init__(self, regex):
        self.regex = regex

    def __str__(self):
        return "RepeatorRegex(%s)" % str(self.regex)

    def NFA(self):
        nfas, nfae = self.regex.NFA()

        for chars, state in nfas.Transitions():
            nfae.AddTransition(chars, state)

        return nfas, nfae
        
class OrRegex(RegexAST):
    
    def __init__(self, regex1, regex2):
        self.regex1, self.regex2 = regex1, regex2

    def __str__(self):
        return "OrRegex(%s, %s)" % (str(self.regex1), str(self.regex2))

    def NFA(self):

        nfa1s, nfa1e = self.regex1.NFA()
        nfa2s, nfa2e = self.regex2.NFA()

        start = AutomatonState.Merge(nfa1s, nfa2s)

        end = AutomatonState()

        start.Close(end, [nfa1e, nfa2e])

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
            negate = False

            while True:
                char = iterator.next()
                if first:
                    if char == '^':
                        negate = True
                        char = set(chr(i) for i in xrange(256))
                        continue
                    first = False

                if char == ']':
                    return chars
                
                cset = set()
                if char == '\\':
                    cset |= self.ParseEscape(iterator)
                else:
                    cset |= set(char)

                if negate:
                    chars -= cset
                else:
                    chars |= cset

        except StopIteration:
            print "error"
            return None

    def Parse(self):
        ops = []
        args = []

        def Or():
            arg2 = args.pop() 
            arg1 = args.pop()

            args.append(OrRegex(arg1, arg2))

        def Seq():
            arg2 = args.pop()
            arg1 = args.pop()

            args.append(SequenceRegex(arg1, arg2))

        def Plus():
            arg = args.pop()
            args.append(SequenceRegex(arg, RepeatorRegex(arg)))

        def Mult():
            arg = args.pop()
            args.append(RepeatorRegex(arg))

        def Opt():
            arg = args.pop()
            args.append(OptionRegex(arg))

        def OParen():
            print "error"
            raise StopIteration()
            
        def CParen():

            while ops[-1] != '(':
                prec, act = operators[ops.pop()]
                act()

            # remove the paren
            ops.pop()

        operators = {
            '|' : (-1,Or),
            ''  : (1,Seq),
            '+' : (2,Plus),
            '*' : (2,Mult),
            '?' : (2,Opt),
            '(' : (3,OParen),
            ')' : (3,CParen),
            }

        def Operate(operation):
            precop,  actop  = operators[operation]
            prectop, acttop = 0, None
            if ops:
                prectop, acttop = operators[ops[-1]]
            
            if precop > prectop:
                actop()
            elif precop == prectop:
                if acttop:
                    acttop()
                    ops.pop()
                ops.append(operation)
            else:
                ops.append(operation)
                
        iterator = iter(self.regex)

        try:
            first = True

            while True:
                # debug
                # print "ops"
                # for op in ops:
                #     print str(op)
                # print "args"
                # for arg in args:
                #     print str(arg)


                char = iterator.next()

                if char == '[':
                    args.append(CharacterRegex(self.ParseChrClass(iterator)))
                    if not first:
                        Operate('')
                    first = False

                elif char == ']':
                    print "error"
                    raise StopIteration()

                elif char == '(':
                    Operate('(')

                elif char == ')':
                    Operate(')')

                elif char == '|':
                    Operate('|')
                    first = True

                elif char == '+':
                    Operate('+')

                elif char == '*':
                    Operate('*')

                elif char == '?':
                    Operate('?')
                    
                elif char == '.':
                    cset = set(chr(i) for i in xrange(256))
                    cset -= set('\n\r')
                    args.append(CharacterRegex(cset))

                elif char == '\\':
                    args.append(CharacterRegex(self.ParseEscape(iterator)))
                    if not first:
                        Operate('')

                else:
                    args.append(CharacterRegex(set([char])))
                    if not first:
                        Operate('')
                    first = False


        except StopIteration:

            for op in ops:
                prec, act = operators[ops.pop()]
                act()

            print str(args[0])


            return None, None # args[0].NFA()
  
    def __init__(self, regex):
        self.regex = regex
        self.start, self.end = self.Parse()

    def Start(self):
        return self.start

class LexingNFA(object):
    
    def __init__(self, lexer):
        self.lexer = lexer
        self.states = []
        self.start = None

    def Construct(self):

        self.start = AutomatonState()

        # create the automaton parts for the inline tokens

        for token in self.lexer.InlineTokens():
            previous = self.start

            # use the same automaton part for common beginnings            
            for char in token[:-1]:

                new = AutomatonState()
                previous.AddTransition(char, new)
                previous = new
                self.states.append(new)
            
            creator = ActionAutomatonState(Token('"' + token + '"'))
            previous.AddTransition(token[-1], creator)

        for lexingRule in self.lexer.Lexer():
            regex = Regex(lexingRule.Regex())

            for chars, state in regex.Start().Transitions():
                self.start.AddTransition(char, state)


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
                        move += c.Move(char).EpsilonClosure(frozenset())
                    newState = frozenset(move)
                    
                    if newState not in dfaStates:
                        todo.append(newState)
                        dfaStates[newState] = AutomatonState()

                    dfaStates[cur].AddTransition(char, newState)
                
        except IndexError:
            return LexingDFA(self.lexer, dfaStates, si)
        
        # unreachable

class LexingDFA(object):

    def __init__(self, lexer, states, start):
        self.lexer = lexer
        self.states = []

        # remove the unnecassary NFA state information
        for state in states.itervalues():
            self.states.append(state)

        self.start = states[start]

    def Optimize(self):
        # reduce the number of states
        pass

    def CreateLexTable(self):
        # ... create the lexing table from the dfa
        # important: greediness
        pass

class Writer(object):

    def __init__(self, parser_file):
        self.parser_file = parser_file

    def Write(self, syntax, graph):
        
        self.parser_file.write("""# this file was generated automagically by pyLR1
# do not edit, if you want to modify the parser, adapt the grammar file

import re

""")

        for headline in syntax.Header():
            self.parser_file.write(headline + "\n")

        self.parser_file.write("""class Lexer(object):
    def __init__(self, codefile):
        self.code = file(codefile, 'r')
        self.buffer = ""
        self.line = 0

    def fill(self):
        if not self.buffer:
            try:
                self.buffer = self.code.readline()
                self.line += 1
            except EOFError:
                return False

        return True

    def lex(self):
        if self.fill():
            return None
""")
        

        for rule in syntax.Lexer():
            self.parser_file.write("""
        match = re.match(r"%s", self.buffer)
        if match:
            self.buffer = self.buffer[len(match.group(0)):]""" % rule.Regex())

            self.parser_file.write("""
            """ + rule.PyAction() + """
""")


        self.parser_file.write("""
        print "Lexing error: %d (%s)" % (self.line, self.buffer)
        self.buffer = self.buffer[1:]

class StackObject(object):
    def __init__(self, state, text):
        self.state = state
        self.text = text
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

            
if __name__ == '__main__':
    fi = file('Syntax', 'r')
    p = Parser(fi)
    syn = p.Parse()
    fi.close()

    graph = LR1StateTransitionGraph(syn)
    graph.Construct()

    lexingNFA = LexingNFA(syn)
    lexingNFA.Construct()
    lexingDFA = lexingNFA.CreateDFA()
    lexingNFA = None # remove the reference to make it garbage
    
    lexingDFA.Optimize()

    # for state in graph.states:
    #     print str(state)

    fo = file('Syntax.py', 'w')
    writer = Writer(fo)
    writer.Write(syn, graph)
    fo.close()
