"""
Parse parser and lexer specifications and create lexers based on the re-module and LR(1) parsers from them.
It is planned to implement LALR(1) parser support in future.
"""

import re

class Production(object):
    """A production in a grammar. Productions with left set to None may be used as arbitrary symbol strings."""

    def __init__(self, left, syms):
        self.left = left
        self.syms = syms
        self.first = None

    def __iter__(self):
        return iter(self.syms)

    def AddSym(self, sym):
        self.syms.append(sym)

    def First(self, visited = set()):
        if self.first != None:
            return self.first

        result = set()

        for sub in self.syms:
            if sub  not in visited:
                result |= sub.First(visited) - set([Empty.Instance()])

            if not sub.ReducesToEmpty():
                break

        self.first = result
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
        Return a new Production with left=None and syms=self.syms+[Production(None, elem)].
        The main use of this is to evaluate the FIRST set of the concatenation.
        """
        return Production(None, self.syms + [elem])


class LR1Element(object):
    """A LR(1) element (production, position, lookahead set)"""
    
    def __init__(self, prod, pos, la):
        self.prod = prod
        self.pos = pos
        self.la = frozenset(la)
        self.goto = None
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
        if self.goto != None:
            return self.goto

        afterDot = self.AfterDot()
        result = set()

        if afterDot == symbol:
            result |= LR1Element(self.prod, self.pos+1, self.la).Closure()

        self.goto = result
        return result
            
    def Closure(self, visited = set()):

        if self.closure != None:
            return self.closure

        closure = set([self])
        afterDot = self.AfterDot()
        
        if afterDot:
            for prod in afterDot.Productions():
                laset = set()

                for la in self.la:
                    laset |= prod.SubProduction(self.pos+1, None).Concat(la).First()

                elem = LR1Element(prod, 0, laset)

                if elem not in visited:
                    closure |= elem.Closure(visited | set([elem]))

        self.closure = closure

        return closure

class Symbol(object):
    """Base class of all symbols in the system (terminal, meta and empty)."""

    def __init__(self, name, syntax):
        self.name = name
        self.syntax = syntax

    def Name(self):
        return self.name
        
    def Syntax(self):
        return self.syntax

    def Productions(self):
        """Return an iterator over the list of productions"""
        return iter([])

    def First(self, visited = set()):
        """The FIRST-set of the symbol."""
        raise NotImplementedError()

    def ReducesToEmpty(self, visited = set()):
        """Return whether the symbol can be reduced to the empty symbol."""
        return False

    def Productions(self):
        return []

    def IsEmpty(self):
        """Return whether the symbol is the empty symbol."""
        return False

class EOF(Symbol):
    """
    The EOF symbol.
    """

    def __init__(self):
        super(EOF, self).__init__("$EOF", None)

    def First(self, visited = set()):
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
        super(Empty, self).__init__(None, None)

    @classmethod
    def Instance(clazz):
        """Return the singleton instance, create it, if neccessary."""
        if not clazz.instance:
            clazz.instance = Empty()

        return clazz.instance

    def First(self, visited = set()):
        return set([self])

    def ReducesToEmpty(self, visited = set()):
        return True

    def IsEmpty(self):
        return True

class Terminal(Symbol):
    """The Terminal symbol class."""

    def __init__(self, name, syntax):
        super(Terminal, self).__init__(name, syntax)
 
    def First(self, visited = set()):
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

    def First(self, visited = set()):
        if self.first != None:
            return self.first

        result = set()

        if self.ReducesToEmpty():
            result.add(Empty.Instance())

        for prod in self.prod:
            # refactor to the production class
            result |= prod.First(visited | set([self]))

        self.first = result
        return result

    def ReducesToEmpty(self, visited = set()):
        
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

class LexingAction(object):
    
    def __init__(self):
        pass

class Restart(LexingAction):
    
    def __init__(self):
        super(LexingAction, self).__init__()


class Token(LexingAction):
    
    def __init__(self, name):
        super(LexingAction, self).__init__()
        self.name = name

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
                        elem = self.syntax.RequireTerminal(match.group(1))
                        self.syntax.AddInlineTerminalLexingRule(match.group(1))
                        break
                    
                    match = self.syntax_symbol_re.match(line)
                    
                    if match:
                        elem = self.syntax.RequireMeta(match.group(1))
                        break

                    match = self.syntax_empty_re.match(line)
                        
                    if match:
                        elem = Empty.Instance()
                        break

                    print "Syntax error: line %d (%s)" % (self.line,line)
                    return

                line = line[len(match.group(0)):]
                line = line.strip()
                
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

        self.inline_tokens = set()
        self.lexer = []
        
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
# the only thing available for constructing this is a German paper
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

        start = LR1Element(prod,0,set([EOF()])).Closure()
        
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


class Writer(object):

    def __init__(self, parser_file):
        self.parser_file = parser_file

    def Write(self, syntax):
        
        self.parser_file.write("""# this file was generated automagically by spg
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

        for name, regex in syntax.Lexer():

        # restart tokens
            if name == "%restart":
                for ignored in regex:
                    self.parser_file.write("""
        match = re.match(r"%s", self.buffer)
        if match:
            self.buffer = self.buffer[len(match.group(0)):]
            return self.lex()
""" % ignored)
            else:
                self.parser_file.write("""
        match = re.match(r"%s", self.buffer)

        if match:
            self.buffer = self.buffer[len(match.group(0)):]
            return ("%s", match.group(0))
""" % (regex, name))

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
        self.state = '%s'
    
    def Parse(self):
        while True:
            token = self.lexer.lex()

            if not token:
                break
            
            
""" % (self.parser.at(0)[0]))

            
if __name__ == '__main__':
    fi = file('Test.pyLRp', 'r')
    p = Parser(fi)
    syn = p.Parse()
    fi.close()

    graph = LR1StateTransitionGraph(syn)
    graph.Construct()

    for state in graph.states:
        print str(state)

    #fo = file('Syntax.py', 'w')
    #writer = Writer(fo)
    #writer.Write(syn, graph)
    #fo.close()
