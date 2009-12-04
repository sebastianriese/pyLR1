"""
Module for parsing parser specifications and creating parsers from them
"""

import re

# this is used to replace dictionaries,
# if the ordering of the elements shall be preserved
class AList(object):
    def __init__(self):
        self.list = []

    def __len__(self):
        return len(self.list)

    def __repr__(self):
        return "AList("+ repr(self.list) + ")"

    def __str__(self):
        return "AList("+ str(self.list) + ")"

    def __contains__(self, key):
        return self.has_key(key)

    def at(self, index):
        return self.list[index]

    def has_key(self, key):
        for ckey, value in self.list:
            if ckey == key:
                return True

        return False
    
    def append(self, key, value):
        if self.has_key(key):
            raise KeyError()

        self.list.append((key, value))

    def __setitem__(self, key, value):
        self.append(key, value)

    def __getitem__(self, key):
        for ckey, value in self.list:
            if key == ckey:
                return value

        raise KeyError()

    def __delitem__(self, key):
        index = 0
        for ckey, value in self.list:
            if key == ckey:
                del self.list[index]
                return

            index += 1

        raise KeyError()

    def __iter__(self):
        for item in self.list:
            yield item

class Production(object):
    """A production in a grammar."""

    def __init__(self):
        pass

        

class LR1Element(Production):
    """A LR(1) element (production, position, lookahead set)"""
    
    def __init__(self):
        super(Production, self).__init__()



class Symbol(object):
    """Base class of all symbols in the system (terminal, meta and empty)."""

    def __init__(self, name, syntax):
        self.name = name
        self.syntax = syntax

    def First(self):
        """The FIRST-set of the symbol."""
        raise NotImplementedError()

    def ReducesToEmpty(self):
        """Return whether the symbol can be reduced to the empty symbol."""
        raise NotImplementedError()

    def IsEmpty(self):
        """Return whether the symbol is the empty symbol."""
        return False

class Emtpy(Symbol):
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
        super(Symbol, self).__init__(None, None)

    @classmethod
    def Instance(clazz):
        """Return the singleton instance, create it, if neccessary."""
        if not clazz.instance:
            clazz.instance = Empty()

        return clazz.instance

    def First(self):
        return set([self])

    def ReducesToEmpty(self):
        return True

    def IsEmpty(self):
        return True

class Terminal(Symbol):
    """The Terminal symbol class."""

    def __init__(self, name, syntax, regex):
        super(Symbol, self).__init__(name, syntax)
        self.regex = regex
        
    def First(self):
        return set([self])

    def ReducesToEmpty(self):
        return False


class Meta(Symbol):
    """
    The Metasymbol class.
    This stores the grammar for the symbol.
    """

    def __init__(self, name, syntax):
        super(Symbol, self).__init__(name, syntax)
        self.prod = []

    def AddProd(self, prod):
        self.prod.append(prod)

    def First(self):
        result = set()

        if self.ReducesToEmpty():
            result.add(Empty.Instance())

        for prod in self.prod:
            for sub in prod:
                if sub.ReducesToEmpty():
                    result |= sub.First() - set([Empty.Instance()])
                else:
                    break

    def ReducesToEmpty(self):
        
        # sorry this is a little mess ... but I found no more beautiful way
        # using a list or similar stuff is quite as ugly (though maybe more comprehensible)
        for prod in self.prod:
            
            for sub in prod:
                if not sub.ReducesToEmpty():
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


class Syntax(object):
    parser_re = re.compile(r"%parser\s*$")
    lexer_re = re.compile(r"%lexer\s*$")
    comment_re = re.compile(r"\s+(#.*)?\s*$")

    lexing_rule_re = re.compile(r"((.|(\\ ))+)\s+(([a-zA-Z_][a-zA-Z_0-9]*)|(%restart))\s*$")

    syntax_rule_re = re.compile(r"([a-zA-Z_][a-zA-Z_0-9]*):\s*$")
    syntax_symbol_re = re.compile(r"([a-zA-Z_][a-zA-Z_0-9]*)")
    syntax_stoken_re = re.compile(r'\"((.|\\\")+?)\"')
    syntax_empty_re = re.compile(r'%empty')

    def __init__(self, parser):
        self.parser_file = parser
        self.line = 0

        self.parser = AList()
        self.lexer = AList()
        self.symbols = {}

        self.header = []

        # ugly state variable available to the subparsers
        self.current = None
        self.state = self.Header

    def Header(self, line):
        self.header.append(line)

    def Lexer(self, line):
         match = self.lexing_rule_re.match(line)

         if not match:
             print "Error: line %i, invalid token spec" % (self.line,)
             return

         if match.group(4) == "%restart":
             
             if not self.lexer.has_key("%restart"):
                 self.lexer.append("%restart", [])

             self.lexer["%restart"].append(match.group(1))

         else:
             self.lexer.append(match.group(4), match.group(1))

    def Parser(self, line):
        match = self.syntax_rule_re.match(line)

        if match:
            self.current = match.group(1)
            self.parser[self.current] = {
                "name" : self.current,
                "seqs" : [],
                }
        else:
            seq = []
            line = line.strip()

            while line:
                
                match = self.syntax_stoken_re.match(line)
                
                if match:
                    seq.append(("stat", match.group(1)))
                else:
                    match = self.syntax_symbol_re.match(line)
                    
                    if match:
                        seq.append(("symb", match.group(1)))
                    else:
                        match = self.syntax_empty_re.match(line)
                        
                        if match:
                            seq.append(("emtpy", "%empty"))
                        else:
                            print "Syntax error: line %d (%s)" % (self.line,line)
                            seq.append(("error", line))

                line = line[len(match.group(0)):]
                line = line.strip()

            self.parser[self.current]["seqs"].append(seq)

    def Parse(self):
        self.line = 0

        for line in self.parser_file:
            self.line += 1

            if self.comment_re.match(line):
                pass
            elif self.parser_re.match(line):
                self.state = self.Parser
            elif self.lexer_re.match(line):
                self.state = self.Lexer
            else:
                self.state(line)

    def Closure(self):
        pass

    def Write(self, parser_file):
        
        parser_file.write("""# this file was generated automagically by spg
# do not edit, if you want to modify the parser, adapt the grammar file

import re

""")

        for headline in self.header:
            parser_file.write(headline + "\n")

        parser_file.write("""class Lexer(object):
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

        for name, regex in self.lexer:

        # restart tokens
            if name == "%restart":
                for ignored in regex:
                    parser_file.write("""
        match = re.match(r"%s", self.buffer)
        if match:
            self.buffer = self.buffer[len(match.group(0)):]
            return self.lex()
""" % ignored)
            else:
                parser_file.write("""
        match = re.match(r"%s", self.buffer)

        if match:
            self.buffer = self.buffer[len(match.group(0)):]
            return ("%s", match.group(0))
""" % (regex, name))

        parser_file.write("""
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
        
        for name, symbol in self.parser:
            for red in symbol['seqs']:
                pass

        parser_file.write("""

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
    fi = file('Syntax', 'r')
    p = Syntax(fi)
    p.Parse()
    fi.close()
    
    fo = file('Syntax.py', 'w')
    p.Write(fo)
    fo.close()
