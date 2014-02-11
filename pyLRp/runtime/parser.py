from pyLRp.runtime.input import Position

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

# default definitions of the error reporting functions there are
# usually overwritten by the parser
def error(parser, pos, msg):
    raise SyntaxError(message=msg, position=pos)

def warning(parser, pos, msg):
    pass

class Parser(object):
    def __init__(self, lexer):
        self.lexer = lexer
        self.stack = []

    def parse(self):
        lexer = self.lexer
        atable = self.atable
        gtable = self.gtable
        stack = self.stack
        reductions = self.reductions
        stack.append(StackObject(self.start))
        recovering = False
        stack[-1].pos = Position('', 0, 0, 0, 0)

        try:
            while True:
                token, lexeme, pos = lexer.lex()
                t, d = atable[stack[-1].state][token]
                """ + state_trace + """
                while t == 1:
                    recovering = False
                    size, sym, action = reductions[d]
                    state = gtable[stack[-size-1].state][sym]
                    new = StackObject(state)
                    new.pos = stack[-size].pos.Add(stack[-1].pos)
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

                else: # t == 2
                    if recovering:
                        # just skip unfit tokens during recovery
                        pass
                    else:
                        # setup error recovery by shifting the $RECOVER token
                        recovering = True
                        rec = self.lexer.TOKEN_NUMBERS["$RECOVER"]

                        error(self, pos, "syntax error")

                        # pop tokens until error can be shifted
                        t, d = atable[stack[-1].state][rec]
                        errstates = []
                        while t != 0:
                            errstates.append(stack.pop())
                            if not stack:
                                raise SyntaxError(position=errstates[0].pos)
                            t, d = atable[stack[-1].state][rec]
                        new = StackObject(d)
                        new.sem = lexeme
                        new.pos = pos
                        stack.append(new)
                        # TODO: emit error message ... or should this
                        # be done on reduction of the error rule? what
                        # error sink should we use?  perhaps do some
                        # inspection to get a list of acceptable
                        # tokens

        except Accept:
            return stack[-1].sem

    def print_trace(self, action, token, lexeme):
        print(' '.join(str(entry.state) for entry in stack), '#', action,
              self.lexer.TOKEN_NAMES[token], repr(lexeme))

    def parse_traced(self):
        lexer = self.lexer
        atable = self.atable
        gtable = self.gtable
        stack = self.stack
        reductions = self.reductions
        stack.append(StackObject(self.start))
        recovering = False
        stack[-1].pos = Position('', 0, 0, 0, 0)

        try:
            while True:
                token, lexeme, pos = lexer.lex()
                t, d = atable[stack[-1].state][token]
                while t == 1:
                    recovering = False
                    size, sym, action = reductions[d]
                    state = gtable[stack[-size-1].state][sym]
                    new = StackObject(state)
                    new.pos = stack[-size].pos.Add(stack[-1].pos)
                    action(new)
                    if size > 0:
                        del stack[-size:]
                    stack.append(new)
                    t, d = atable[stack[-1].state][token]
                    self.print_trace('reduce on lookahead', token, lexeme)
                if t == 0:
                    new = StackObject(d)
                    new.sem = lexeme
                    new.pos = pos
                    stack.append(new)
                    self.print_trace('shift', token, lexeme)

                else: # t == 2
                    if recovering:
                        # just skip unfit tokens during recovery
                        pass
                    else:
                        # setup error recovery by shifting the $RECOVER token
                        recovering = True
                        rec = self.lexer.TOKEN_NUMBERS["$RECOVER"]

                        error(self, pos, "syntax error")

                        # pop tokens until error can be shifted
                        t, d = atable[stack[-1].state][rec]
                        errstates = []
                        while t != 0:
                            errstates.append(stack.pop())
                            if not stack:
                                raise SyntaxError(position=errstates[0].pos)
                            t, d = atable[stack[-1].state][rec]
                        new = StackObject(d)
                        new.sem = lexeme
                        new.pos = pos
                        stack.append(new)
                        # TODO: emit error message ... or should this
                        # be done on reduction of the error rule? what
                        # error sink should we use?  perhaps do some
                        # inspection to get a list of acceptable
                        # tokens

        except Accept:
            return stack[-1].sem
