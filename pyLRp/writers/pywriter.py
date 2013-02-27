
from .. import pyblob
from .. import lexactions
from .. import parsetable
from ..syntax import Syntax
from ..pyblob import PyBlobStackVarMapVisitor, PySuite, PyText, PyNewline, PyStackvar

class PyBlobToLines(pyblob.PyBlobVisitor):
    def __init__(self, stacklen, toplevel=True):
        self.lines = []
        self.add = True
        self.multiline = False
        self.stacklen = stacklen
        self.toplevel = toplevel

    def get_lines(self):
        for line in self.lines:
            yield ''.join(line)

    def ensure_list(self):
        if self.add:
            self.lines.append([])
        self.add = False

    def VisitPySuite(self, suite):
        self.multiline = True
        if suite.code:
            visitor = PyBlobToLines(self.stacklen, toplevel=False)
            for fragment in suite.code:
                fragment.Accept(visitor)
            indent = ['    ']
            if self.toplevel: indent = []
            for line in visitor.get_lines():
                self.lines.append(indent + [line])
        else:
            self.lines.append(['pass'])
        self.add = True

    def VisitPyText(self, text):
        self.ensure_list()
        self.lines[-1].append(text.text)

    def VisitPyNewline(self, newline):
        self.ensure_list()
        self.multiline = True
        self.add = True

    def VisitPyStackvar(self, stackvar):
        self.ensure_list()
        if stackvar.result:
            self.lines[-1].append('result')
        else:
            self.lines[-1].append('self.stack[-{:d}]'.format(
                    self.stacklen - stackvar.num + 1))


class LexActionToCode(lexactions.LexingActionVisitor):

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

class LRActionToLRTableEntry(parsetable.LRActionVisitor):

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

                        action = PySuite()
                        if len(positions) == 0:
                            # $$.sem = []
                            action.add(PyStackvar(result=True))
                            action.add(PyText('.sem = []'))
                        elif len(positions) == 1:
                            # $$.sem = [$N.sem]
                            pos, = positions
                            action.add(PyStackvar(result=True))
                            action.add(PyText('.sem = ['))
                            action.add(PyStackvar(num=pos))
                            action.add(PyText('.sem]'))
                        elif len(positions) == 2:
                            # $$.sem = $N1.sem; $$.sem.append($N2.sem)
                            action.add(PyStackvar(result=True))
                            action.add(PyText('.sem = '))
                            head, tail = positions
                            action.add(PyStackvar(num=head))
                            action.add(PyText('.sem; '))
                            action.add(PyStackvar(result=True))
                            action.add(PyText('.sem.append('))
                            action.add(PyStackvar(num=tail))
                            action.add(PyText('.sem)'))
                        else:
                            self.logger.error("Erroneous %list target: more items than can be enlisted")
                            raise Exception()
                        prod.SetAction(action)
                else:
                    for prod in symbol.Symbol().Productions():
                        if prod in ast.bindings:
                            args = []
                            i = 0
                            action = PySuite()
                            action.add(PyStackvar(result=True))
                            action.add(PyText('.sem = ' + ast.bindings[prod] + '('))
                            if self.lines:
                                action.add(PyStackvar(result=True))
                                action.add(PyText('.pos, '))

                            for symb in prod:
                                i += 1
                                if not symb.IsSToken():
                                    action.add(PyStackvar(num=i))
                                    action.add('.sem, ')
                                    if symb.Name() in args:
                                        args.append('{name:s}{count:d}'.format(
                                                name=symb.Name(),
                                                count=args.count(symb.Name()))
                                        )
                                    else:
                                        args.append(symb.Name())
                            action.add(PyText(')'))
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

    def WriteLexer(self, lexer, symtable, initial_conditions):

        if self.python3:
            extract = '.decode("UTF-8")'
            baccess = "buffer[cur_pos]"
        else:
            extract = ''
            baccess = "ord(buffer[cur_pos])"

        data = []
        action_table = {}

        lookup = baccess
        if lexer.Mapping():
            lookup = "mapping[" + baccess + "]"

        for cond, table, start, actions, mapping in lexer.Get():

            lextablehelper, lextablestr = \
                self.TableStrings("ltd%d" % cond.Number(),
                  tuple(tuple(state) for state in table))

            # create the string representing the actions
            action_vector = []
            for action in actions:
                if action is None:
                    action_vector.append('None')
                elif action == lexactions.GetMatch():
                    action_vector.append('-1')
                else:
                    if action not in action_table:
                        action_table[action] = len(action_table)
                    action_vector.append('{}'.format(action_table[action]))
            actionmapstr = "({})".format(','.join(action_vector))

            mappingstr = ""
            if lexer.Mapping():
                # create the string mapping
                mappingstr = '({})'.format(','.join(map(str, mapping)))

            data.append((cond, start, actionmapstr, mappingstr, lextablehelper, lextablestr))

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
                    token_spec = dict(key=repr(key), token=value.Number())
                    token_names.append("{token}: {key}".format(**token_spec))
                    token_numbers.append("{key}: {token}".format(**token_spec))

            condition_names = []
            condition_numbers = []
            for name, cond in initial_conditions.items():
                condition_spec = dict(name=repr(name), num=cond.Number())
                condition_names.append("{num}: {name}".format(**condition_spec))
                condition_numbers.append("{name}: {num}".format(**condition_spec))

            lexerDebugData = r"""
    TOKEN_NAMES = {{{}}}
    TOKEN_NUMBERS = {{{}}}
    CONDITION_NAMES = {{{}}}
    CONDITION_NUMBERS = {{{}}}
""".format(','.join(token_names), ','.join(token_numbers),
           ','.join(condition_names), ','.join(condition_numbers))

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
    mappings = """ + (mappingstr if lexer.Mapping() else "()") + r"""
""" + (lextablehelper if self.deduplicate else "") + r"""
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
        self.nextCond = [""" + repr(initial_conditions["$SOF"].Number()) + r"""]
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
        """ + (r"size, table, cactions, mapping, buffer = self.size, self.tables[cond], self.actionmap[cond], self.mappings[cond], self.buffer" if lexer.Mapping() else
        r"size, table, cactions, buffer = self.size, self.tables[cond], self.actionmap[cond], self.buffer") + r"""
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

            if self.nextCond[-1] == """ + repr(initial_conditions["$SOF"].Number()) + r""":
                self.nextCond[-1] = """ + repr(initial_conditions["$INITIAL"].Number()) + r"""

            if self.nextCond[-1] == """
                        + repr(initial_conditions["$INITIAL"].Number()) +
                               r""" and text and text[-1] == '\n':
                self.nextCond[-1] = """
                               + repr(initial_conditions["$SOL"].Number()) +
                               r"""
            elif self.nextCond[-1] == """
                               + repr(initial_conditions["$SOL"].Number()) +
                               r""" and text and text[-1] != '\n':
                self.nextCond[-1] = """
                               + repr(initial_conditions["$INITIAL"].Number()) +
                               r"""
            self.root = pos

            if name is None:
                return self.lex()
            else:
                return (name, text, position)
""")

        lexActionGen = LexActionToCode(symtable)

        for action, number in sorted(action_table.items(), key=lambda x: x[1]):
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
        recovering = False
        """ + linesNullPos + """

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

                else: # t == 2
                    if recovering:
                        # just skip unfit tokens during recovery
                        pass
                    else:
                        # setup error recovery by shifting the $RECOVER token
                        recovering = True
                        rec = """ + str(symtable["$RECOVER"].Number()) + r"""

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
""")
        redNum = 0
        for red in parseTable.Rules():
            text = red.GetAction()

            self.parser_file.write("""
    def action%d(self, result):""" % (redNum,))

            if isinstance(text, pyblob.PyBlob):
                visitor = PyBlobToLines(len(red))
                visitor.Visit(text)
                if visitor.multiline:
                    self.parser_file.write('\n')

                for line in visitor.get_lines():
                    if line:
                        # don't write indentation if there is
                        # no line!
                        if visitor.multiline:
                            self.parser_file.write('        ')
                        else:
                            self.parser_file.write(' ')
                        self.parser_file.write(line)
                    self.parser_file.write('\n')

            elif isinstance(text, list):
                text = list(filter(lambda x: bool(x.strip()), text))
                if not text: text = ["pass"]
                if len(text) == 1:
                    indent = False
                else:
                    indent = True
                    self.parser_file.write("\n")
                for line in text:

                    line = line.replace("$$", "result")
                    for i in reversed(range(1, len(red) + 1)):
                        line = line.replace("$%d" % i, "self.stack[-%d]" % (len(red) - i + 1))

                    if indent:
                        self.parser_file.write("        ")
                    else:
                        self.parser_file.write(" ")
                    self.parser_file.write(line)
                    self.parser_file.write("\n")
            else:
                if not text: text = "pass"
                text = text.replace("$$", "result")
                for i in reversed(range(1, len(red) + 1)):
                    text = text.replace("$%d" % i, "self.stack[-%d]" % (len(red) - i + 1))


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

        self.WriteLexer(lextable, syntax.SymTable(), syntax.initialConditions)

        self.WriteParser(parsetable, syntax.SymTable())

        self.WriteFooter(syntax.Footer())
