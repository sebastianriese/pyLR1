
from .. import pyblob
from .. import lexactions
from .. import parsetable
from ..syntax import Syntax, Symtable
from ..pyblob import PySuite, PyText, PyNewline, PyStackvar

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

    def visit_PySuite(self, suite):
        self.multiline = True
        if suite.code:
            visitor = PyBlobToLines(self.stacklen, toplevel=False)
            for fragment in suite.code:
                fragment.accept(visitor)
            indent = ['    ']
            if self.toplevel: indent = []
            for line in visitor.get_lines():
                self.lines.append(indent + [line])
        else:
            self.lines.append(['pass'])
        self.add = True

    def visit_PyText(self, text):
        self.ensure_list()
        self.lines[-1].append(text.text)

    def visit_PyNewline(self, newline):
        self.ensure_list()
        self.multiline = True
        self.add = True

    def visit_PyStackvar(self, stackvar):
        self.ensure_list()
        if stackvar.result:
            self.lines[-1].append('result')
        else:
            self.lines[-1].append('self.stack[-{:d}]'.format(
                    self.stacklen - stackvar.num + 1))


class LexActionToCode(lexactions.LexingActionVisitor):

    def __init__(self, symtable):
        super(LexActionToCode, self).__init__()
        self._symtable = symtable
        self._code = []
        self._indent = 0

    def _emit(self, code):
        self._code.append('    ' * self._indent + code)

    def code(self):
        return iter(self._code)

    def visit_Debug(self, action):
        self._emit("print(%s, repr(text))" % repr(action.text))

    def visit_Restart(self, action):
        self._emit("return None")

    def visit_Token(self, action):
        self._emit("return {:d}".format(self._symtable[action.name].number))

    def visit_GetMatch(self, action):
        # this is never actually called!
        assert False
        self._emit("pass")

    def visit_Begin(self, action):
        self._emit("self.nextCond[-1] = {:d}".format(action.state.number))

    def visit_Push(self, action):
        self._emit("self.nextCond.append({:d})".format(action.state.number))

    def visit_Pop(self, action):
        self._emit("self.nextCond.pop()")

    def visit_List(self, actionList):
        added = False
        for action in actionList:
            action.accept(self)
            added = True
        if not added:
            self._emit('pass')

    def visit_Continue(self, action):
        self._emit('self.state = self.start')

    def visit_Function(self, action):
        self._emit('{}(self, text, position)'.format(action.name))

class LRActionToLRTableEntry(parsetable.LRActionVisitor):

    def __init__(self, symtable):
        self.symtable = symtable

    def visit_Shift(self, shift):
        return (0, shift.next)

    def visit_Reduce(self, red):
        return (1, red.red)


class Writer(object):

    def deduplicate(self, iterable):
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

    def __init__(self, parser_file, logger, lines, trace,
                 deduplicate, python3, debug=False):
        self.logger = logger

        self._parser_file = parser_file
        self._lines = lines
        self._trace = trace
        self._deduplicate = deduplicate
        self._python3 = python3
        self._debug = debug

    def write_header(self, header):
        self._parser_file.write(
"""# this file was generated automagically by pyLR1
# do not edit, if you want to modify the parser, adapt the grammar file

import mmap
""")

        for headline in header:
            self._parser_file.write(headline)

    def table_strings(self, helper, tableTuple):
        tablehelper = ""
        tablestr = "("

        if self._deduplicate:
            ded, indices = self.deduplicate(tableTuple)

            tablehelper = helper + ' = (' + \
                ',\n'.join(str(entry).replace(' ', '') for entry in ded) + \
                (',)' if len(ded) == 1 else ')')
            tablestr += ','.join(helper + '[%d]' % i for i in indices)
            if len(indices) == 1:
                tablestr += ','
        else:
            for state in tableTuple:
                tablestr += str(state).replace(' ', '')
                tablestr += ",\n"

        tablestr += ")"

        return tablehelper, tablestr

    def write_AST(self, ast, symtable):
        if not ast.used:
            return

        classes = {}

        # collect information on the classes and attach the actions
        for symbolname in symtable:
            symbol = symtable[symbolname]

            if symbol.symtype == Symtable.META:
                if symbol.symbol.name in ast.lists:
                    # trivial list creation ... could be more
                    # intelligent at guessing how to do this
                    for prod in symbol.symbol.productions():
                        if prod.action is not None:
                            continue
                        positions = []
                        i = 0
                        for symb in prod:
                            i += 1
                            if not symb.is_s_token:
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
                            errmsg = "Erroneous %list target: more items" \
                                " than can be enlisted"
                            self.logger.error(errmsg)
                            raise Exception()
                        prod.action = action
                else:
                    for prod in symbol.symbol.productions():
                        if prod in ast.bindings:
                            args = []
                            i = 0
                            action = PySuite()
                            action.add(PyStackvar(result=True))
                            action.add(PyText('.sem = ' +
                                              ast.bindings[prod] + '('))
                            if self._lines:
                                action.add(PyStackvar(result=True))
                                action.add(PyText('.pos, '))

                            for symb in prod:
                                i += 1
                                if not symb.is_s_token:
                                    action.add(PyStackvar(num=i))
                                    action.add(PyText('.sem, '))
                                    if symb.name in args:
                                        args.append('{name:s}{count:d}'.format(
                                                name=symb.name,
                                                count=args.count(symb.name))
                                        )
                                    else:
                                        args.append(symb.name)
                            action.add(PyText(')'))
                            classes[ast.bindings[prod]] = args
                            prod.action = action

        self._parser_file.write("""
class AST(object):
    def Accept(self, visitor):
        raise NotImplementedError()
""")

        if self._lines:
            self._parser_file.write("""
    def Pos(self):
        return self.pos
""")

        self._parser_file.write("""
class %s(object):
    def Visit(self, ast):
        return ast.Accept(self)
""" % (ast.visitor,))

        for name in classes:
            self._parser_file.write("""
    def Visit%s(self, node):
        raise NotImplementedError()
""" % (name,))

        basearg = ['self']
        if self._lines:
            basearg.append('pos')

        for name, args in classes.items():
            self._parser_file.write("""
class %s(AST):
    def __init__(""" % (name,) + ", ".join(basearg + args))

            self._parser_file.write("):")
            if len(args) == 0:
                self._parser_file.write("""
        pass""")

            if self._lines:
                self._parser_file.write("""
        self.pos = pos""")

            for arg in args:
                self._parser_file.write("""
        self.%s = %s""" % (arg, arg))

            for arg in args:
                self._parser_file.write("""
    def get_%s(self):
        return self.%s
""" % (arg, arg))

            self._parser_file.write("""
    def Accept(self, visitor):
        return visitor.Visit%s(self)
""" % (name,))

    def write_lexer(self, lexer, symtable, initial_conditions):

        if self._python3:
            extract = '.decode("UTF-8")'
            baccess = "buffer[cur_pos]"
        else:
            extract = ''
            baccess = "ord(buffer[cur_pos])"

        data = []
        action_table = {}

        lookup = baccess
        if lexer.mapping:
            lookup = "mapping[" + baccess + "]"

        for cond, table, start, actions, mapping in lexer.get():

            lextablehelper, lextablestr = \
                self.table_strings("ltd%d" % cond.number,
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
            if lexer.mapping:
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

        lines_position_class = ''
        lines_count = "position = None"
        eof_position = "None"

        lexer_debug_data = ""
        if self._debug:
            token_names = []
            token_numbers = []
            symtypes = frozenset([Symtable.TERMINAL, Symtable.EOF, Symtable.ERROR])
            for key in symtable:
                value = symtable[key]
                if value.symtype in symtypes:
                    token_spec = dict(key=repr(key), token=value.number)
                    token_names.append("{token}: {key}".format(**token_spec))
                    token_numbers.append("{key}: {token}".format(**token_spec))

            condition_names = []
            condition_numbers = []
            for name, cond in initial_conditions.items():
                condition_spec = dict(name=repr(name), num=cond.number)
                condition_names.append("{num}: {name}".format(**condition_spec))
                condition_numbers.append("{name}: {num}".format(**condition_spec))

            lexer_debug_data = r"""
    TOKEN_NAMES = {{{}}}
    TOKEN_NUMBERS = {{{}}}
    CONDITION_NAMES = {{{}}}
    CONDITION_NUMBERS = {{{}}}
""".format(','.join(token_names), ','.join(token_numbers),
           ','.join(condition_names), ','.join(condition_numbers))

        if self._lines:
            lines_position_class = """class Position(object):
    def __init__(self, file, line0, col0, line1, col1):
        self.file  = file
        self.line0 = line0
        self.col0  = col0
        self.line1 = line1
        self.col1  = col1

    def Add(self, oth):
        return Position(self.file, self.line0, self.col0, oth.line1, oth.col1)

    def __str__(self):
        return "{:s} Line {:d}:{:d} - {:d}:{:d}".format(
            self.file, self.line0, self.col0, self.line1, self.col1)
"""

            lines_count = r"""
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
            eof_position = \
                r"""Position(self.filename, self.line, 0, self.line, 0)"""

        self._parser_file.write(r"""class GotToken(Exception):
    pass

""" + lines_position_class + r"""

class Lexer(object):

    starts = """ + startstr + r"""
    mappings = """ + (mappingstr if lexer.mapping else "()") + r"""
""" + (lextablehelper if self._deduplicate else "") + r"""
    tables  = """ + lextablestr + lexer_debug_data + r"""
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
        self.nextCond = [""" + repr(initial_conditions["$SOF"].number) + r"""]
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
            if type == """ + str(symtable["$EOF"].number) + r""":
                return tokens
            tokens.append((type, text, pos))

    def lex(self):
        if self.token_push_back:
            return self.token_push_back.pop()

        cond = self.nextCond[-1]
        state = self.starts[cond]
        """ + (r"size, table, cactions, mapping, buffer = self.size, self.tables[cond], self.actionmap[cond], self.mappings[cond], self.buffer" if lexer.mapping else
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
           + "{0}, {1}, {2}".format(symtable["$EOF"].number, "''", eof_position) +
                               r""")
                else:
                    action = cur_pos, self.error_action
            pos, faction = action

            text = self.buffer[self.root:pos]""" + extract + r"""

            """ + lines_count + r"""
            name = faction(text, position)

            if self.nextCond[-1] == """ + repr(initial_conditions["$SOF"].number) + r""":
                self.nextCond[-1] = """ + repr(initial_conditions["$INITIAL"].number) + r"""

            if self.nextCond[-1] == """
                        + repr(initial_conditions["$INITIAL"].number) +
                               r""" and text and text[-1] == '\n':
                self.nextCond[-1] = """
                               + repr(initial_conditions["$SOL"].number) +
                               r"""
            elif self.nextCond[-1] == """
                               + repr(initial_conditions["$SOL"].number) +
                               r""" and text and text[-1] != '\n':
                self.nextCond[-1] = """
                               + repr(initial_conditions["$INITIAL"].number) +
                               r"""
            self.root = pos

            if name is None:
                return self.lex()
            else:
                return (name, text, position)
""")

        for action, number in sorted(action_table.items(), key=lambda x: x[1]):
            self._parser_file.write("""
    def action%d(self, text, position):
""" % (number,))

            lexActionGen = LexActionToCode(symtable)
            lexActionGen.visit(action)
            for line in lexActionGen.code():
                self._parser_file.write("        " + line + "\n")

        self._parser_file.write(r"""
    def error_action(self, text, position):
        return """ + "{}".format(symtable["$ERROR"].number) + r"""
""")

    def write_parser(self, parse_table, symtable):
        # when there is no parser specified parse_table is None
        # and we don't write a parser to the output file
        if parse_table is None:
            return

        lines_pos_addition = ""
        lines_null_pos = ""

        if self._lines:
            lines_pos_addition = """new.pos = stack[-size].pos.Add(stack[-1].pos)"""
            lines_null_pos = "stack[-1].pos = Position('', 0,0,0,0)"

        state_trace = ""

        if self._trace:
            if self._python3:
                state_trace = "print(' '.join(str(entry.state) for entry in stack), '#', str((t,d)) ," + ("self.lexer.TOKEN_NAMES[token]" if self._debug else "token") + ", '\"' + lexeme + '\"')"
            else:
                state_trace = "print stack[-1].state, token lexeme"

        self._parser_file.write("""
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
    # actions from the grammar
""")

        translator = LRActionToLRTableEntry(symtable)

        action_table_helper, action_table_str = self.table_strings("atd", tuple(tuple(translator.visit(a) if a is not None else (2,0) for a in state) for state in parse_table.actiontable()))

        goto_table_helper, goto_table_str = self.table_strings("gtd", tuple(tuple(a if a else 0 for a in state) for state in parse_table.gototable()))

        reduction_str = "("
        i = 0
        for red in parse_table.rules():
            reduction_str += "(%d,%d,self.action%d),\n" % (len(red), symtable[red.left.name].number, i)
            i += 1
        reduction_str += ")"

        self._parser_file.write("""
    # tables
    start = %d""" % parse_table.start + """
    """ + action_table_helper + """
    atable = """ + action_table_str + """
    """ + goto_table_helper + """
    gtable = """ + goto_table_str + """

    # auto generated methods
    def __init__(self, lexer):
        self.lexer = lexer
        self.stack = []
        self.reductions = """ + reduction_str + """

    def Parse(self):
        lexer = self.lexer
        atable = self.atable
        gtable = self.gtable
        stack = self.stack
        reductions = self.reductions
        stack.append(StackObject(self.start))
        recovering = False
        """ + lines_null_pos + """

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
                    """ + lines_pos_addition  + r"""
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
                        rec = """ + str(symtable["$RECOVER"].number) + r"""

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
""")
        redNum = 0
        for red in parse_table.rules():
            text = red.action

            self._parser_file.write("""
    def action%d(self, result):""" % (redNum,))

            # the proper parser builds up a pyblob
            if isinstance(text, pyblob.PyBlob):
                visitor = PyBlobToLines(len(red))
                visitor.visit(text)
                if visitor.multiline:
                    self._parser_file.write('\n')

                for line in visitor.get_lines():
                    if line:
                        # don't write indentation if there is
                        # no line!
                        if visitor.multiline:
                            self._parser_file.write('        ')
                        else:
                            self._parser_file.write(' ')
                        self._parser_file.write(line)
                    self._parser_file.write('\n')

            # the bootstrap parser just concatenates text
            elif isinstance(text, list):
                text = list(filter(lambda x: bool(x.strip()), text))
                if not text: text = ["pass"]
                if len(text) == 1:
                    indent = False
                else:
                    indent = True
                    self._parser_file.write("\n")
                for line in text:

                    line = line.replace("$$", "result")
                    for i in reversed(range(1, len(red) + 1)):
                        line = line.replace("$%d" % i, "self.stack[-%d]" % (len(red) - i + 1))

                    if indent:
                        self._parser_file.write("        ")
                    else:
                        self._parser_file.write(" ")
                    self._parser_file.write(line)
                    self._parser_file.write("\n")
            else:
                if not text: text = "pass"
                text = text.replace("$$", "result")
                for i in reversed(range(1, len(red) + 1)):
                    text = text.replace("$%d" % i, "self.stack[-%d]" % (len(red) - i + 1))


                for char in text:
                    self._parser_file.write(char)
                    if char == '\n':
                        # indent two levels: Parser class, current function
                        self._parser_file.write("        ")

                self._parser_file.write("\n")
            redNum += 1


    def write_footer(self, footer):
        if footer:
            self._parser_file.write("""
# The following code is copied verbatim from the %footer section of
# the parser specification
""")

        for line in footer:
            self._parser_file.write(line)


    def write(self, syntax, parsetable, lextable):

        self.write_header(syntax.header)

        self.write_AST(syntax.AST_info, syntax.symtable)

        self.write_lexer(lextable, syntax.symtable, syntax.lexer.initial_conditions)

        self.write_parser(parsetable, syntax.symtable)

        self.write_footer(syntax.footer)
