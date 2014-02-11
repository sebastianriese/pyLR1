
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
        self._emit("self.next_cond[-1] = {:d}".format(action.state.number))

    def visit_Push(self, action):
        self._emit("self.next_cond.append({:d})".format(action.state.number))

    def visit_Pop(self, action):
        self._emit("self.next_cond.pop()")

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
        self._debug = True
        self._standalone = False

    def write_header(self, header):
        if self._standalone:
            raise NotImplementedError("Can't do that yet")
        else:
            self._parser_file.write(
"""# this file was generated automagically by pyLR1
# do not edit, if you want to modify the parser, adapt the grammar file

from pyLRp.runtime.lexer import Lexer as BaseLexer
from pyLRp.runtime.parser import Parser as BaseParser
from pyLRp.runtime.parser import Accept
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

    def compile_lexer_symtable(self, symtable, initial_conditions):
        lexer_debug_data = ""

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

        return lexer_debug_data

    def write_lexer(self, lexer, symtable, initial_conditions):

        data = []
        action_table = {}

        for cond, lextable in lexer.lextables():

            lextablehelper, lextablestr = \
                self.table_strings("ltd%d" % cond.number,
                  tuple(tuple(state) for state in lextable.table))

            # create the string representing the actions
            action_vector = []
            for action in lextable.actions:
                if action is None:
                    action_vector.append('None')
                elif action == lexactions.GetMatch():
                    action_vector.append('-1')
                else:
                    if action not in action_table:
                        action_table[action] = len(action_table)
                    action_vector.append('{}'.format(action_table[action]))
            actionmapstr = "({})".format(','.join(action_vector))

            # create the data for the character mapping
            mappingstr = ""
            if lexer.mapping:
                # create the string mapping
                mappingstr = '({})'.format(','.join(map(str,
                    lextable.alphabetizer.mapping)))

            data.append((cond, lextable.start, actionmapstr, mappingstr,
                         lextablehelper, lextablestr))

        actionstr = ','.join('self.action{:d}'.format(i)
                             for i in range(len(action_table)))
        actionstr = ('({},)' if len(action_table) == 1
                             else '({})').format(actionstr)

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

        mappinghelper = ''

        lines_position_class = ''
        lines_count = "position = None"
        eof_position = "None"

        lexer_debug_data = self.compile_lexer_symtable(symtable,
                                                       initial_conditions)



        self._parser_file.write(r"""

class Lexer(BaseLexer):

    starts = """ + startstr + r"""
""" + mappinghelper + r"""
    mappings = """ + (mappingstr if lexer.mapping else "()") + r"""
""" + (lextablehelper if self._deduplicate else "") + r"""
    tables  = """ + lextablestr + lexer_debug_data + r"""
    actionmap = """ + actionmapstr + r"""

    def __init__(self, input_buffer):
        super(Lexer, self).__init__(input_buffer)
        self.actions = """ + actionstr  + r"""
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

        self._parser_file.write("""
class Parser(BaseParser):
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
        super(Parser, self).__init__(lexer)
        self.reductions = """ + reduction_str + """
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
