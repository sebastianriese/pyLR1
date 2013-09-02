
import re

from ..core import CantHappen
from ..syntax import Syntax, Symtable, SyntaxNameError
from ..regex import Regex, RegexSyntaxError
from ..lexactions import (List, Debug, Push, Pop, Function, Token,
                          Begin, Restart, Continue)
from ..lexer import LexingRule
from ..lr import Production

class Parser(object):
    ast_re = re.compile(r"%ast\s*$")
    parser_re = re.compile(r"%parser\s*$")
    lexer_re = re.compile(r"%lexer\s*$")
    footer_re = re.compile(r"%footer\s*$")
    comment_re = re.compile(r"\s*([^\\]#.*|)(#.*)?\s*$")

    lexing_rule_re = re.compile(r"""
    # the initial condition specifier
    (<(?P<initialNames>([a-zA-Z0-9,_]+|\$SOL|\$SOF|\$INITIAL|\s)*)>|(?P<sol>\^)|)

    # the regex
    (?P<regex>(\S|(\\\ ))+)\s+

    # the action spec
    (%debug\(\s*"(?P<debug>[^\"]*)"\s*\)\s*,\s*)?

    ((?P<beginType>%begin|%push|%pop|%function)
        \(\s*(?P<begin>([A-Za-z0-9_]+|\$INITIAL|))\s*\)\s*,\s*)?

    ((?P<beginType2>%begin|%push|%pop|%function)
        \(\s*(?P<begin2>([A-Za-z0-9_]+|\$INITIAL|))\s*\)\s*,\s*)?

    ((?P<beginType3>%begin|%push|%pop|%function)
        \(\s*(?P<begin3>([A-Za-z0-9_]+|\$INITIAL|))\s*\)\s*,\s*)?

    ((?P<token>[a-zA-Z_][a-zA-Z_0-9]*)
     |(?P<restart>%restart)
     |(?P<continue>%continue))\s*$""",
                                flags=re.X)

    lexing_statedef_re = re.compile(r'''
    # the directive
    (?P<type>%x|%s|%nullmatch)\s+

    # the argument list
    (?P<names>([a-zA-Z_][a-zA-Z0-9_]*(\s*,\s*)?)+)\s*$''',
                                    flags=re.X)

    lexing_named_pattern_def_re = re.compile(r'''%def
    (?P<one>\s+
          (?P<name>[a-zA-Z_][a-zA-Z0-9_]*)\s+
          (?P<regex>(\S|(\\\ ))+)
    )?\s*$''', flags=re.X)
    lexing_named_pattern_line_re = re.compile(r'''
          (?P<name>[a-zA-Z_][a-zA-Z0-9_]*)\s+
          (?P<regex>(\S|(\\\ ))+)\s*
    $''', flags=re.X)

    syntax_rule_re = re.compile(r"([a-zA-Z_][a-zA-Z_0-9]*):\s*$")
    syntax_symbol_re = re.compile(r"([a-zA-Z_][a-zA-Z_0-9]*)")
    syntax_action_re = re.compile(r'\:')
    syntax_stoken_re = re.compile(r'\"((.|\\\")+?)\"')
    syntax_empty_re = re.compile(r'%empty')
    syntax_error_re = re.compile(r'%error')
    syntax_prec_re = re.compile(r'%prec\s*\(\s*([a-zA-Z_][a-zA-Z_0-9]*)\s*\)')
    syntax_AST_re = re.compile(r'%AST\s*\(\s*([a-zA-Z_][a-zA-Z_0-9]*)\s*\)')
    syntax_binding_re = re.compile(r'%left|%right|%nonassoc')
    syntax_binding_param_re = re.compile(r'''
    (,\s*)?
    ((?P<token>[a-zA-Z_][a-zA-Z_0-9]*)|
    (?P<stoken>\"(.|\\\")+?\"))''',
                                         flags=re.X)

    ast_list_re = re.compile(r'%list\s+([a-zA-Z_][a-zA-Z_0-9]*)')
    ast_visitor_re = re.compile(r'%visitor\s+([a-zA-Z_][a-zA-Z_0-9]*)')

    def __init__(self, grammar_file, logger, filename=None):
        self.logger = logger

        self._syntax = Syntax()

        self._grammar_file = grammar_file
        self._grammer_file_name = filename
        self._line = 0

        # ugly state variable available to the subparsers
        self._current = None
        # even more ugly state ... only usable by one subparser
        self._assoc_defs = dict()
        self._assoc_power = 0
        self._production_number = 0
        self._indent = None

        self._state = self.header

    def error(self, message):
        """
        Wrapper for the logging.error method to include the current
        line number in the error message.
        """
        if self._grammar_file_name is not None:
            self.logger.error('{}:{}: {}'.format(self._grammar_file_name,
                                                 self._line, message))
        else:
            self.logger.error('line {}: {}'.format(self._line, message))

    def warning(self, message):
        """
        Wrapper for the logging.warning method to include the current
        line number in the error message.
        """
        if self._grammar_file_name is not None:
            self.logger.warning('{}:{}: {}'.format(self._grammar_file_name,
                                                   self._line, message))
        else:
            self.logger.warning('line {}: {}'.format(self._line, message))

    def header(self, line, eof=False):
        """
        Parse header lines.
        """
        if eof:
            return

        self._syntax.header.add(line)

    def footer(self, line, eof=False):
        """
        Parse footer lines.
        """
        if eof:
            return

        self._syntax.footer.add(line)

    def AST(self, line, eof=False):
        """
        Parse AST spec lines.
        """

        if eof:
            return

        match = self.ast_list_re.match(line)
        if match:
            self._syntax.AST_info.list(match.group(1))
            return

        match = self.ast_visitor_re.match(line)
        if not match:
            self.error("invalid AST spec")
            return

        self._syntax.AST_info.visitor = match.group(1)

    def lexer_defs(self, line, eof=False):
        """
        Parse lines of a %def-section in a lexer.

        Switch back to `lexer` when there is an unindent.

        Uses self._indent.
        """
        if eof:
            return

        indent = self.indention(line)
        if self._indent is None:
            self._indent = indent

        if indent < self._indent:
            self._indent = None
            self._state = self.lexer
            return self.lexer(line)

        match = self.lexing_named_pattern_line_re.match(line.strip())
        if match:
            try:
                self._syntax.lexer.add_named_pattern(
                    match.group('name'),
                    Regex(match.group('regex'),
                          bindings=self._syntax.lexer.named_patterns()).ast)
            except (RegexSyntaxError, SyntaxNameError) as e:
                self.error("syntax error in regex def: {}".format(e.args[0]))
        else:
            self.error("invalid named pattern spec")


    def lexer(self, line, eof=False):
        """
        Parse a lexer.

        Switches to lexer_defs on seeing %def.
        """
        if eof:
            return

        match = self.lexing_statedef_re.match(line)
        if match:
            statenames = \
                [name.strip() for name in match.group('names').split(',')]
            statenames = sum([name.split() for name in statenames], [])
            try:
                if match.group('type') == '%x':
                    for name in statenames:
                        self._syntax.lexer.add_exclusive_initial_condition(name)
                elif match.group('type') == '%s':
                    for name in statenames:
                        self._syntax.lexer.add_inclusive_initial_condition(name)
                elif match.group('type') == '%nullmatch':
                    for name in statenames:
                        self._syntax.lexer.initial_condition(name).declare_nullmatch()
                else:
                    raise CantHappen()
            except SyntaxNameError as e:
                self.error(str(e))
            return

        match = self.lexing_named_pattern_def_re.match(line)
        if match:
            if match.group('one'):
                try:
                    self._syntax.lexer.add_named_pattern(
                        match.group('name'),
                        Regex(match.group('regex'),
                              bindings=self._syntax.lexer.named_patterns()).ast)
                except (RegexSyntaxError, SyntaxNameError) as e:
                    errmsg = "syntax error in regex def: {}".format(e.args[0])
                    self.error(errmsg)
            else:
                self._state = self.lexer_defs
                return


        match = self.lexing_rule_re.match(line)
        state = set()

        if not match:
            self.error("invalid token spec")
            return

        # determine the inital condtions
        if match.group('sol'):
            state.add(self._syntax.lexer.initial_condition("$SOL"))

        if match.group('initialNames'):
            names = \
                [name.strip() for name in match.group('initialNames').split(',')]
            for name in names:
                try:
                    state.add(self._syntax.lexer.initial_condition(name))
                except  SyntaxNameError as e:
                    errmsg = \
                        "error in start condition list: {}".format(e.args[0])
                    self.error(errmsg)


        # collect actions
        action = List()

        if match.group('debug'):
            action.append(Debug(match.group('debug')))

        def begin_matcher(head, args):
            if match.group(head):
                if match.group(head) == '%begin':
                    action.append(Begin(
                            self._syntax.lexer.initial_condition(match.group(args))))
                elif match.group(head) == '%push':
                    action.append(Push(
                            self._syntax.lexer.initial_condition(match.group(args))))
                elif match.group(head) == '%pop':
                    if match.group(args):
                        self.error("state argument for %pop")
                    action.append(Pop())
                elif match.group(head) == '%function':
                    action.append(Function(match.group(args)))
                else:
                    self.error("invalid lexing action")
                    return True
            return False

        try:
            for type_str, action_str in [('beginType', 'begin'),
                                         ('beginType2', 'begin2'),
                                         ('beginType3', 'begin3')]:
                if begin_matcher(type_str, action_str):
                    return
        except SyntaxNameError as e:
            self.error( "error in lexaction: {}".format(e.args[0]))

        if match.group('restart'):
            action.append(Restart())

        elif match.group('token'):
            self._syntax.symtable.define_terminal(match.group('token'))
            action.append(Token(match.group('token')))

        elif match.group('continue'):
            action.append(Continue())

        # put it all together, add a lexing rule
        try:
            regex = Regex(match.group('regex'),
                          bindings=self._syntax.lexer.named_patterns())
        except RegexSyntaxError as e:
            self.error("syntax error in regex: {}".format(e.args[0]))
        else:
            self._syntax.lexer.add_lexing_rule(LexingRule(state, regex, action))

    def parser(self, line, eof=False):
        """
        Parse the parser.

        Uses `self._current` to keep track of its state. Switches to
        `action` for parsing semantic action.
        """
        if eof:
            return

        if self._current is None:
            match = self.syntax_binding_re.match(line)
            obj = None

            if match:
                if match.group(0) == '%left':
                    obj = Production.LEFT, self._assoc_power
                elif match.group(0) == '%right':
                    obj = Production.RIGHT, self._assoc_power
                elif match.group(0) == '%nonassoc':
                    obj = Production.NONASSOC, self._assoc_power

                line = line[len(match.group(0)):]
                line = line.strip()

                while line:
                    match = self.syntax_binding_param_re.match(line)
                    if match:
                        groupdict = match.groupdict()
                        if groupdict['token'] is not None:
                            self._assoc_defs[groupdict['token']] = obj
                        else:
                            text, normal_name = self._syntax.normalize_s_token_name(groupdict['stoken'])
                            self._assoc_defs[normal_name] = obj

                        line = line[len(match.group(0)):]
                        line = line.strip()
                    else:
                        self.error("Syntax error in associativity definition")
                        return

                self._assoc_power += 1
                return

        match = self.syntax_rule_re.match(line)
        if match:
            symbol = self._syntax.symtable.define_meta(match.group(1))

            if self._syntax.grammar.start_symbol is None:
                self._syntax.grammar.start_symbol = symbol

            self._current = symbol

        else:
            prod = Production(self._current, [], self._production_number)
            self._production_number += 1
            line = line.strip()

            while line:
                elem = None

                # this loop is broken not beautiful, but more readable
                # than all other solutions (I don't want to nest ifs
                # to thirty levels) effectively this simulates goto to
                # common code
                while True:

                    match = self.syntax_stoken_re.match(line)
                    if match:
                        elem = self._syntax.define_s_token(match.group(0))
                        break

                    match = self.syntax_symbol_re.match(line)
                    if match:
                        elem = self._syntax.symtable.require_symbol(match.group(1), self._line)
                        break

                    match = self.syntax_empty_re.match(line)
                    if match:
                        break

                    match = self.syntax_error_re.match(line)
                    if match:
                        elem = self._syntax.symtable.require_recover()
                        break

                    match = self.syntax_prec_re.match(line)
                    if match:
                        try:
                            prod.assoc = self._assoc_defs[match.group(1)]
                        except KeyError:
                            errmsg = "line {}: precedence of symbol used in %prec undefined".format(self._line)
                            self.error(errmsg)

                        break

                    match = self.syntax_AST_re.match(line)
                    if match:
                        self._syntax.AST_info.bind(prod, match.group(1))
                        break

                    match = self.syntax_action_re.match(line)
                    if match:
                        line = line[len(match.group(0)):]
                        line = line.strip()

                        if line:
                            prod.action = line
                            self._current.add_prod(prod)
                        else:
                            self._state = self.action
                            self._current = prod

                        return

                    self.error("syntax error ({})".format(line))
                    return

                line = line[len(match.group(0)):]
                line = line.strip()

                if elem:
                    prod.assoc = self._assoc_defs.get(elem.name, prod.assoc)
                    prod.add_sym(elem)

            self._current.add_prod(prod)

    @staticmethod
    def indention(line):
        """
        Return the amount of indention of line.
        """
        ind = 0

        for char in line:
            if char == ' ':
               ind += 1
            elif char == '\t':
                logging.getLogger('pyLR1').warning(
                    "Tab used for significant indention!")
                ind += 8
            else:
                break

        return ind

    def action(self, line, eof=False):
        """
        Get inline python code. Uses `self._indent` to keep
        track. Switches back do `parser` on unindents.
        """
        if eof:
            self._current.left.add_prod(self._current)
            return

        indent = self.indention(line)
        if self._indent is None:
            self._indent = indent

        if indent < self._indent:
            self._state = self.parser
            self._current.left.add_prod(self._current)
            self._current = self._current.left
            self._indent = None
            return self._state(line)

        def unindent(line):
            "Reindent line to be offset from the baseline self._indent"
            ind = self.indention(line)
            line = line.strip()

            return " " * (ind - self._indent) + line

        if self._current.action is None:
            self._current.action = ""

        self._current.action = self._current.action + "\n" + unindent(line)

    def parse(self):
        """
        Parse the given grammar file.
        """
        self._line = 0

        for line in self._grammar_file:
            self._line += 1

            if self.comment_re.match(line):
                pass
            elif self.ast_re.match(line):
                self._state = self.AST
                self._syntax.AST_info.set_used()
            elif self.parser_re.match(line):
                self._state = self.parser
            elif self.lexer_re.match(line):
                self._state = self.lexer
            elif self.footer_re.match(line):
                self._state = self.footer
            else:
                self._state(line)

        # notify the current state of eof
        # apply any pending state
        self._state('', eof=True)

        for symbol, lines in sorted(self._syntax.symtable.undef(),
                                    key=lambda x: x[0].name):
            usedinlines = "used in lines"
            if len(lines) == 1:
                usedinlines = "used in line"
            self.logger.error(' '.join(["Undefined symbol",
                                        symbol.name,
                                        usedinlines,
                                        ', '.join(str(line)
                                                  for line
                                                  in lines)]))

        return self._syntax
