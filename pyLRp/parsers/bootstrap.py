
import re

from ..core import CantHappen
from ..syntax import Syntax, SyntaxNameError
from ..regex import Regex, RegexSyntaxError
from ..lexactions import List, Debug, Push, Pop, Function, Token, Begin, Restart
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

    lexing_statedef_re = re.compile(r'(?P<type>%x|%s|%nullmatch) (?P<names>([a-zA-Z_][a-zA-Z0-9_]*(\s*,\s*)?)+)\s*$')
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
    syntax_binding_param_re = re.compile(r'(,\s*)?([a-zA-Z_][a-zA-Z_0-9]*|\"(.|\\\")+?\")')

    ast_list_re = re.compile(r'%list\s+([a-zA-Z_][a-zA-Z_0-9]*)')
    ast_visitor_re = re.compile(r'%visitor\s+([a-zA-Z_][a-zA-Z_0-9]*)')

    def __init__(self, grammar_file, logger):
        self.logger = logger

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

        self.undef = {}
        self.defined = set()

        self.state = self.Header

    def Header(self, line, eof=False):
        if eof:
            return

        self.syntax.AddHeader(line)

    def Footer(self, line, eof=False):
        if eof:
            return

        self.syntax.AddFooter(line)

    def AST(self, line, eof=False):
        if eof:
            return

        match = self.ast_list_re.match(line)
        if match:
            self.syntax.ASTInfo().list(match.group(1))
            return

        match = self.ast_visitor_re.match(line)
        if not match:
            self.logger.error("line %i, invalid AST spec" % (self.line,))
            return

        self.syntax.ASTInfo().visitor = match.group(1)

    def LexerDefs(self, line, eof=False):
        if eof:
            return

        indent = self.Indention(line)
        if self.indent is None:
            self.indent = indent

        if indent < self.indent:
            self.indent = None
            self.state = self.Lexer
            return self.Lexer(line)

        match = self.lexing_named_pattern_line_re.match(line.strip())
        if match:
            try:
                self.syntax.AddNamedPattern(match.group('name'),
                                            Regex(match.group('regex'),
                                                  bindings=self.syntax.NamedPatterns()).ast)
            except (RegexSyntaxError, SyntaxNameError) as e:
                self.logger.error("line {}: syntax error in regex def: {}".format(self.line, e.args[0]))
        else:
            self.logger.error("line {}, invalid named pattern spec".format(self.line))


    def Lexer(self, line, eof=False):
        if eof:
            return

        match = self.lexing_statedef_re.match(line)
        if match:
            statenames = [name.strip() for name in match.group('names').split(',')]
            statenames = sum([name.split() for name in statenames], [])
            try:
                if match.group('type') == '%x':
                    for name in statenames:
                        self.syntax.AddExclusiveInitialCondition(name)
                elif match.group('type') == '%s':
                    for name in statenames:
                        self.syntax.AddInclusiveInitialCondition(name)
                elif match.group('type') == '%nullmatch':
                    for name in statenames:
                        self.syntax.InitialCondition(name).DeclareNullmatch()
                else:
                    raise CantHappen()
            except SyntaxNameError as e:
                self.logger.error("line {}: {}".format(self.line, str(e)))
            return

        match = self.lexing_named_pattern_def_re.match(line)
        if match:
            if match.group('one'):
                try:
                    self.syntax.AddNamedPattern(match.group('name'),
                                                Regex(match.group('regex'),
                                                      bindings=self.syntax.NamedPatterns()).ast)
                except (RegexSyntaxError, SyntaxNameError) as e:
                    self.logger.error("line {}: syntax error in regex def: {}".format(self.line, e.args[0]))
            else:
                self.state = self.LexerDefs
                return


        match = self.lexing_rule_re.match(line)
        state = set()

        if not match:
            self.logger.error("line {}: invalid token spec".format(self.line))
            return

        # determine the inital condtions
        if match.group('sol'):
            state.add(self.syntax.InitialCondition("$SOL"))

        if match.group('initialNames'):
            names = [name.strip() for name in match.group('initialNames').split(',')]
            for name in names:
                try:
                    state.add(self.syntax.InitialCondition(name))
                except  SyntaxNameError as e:
                    self.logger.error("line {}: error in start condition list: {}".format(self.line, e.args[0]))

        # print('SOL match:', match.group('sol'), 'inital names match:', match.group('initialNames'))

        # collect actions
        action = List()

        if match.group('debug'):
            action.Append(Debug(match.group('debug')))

        def beginMatcher(head, args):
            if match.group(head):
                if match.group(head) == '%begin':
                    action.Append(Begin(self.syntax.InitialCondition(match.group(args))))
                elif match.group(head) == '%push':
                    action.Append(Push(self.syntax.InitialCondition(match.group(args))))
                elif match.group(head) == '%pop':
                    if match.group(args):
                        self.logger.error("line {}: state argument for %pop".format(self.line))
                    action.Append(Pop())
                elif match.group(head) == '%function':
                    action.Append(Function(match.group(args)))
                else:
                    self.logger.error("line {}: invalid lexing action".format(self.line))
                    return True
            return False

        try:
            if beginMatcher('beginType', 'begin'): return
            if beginMatcher('beginType2', 'begin2'): return
            if beginMatcher('beginType3', 'begin3'): return
        except SyntaxNameError as e:
            self.logger.error("line {}: error in lexaction: {}".format(self.line, e.args[0]))

        if match.group('restart'):
            action.Append(Restart())

        elif match.group('token'):
            self.syntax.RequireTerminal(match.group('token'))
            action.Append(Token(match.group('token')))

        elif match.group('continue'):
            action.Append(Continue())

        # put it all together, add a lexing rule
        try:
            regex = Regex(match.group('regex'), bindings=self.syntax.NamedPatterns())
        except RegexSyntaxError as e:
            self.logger.error("line {}: syntax error in regex: {}".format(self.line, e.args[0]))
        else:
            self.syntax.AddLexingRule(LexingRule(state, regex, action))

    def Parser(self, line, eof=False):
        if eof:
            return

        if self.current is None:
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
                        self.logger.error("line {}: Syntax error in associativity definition".format(self.line))
                        return

                self.assocPower += 1
                return

        match = self.syntax_rule_re.match(line)
        if match:
            symbol = self.syntax.RequireMeta(match.group(1))
            if symbol in self.undef:
                del self.undef[symbol]
            self.defined.add(symbol)

            if self.syntax.Start() is None:
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
                        elem = self.syntax.RequireTerminal(match.group(0), stoken=True)
                        # XXX: maybe we should do this by hand
                        self.syntax.AddInlineLexingRule(bytes(match.group(1), "utf-8").decode('unicode-escape'))
                        break

                    match = self.syntax_symbol_re.match(line)

                    if match:
                        elem = self.syntax.RequireMeta(match.group(1))
                        # terminal symbols are already defined, and returned
                        # as such
                        if self.syntax.SymTable()[elem.name].SymType() == Syntax.META and \
                                elem not in self.defined:
                            self.undef.setdefault(elem, []).append(self.line)

                        break

                    match = self.syntax_empty_re.match(line)

                    if match:
                        break

                    match = self.syntax_error_re.match(line)

                    if match:
                        elem = self.syntax.RequireTerminal("$RECOVER")
                        break

                    match = self.syntax_prec_re.match(line)
                    if match:
                        try:
                            prod.assoc = self.assocDefs[match.group(1)]
                        except KeyError:
                            self.logger.warning("%d: Erroneous precedence declaration" % self.line)

                        break

                    match = self.syntax_AST_re.match(line)
                    if match:
                        self.syntax.ASTInfo().bind(prod, match.group(1))
                        break

                    match = self.syntax_action_re.match(line)

                    if match:
                        line = line[len(match.group(0)):]
                        line = line.strip()

                        if line:
                            prod.action = line
                            self.current.add_prod(prod)
                        else:
                            self.state = self.Action
                            self.current = prod

                        return

                    self.logger.error("line %d syntax error (%s)" % (self.line,line))
                    return

                line = line[len(match.group(0)):]
                line = line.strip()

                if elem:
                    prod.assoc = self.assocDefs.get(elem.name, prod.assoc)
                    prod.add_sym(elem)

            self.current.add_prod(prod)

    @staticmethod
    def Indention(line):
        ind = 0

        for char in line:
            if char == ' ':
               ind += 1
            elif char == '\t':
                self.logger.warning("Tab used for significant indention!")
                ind += 8
            else:
                break

        return ind

    def Action(self, line, eof=False):
        if eof:
            self.current.left.add_prod(self.current)
            return

        indent = self.Indention(line)
        if self.indent is None:
            self.indent = indent

        if indent < self.indent:
            self.state = self.Parser
            self.current.left.add_prod(self.current)
            self.current = self.current.left
            self.indent = None
            return self.state(line)

        def Unindent(line):
            ind = self.Indention(line)
            line = line.strip()

            return " " * (ind - self.indent) + line

        if self.current.action is None:
            self.current.action = ""

        self.current.action = self.current.action + "\n" + Unindent(line)

    def Parse(self):
        self.line = 0

        for line in self.grammar_file:
            self.line += 1

            if self.comment_re.match(line):
                pass
            elif self.ast_re.match(line):
                self.state = self.AST
                self.syntax.ASTInfo().set_used()
            elif self.parser_re.match(line):
                self.state = self.Parser
            elif self.lexer_re.match(line):
                self.state = self.Lexer
            elif self.footer_re.match(line):
                self.state = self.Footer
            else:
                self.state(line)

        # notify the current state of eof
        # apply any pending state
        self.state('', eof=True)

        if self.undef:
            for symbol, lines in sorted(self.undef.items(), key=lambda x: x[0].name):
                usedinlines = "used in lines"
                if len(lines) == 1: usedinlines = "used in line"
                self.logger.error(' '.join(["Undefined symbol", symbol.name, usedinlines,
                                  ', '.join(str(line) for line in lines)]))
            self.logger.error("Undefined meta symbols found")

        return self.syntax
