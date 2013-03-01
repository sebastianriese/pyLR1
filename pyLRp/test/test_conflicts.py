
import unittest
import sys
import logging

from . import utils

class CompilationMessagesTestCase(utils.ParseResultTestCase):

    def compile_checked(self, source, logcheck):
        self.logger = utils.unique_logger()
        self.logger.setLevel('WARNING')
        logcheckHandler = utils.CheckingHandler(logcheck)
        self.logger.addHandler(logcheckHandler)
        self.logger.propagate = False

        return utils.compile(self.logger, source, trace=False)

    def test_shift_reduce(self):
        source = r"""%lexer
\s+ %restart

if IF
else ELSE
body BODY

%parser

x:
    BODY: $$.sem = 'body'
    IF x ELSE x: $$.sem = ('if', $2.sem, 'else', $4.sem)
    IF x: $$.sem = ('if', $2.sem)
"""

        def logmessages():
            msg = yield
            self.assertRegex(msg.getMessage(), r'shift/reduce',
                             'did not recognize shift/reduce-conflict')
            msg = yield
            self.assertRegex(msg.getMessage(), r'1 conflict',
                             'did not count conflicts properly')
            while True:
                msg = yield
                self.fail("superfluous log message")

        module, symtable = self.compile_checked(source, logmessages())

        self.verify_parse_result(module, b"if if body else body ",
                                 ('if', ('if', 'body', 'else', 'body')))

    def test_reduce_reduce(self):
        source = r"""
%lexer

\s+ %restart

a A

%parser

x:
    %empty: $$.sem = ()
    y: $$.sem = ('x', $1.sem)
    A x: $$.sem = ('x', $2.sem)

y:
    A x: $$.sem = ('y', $2.sem)
"""
        def logmessages():
            msg = yield
            self.assertRegex(msg.getMessage(), r'reduce/reduce',
                             'did not recognize reduce/reduce-conflict')
            msg = yield
            self.assertRegex(msg.getMessage(), r'1 conflict',
                             'did not count conflicts properly')
            while True:
                msg = yield
                self.fail("superfluous log message")

        module, symtable = self.compile_checked(source, logmessages())
        self.verify_parse_result(module, b"   ", ())
        self.verify_parse_result(module, b"a ", ('x', ()))
        self.verify_parse_result(module, b"aa ", ('x', ('x', ())))
        self.verify_parse_result(module, b"aaaa ", ('x', ('x', ('x', ('x', ())))))

class PrecedenceDeclarationsTestCase(utils.FailOnLogTestCase,
                                     utils.ParseResultTestCase):
    def test_precedence(self):
        module, symtable = self.compile(r"""
%lexer

\s+ %restart

[0-9]+ INT

%parser

%left "and"
%nonassoc "=="
%left "+" "-"
%left "*" "/"
%right "^"
%right UNARY

expr:
    expr "==" expr: $$.sem = ["==", $1.sem, $3.sem]
    "(" expr ")": $$.sem = $2.sem
    INT: $$.sem = int($1.sem)
    "-" expr %prec(UNARY): $$.sem = ["-", $2.sem]
    expr "+" expr: $$.sem = ["+", $1.sem, $3.sem]
    expr "-" expr: $$.sem = ["-", $1.sem, $3.sem]
    expr "*" expr: $$.sem = ["*", $1.sem, $3.sem]
    expr "^" expr: $$.sem = ["^", $1.sem, $3.sem]
    expr "/" expr: $$.sem = ["/", $1.sem, $3.sem]
    expr "and" expr: $$.sem = ["and", $1.sem, $3.sem]
""")

        # some checks the parser does not accept nonsense
        self.verify_syntax_error(module, b"1 2 3")
        self.verify_syntax_error(module, b"==")
        self.verify_syntax_error(module, b"and == +")
        self.verify_syntax_error(module, b"(((==)))")

        # check the %prec() declaration
        self.verify_parse_result(module, b"-3*5",
                                 ["*", ["-", 3], 5])
        self.verify_parse_result(module, b"--3*5",
                                 ["*", ["-", ["-", 3]], 5])

        # verify associativity for all operators within one class
        self.verify_parse_result(module, b"1*2*3/4/5",
                                 ["/",["/",["*",["*",1,2],3],4],5])
        self.verify_parse_result(module, b"1+2+3-4-5",
                                 ["-",["-",["+",["+",1,2],3],4],5])
        self.verify_syntax_error(module, b"1 == 2 == 3")
        self.verify_parse_result(module, b"1^2^3", ["^",1,["^",2, 3]])

        # verify some more complex examples
        # XXX: make this more systematic and exhaustive
        self.verify_parse_result(module, b"1+2*3==5",
                                 ["==", ["+", 1, ["*", 2, 3]], 5])
        self.verify_parse_result(module, b"(1+2)*3==5",
                                 ["==", ["*", ["+", 1, 2], 3], 5])
        self.verify_parse_result(module, b"-2^-3", ["^", ["-", 2], ["-", 3]])
        self.verify_parse_result(module, b"1 == 2 and 3*5+7 == 22",
                                 ["and", ["==", 1, 2],
                                  ["==", ["+", ["*", 3, 5], 7], 22]])

        # is this a bug? but how should this work anyway
        # self.verify_syntax_error(module, b"1 == (2 == 3)")
