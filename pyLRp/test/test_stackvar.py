#!/usr/bin/python3

import unittest

import sys
import io
import logging

from . import utils

class TestStackVar(utils.FailOnLogTestCase,
                   utils.ParseResultTestCase):
    """
    Test the correctness of stack var references

    XXX: Most or all of these tests use the result of the generated
    parser for verification, this is not clean unit testing. It would
    be better to test the generated syntax description, but as the
    final translation is done on writing, it is not possible to do so
    correctly.
    """

    def test_bacis_refs(self):
        """
        Test stack var substitution works at all
        """
        parser, syntax = self.compile(r"""
%lexer
\s+ %restart
[a-zA-Z_][a-zA-Z0-9_]* NAME
0+|[1-9][0-9]* INT

%parser

term:
    exp: $$.sem = $1.sem
    term "+" exp: $$.sem = $1.sem + $3.sem
    term "-" exp: $$.sem = $1.sem - $3.sem

exp:
    value:  $$.sem = $1.sem
    value "*" exp: $$.sem = $1.sem * $3.sem
    value "/" exp: $$.sem = $1.sem // $3.sem

value:
    "(" term ")":  $$.sem = $2.sem
    "-" value: $$.sem = -$2.sem
    INT: $$.sem = int($1.sem)
""")

        self.verify_parse_result(parser, b"2/3", 0)
        self.verify_parse_result(parser, b"2-3", -1)
        self.verify_parse_result(parser, b"(2)", 2)

    def test_num_ge_10(self):
        """
        Test for correct handling of numeric references with numbers
        greater than or equal to 10.
        """
        self.logger = utils.unique_logger()
        parser, syntax = self.compile(r"""
%lexer
\s+ %restart
(0+|[1-9][0-9]*) INT
%parser

multiint:
    int int int int int int int int int int int int int int:
        $$.sem = [i.sem for i in ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11,
                                  $12, $13, $14)]

int:
    INT: $$.sem = int($1.sem)
    "-" int: $$.sem = -$2.sem
""")

        self.verify_parse_result(parser, b"1 2 3 4 5 6 7 8 9 10 11 12 13 14",
                                 list(range(1,15)))


    def test_named_refs(self):
        """
        Test for correctness of named references, and named references
        mixed with numerical references.
        """
        parser, syntax = self.compile(r"""
%lexer
\s+ %restart
[a-zA-Z_][a-zA-Z0-9_]* NAME
0+|[1-9][0-9]* INT

%parser

term[res]:
    exp: $term.sem = $exp.sem
    term "+" exp: $$.sem = $1.sem + $exp.sem
    term "-" exp: $res.sem = $1.sem - $exp.sem

exp[res]:
    value:  $$.sem = $value.sem
    exp "*" value: $res.sem = $1.sem * $value.sem
    exp[dividend] "/" value[divisor]: $res.sem = $dividend.sem // $divisor.sem

value:
    "(" term ")":  $value.sem = $term.sem
    "-" value[inv]: $$.sem = -$inv.sem
    INT: $value.sem = int($INT.sem)
""")

        self.verify_parse_result(parser, b"2/3", 0)
        self.verify_parse_result(parser, b"2-3", -1)
        self.verify_parse_result(parser, b"(2)", 2)


class TestStackVarErrors(utils.MessageAssertTestCase):
    """
    Test ambiguous and erroneous references are reported
    """

    def test_missing_ref(self):
        """
        Check for errors, when referencing an undefined stack var reference
        """

        source = r"""%lexer
a A
b B
c C

%parser

a:
    A a: print($b.sem)
    b

b:
    B[theb]: print($tehb.sem)
    B B: print($3.sem)
    c: print($res.sem)

c[res]:
    C C: print($ret.sem)
"""

        def logmessages():
            msg = yield
            self.assertRegex(msg.getMessage(), r'')

            while True:
                msg = yield
                sefl.fail("superfluous log message")

        parser, syntax = self.compile_checked(source, logmessages())


    def test_ambiguous_ref(self):
        source = r"""%lexer
a A
b B
c C

%parser

a:
    A a: print($a.sem)
    b

b:
    B: print($B.sem)
    B B: print($B.sem)
    c: print($c.sem)

c[C]:
    %empty
    C: print($C.sem)
"""
        def logmessages():
            msg = yield
            self.assertTegex(msg.getMessage(), r'')

            while True:
                msg = yield
                sefl.fail("superfluous log message")

        parser, syntax = self.compile_checked(source, logmessages())
