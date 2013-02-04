#!/usr/bin/python3

import unittest

import sys
import io
import logging

import pyLRp
import test.utils as utils

class TestGeneratedLexerErrors(utils.FailOnLogTestCase):
    """
    Test the error handling of the generated lexer
    """

    def verify_tokens(self, parser, source_and_tokens, message):
        """
        Assert a list of scanned tokens matches a given list
        disregarding position information.
        """
        for source, expected in source_and_tokens:
            lexed = [(token, literal)
                     for token, literal, pos
                     in parser["Lexer"](source, string=True).lexAll()]

            self.assertListEqual(expected, lexed, message)



    def test_invalid_char(self):
        """
        Test correct handling of encountering characters not allowed
        in the input.
        """
        parser, symtable = self.compile(r"""
%lexer
\s+ %restart
[a-zA-Z0-9]+ TOKEN
""")

        TOKEN = symtable["TOKEN"].Number()
        ERROR = symtable["$ERROR"].Number()

        test_cases = [
            (b"baked beans and spam", [(TOKEN, "baked"),
                                       (TOKEN, "beans"),
                                       (TOKEN, "and"),
                                       (TOKEN, "spam")]),
            (b"$", [(ERROR, "$")]),
            (b"$$", [(ERROR, "$"), (ERROR, "$")]),
            (b"spam and$ eggs", [(TOKEN, "spam"),
                                 (TOKEN, "and"),
                                 (ERROR, "$"),
                                 (TOKEN, "eggs")]),
            (b"eggs bacon and spam$", [(TOKEN, "eggs"),
                                       (TOKEN, "bacon"),
                                       (TOKEN, "and"),
                                       (TOKEN, "spam"),
                                       (ERROR, "$")])
            ]

        self.verify_tokens(parser, test_cases,
        "incorrect error token handling")

    def test_invalid_token(self):
        """
        Test allowed character in a forbidden position.
        """
        parser, symtable = self.compile(r"""
%lexer
\s+ %restart
a*b*ca*b* TOKEN
""")
        TOKEN = symtable["TOKEN"].Number()
        ERROR = symtable["$ERROR"].Number()

        test_cases = [
            (b"aaabbcab", [(TOKEN, "aaabbcab")]),
            (b"aaabbab", [(ERROR, "aaabba"), (ERROR, "b")]),
            (b"aaaa", [(ERROR, "aaaa")])
            ]

        self.verify_tokens(parser, test_cases,
                           "incorrect handling of malformed lexeme")


class TestGeneratedParserErrors(utils.FailOnLogTestCase,
                                utils.ParseResultTestCase):
    """
    Test the error handling of the generated parser
    """

    def test_overscan(self):
        """
        Test what happens if there is a token that scans till EOF and
        what happens then, when no token can be identified.
        """

        parser, symtable = self.compile(r"""
%lexer
\s+ %restart
"(.|\"|\s)*" %restart
abc ABC
%ast
%list doc
%parser

doc:
   %empty
   doc ABC
""")

        source = br"""
"This should be a comment, but the lexer spec is
faulty, so that the comment rule matches greedily everything
between the first and last quotation mark"
abc abc abc
abc abc abc
"""

        self.verify_parse_result(parser, source, ["abc"] * 6)

        source = br"""
"
abc abc abc
abc abc abc
"""
        self.verify_syntax_error(parser, source)
