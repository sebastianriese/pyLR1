
import unittest
import sys
import logging

import test.utils as utils
import pyLRp

class DefaultConditionsTestCase(utils.FailOnLogTestCase,
                                utils.ParseResultTestCase):

    def test_sof(self):
        parser, _ = self.compile(r"""
# epl (expressive parrot language)
%lexer

\s+ %restart

# allow shebang
<<SOF>>\#!.* %restart

# otherwise the language has "" comments
"[^"]*" %restart

# and parrots
[Tt]his THIS
parrot PARROT
is IS
dead DEAD
\#! FAKE

%parser

doc:
    %empty: $$.sem = []
    doc THIS PARROT IS DEAD "!": $$.sem = $1.sem + ['parrot']
    doc FAKE: $$.sem = $1.sem + ['fake']
""")

        # correct shebang
        self.verify_parse_result(parser, br"""#! shebang comment
This "ljljlkj" parrot is dead!
""", ["parrot"])

        # no shebang <<SOF>> must be inclusive
        self.verify_parse_result(parser, br"""This parrot is dead!""", ["parrot"])

        # the FAKE shebang must be parsed correctly in other contexts
        self.verify_parse_result(parser, br""" #! This parrot is dead ! #!""",
                                 ["fake", "parrot", "fake"])

        # several incorrect versions
        self.verify_syntax_error(parser, br"""This#! parrot is dead!""")
        self.verify_syntax_error(parser, br"""#! parrot is dead!
#! welcome to the ministry of silly walks""")
        self.verify_syntax_error(parser, br"""
#! shebang comment
This parrot is dead!
""")
        self.verify_syntax_error(parser, br""" #! shebang comment
This "ljljlkj" parrot is dead!
""")
        self.verify_syntax_error(parser, br"""##! shebang comment
This "ljljlkj" parrot is dead!
""")

    def test_sol(self):
        parser, _ = self.compile(r"""
# yapl (yet another parrot language)
%lexer

\s+ %restart

# here for confusion and to verify longest-match sematics
<<SOF>>--c %restart

# this language has start of file --| |-- block comments
<<SOF>>--\|([^|]*|\|[^\-]|\|-[^\-])*\|-- %restart

# this language has start of line -- comments
^--.* %restart

# and parrots
[Tt]his THIS
parrot PARROT
is IS
dead DEAD

%parser

doc:
    %empty
    doc THIS PARROT IS DEAD "!"
""")

        self.verify_parse_result(parser, br"--comment", None)
        self.verify_syntax_error(parser, br" --comment")
        self.verify_parse_result(parser, br"""This
--
parrot
--
is
--
dead
-- !
!
""", None)
        self.verify_syntax_error(parser, br"""This
--
parrot
--
is --
dead
-- !
!
""")

        # test sol-sof interaction and longest match semantics for
        # %restart
        self.verify_parse_result(parser, br"""--|
  invalid but inside a comment
|--

This parrot is dead!""", None)

class UserDefinedConditionsTest(utils.FailOnLogTestCase,
                                utils.ParseResultTestCase):

    def test_inclusive(self):
        pass

    def test_exclusive(self):
        pass

