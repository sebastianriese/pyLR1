
import unittest

import pyLRp

class RegexParserTestCase(unittest.TestCase):

    def test_regex_parser(self):

        for regex, str_rep in [(r'[]', "CharacterRegex([])"),
                               (r'', "CharacterRegex([''])"),
                               (r'|a', "OrRegex(CharacterRegex(['']), CharacterRegex(['a']))"),
                               (r'a|', "OrRegex(CharacterRegex(['a']), CharacterRegex(['']))"),
                               (r'a|b*', "OrRegex(CharacterRegex(['a']),"
                                " RepeatorRegex(CharacterRegex(['b'])))")]:
            self.assertEqual(str(pyLRp.Regex(regex).ast), str_rep)

    def test_regex_parser_errors(self):
        for regex, text in [(r'[', r'unclosed character class'),
                            (r']', r'single closing bracket'),
                            (r'a|*', r"missing argument for \'\*\' operator"),
                            (r'*', r"missing argument for \'\*\' operator"),
                            (r'ab+|(cd*', r'missing closing paren'),
                            (r'ab+|cd)*', r'superfluous closing paren'),
                            (r'|+', r"missing argument for \'\+\' operator")]:
            self.assertRaisesRegex(pyLRp.RegexSyntaxError, text,
                                   pyLRp.Regex, regex)
