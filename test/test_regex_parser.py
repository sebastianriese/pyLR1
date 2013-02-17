
import unittest

import pyLRp

class RegexParserTestCase(unittest.TestCase):

    def test_regex_parser(self):

        for regex, str_rep in [(r'[]', "CharacterRegex([])"),
                               (r'', "CharacterRegex([''])"),
                               (r'|a', "OrRegex(CharacterRegex(['']), CharacterRegex(['a']))"),
                               (r'a|', "OrRegex(CharacterRegex(['a']), CharacterRegex(['']))"),
                               (r'a|b*', "OrRegex(CharacterRegex(['a']),"
                                " RepeatorRegex(CharacterRegex(['b'])))"),
                               (r'a{3}', "SequenceRegex(CharacterRegex(['a']),"
                                " SequenceRegex(CharacterRegex(['a']), CharacterRegex(['a'])))"),
                               (r'a{3,}', "SequenceRegex(CharacterRegex(['a']),"
                                " SequenceRegex(CharacterRegex(['a']), SequenceRegex(CharacterRegex(['a']),"
                                " RepeatorRegex(CharacterRegex(['a'])))))"),
                               (r'a{1,2}', "SequenceRegex(CharacterRegex(['a']),"
                                " OrRegex(CharacterRegex(['a']), CharacterRegex([''])))")]:
            self.assertEqual(str(pyLRp.Regex(regex).ast), str_rep)

    def test_regex_parser_errors(self):
        for regex, text in [(r'[', r'unclosed character class'),
                            (r']', r'single closing bracket'),
                            (r'a|*', r"missing argument for \'\*\' operator"),
                            (r'*', r"missing argument for \'\*\' operator"),
                            (r'ab+|(cd*', r'missing closing paren'),
                            (r'ab+|cd)*', r'superfluous closing paren'),
                            (r'|+', r"missing argument for \'\+\' operator"),
                            (r'|?', r"missing argument for \'\?\' operator")]:
            self.assertRaisesRegex(pyLRp.RegexSyntaxError, text,
                                   pyLRp.Regex, regex)

    def test_bindings(self):
        self.assertEqual(str(pyLRp.Regex(r'{foo}',
                                         {'foo': pyLRp.CharacterRegex('b')}).ast),
                         "CharacterRegex(['b'])")

        # test that {name} is treated as a SEQ {foo} in trailing position
        self.assertEqual(str(pyLRp.Regex(r'a{foo}',
                                         {'foo': pyLRp.CharacterRegex('b')}).ast),
                         "SequenceRegex(CharacterRegex(['a']), CharacterRegex(['b']))")

        self.assertRaisesRegex(pyLRp.RegexSyntaxError, 'unbound named pattern {baz}',
                               pyLRp.Regex, r'{baz}')

        self.assertRaisesRegex(pyLRp.RegexSyntaxError, "comma in named regex reference",
                               pyLRp.Regex, r'{baz,}', bindings={'baz': None})


