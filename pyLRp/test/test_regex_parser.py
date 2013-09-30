
import unittest

from .. import regex as Regex

class RegexParserTestCase(unittest.TestCase):

    def test_regex_parser(self):

        for regex, str_rep in [(r'[]', "CharacterRegex([])"),
                               (r'', "EmptyRegex()"),
                               (r'|a', "OrRegex(EmptyRegex(), CharacterRegex(['a']))"),
                               (r'a|', "OrRegex(CharacterRegex(['a']), EmptyRegex())"),
                               (r'a|b*', "OrRegex(CharacterRegex(['a']),"
                                " RepeatorRegex(CharacterRegex(['b'])))"),
                               (r'a{3}', "SequenceRegex(CharacterRegex(['a']),"
                                " SequenceRegex(CharacterRegex(['a']), CharacterRegex(['a'])))"),
                               (r'a{3,}', "SequenceRegex(CharacterRegex(['a']),"
                                " SequenceRegex(CharacterRegex(['a']), SequenceRegex(CharacterRegex(['a']),"
                                " RepeatorRegex(CharacterRegex(['a'])))))"),
                               (r'a{1,2}', "SequenceRegex(CharacterRegex(['a']),"
                                " OrRegex(CharacterRegex(['a']), EmptyRegex()))")]:
            self.assertEqual(str(Regex.Regex(regex).ast), str_rep)

    def test_char_class_operators(self):
        for regex, str_rep in [
            # basic function
            (r'[a-f]{&}[c-z]', "CharacterRegex(['c', 'd', 'e', 'f'])"),
            (r'[a-k]{-}[d-z]', "CharacterRegex(['a', 'b', 'c'])"),
            (r'[abc]{|}[efg]',
             "CharacterRegex(['a', 'b', 'c', 'e', 'f', 'g'])"),
            # associativity and precedence
            (r'a{|}a{-}a', "CharacterRegex([])"),
            (r'a{-}a{&}a', "CharacterRegex([])"),
            (r'a{|}b{&}a', "CharacterRegex(['a'])"),
            (r'[abc]{-}([abc]{&}[cde])', "CharacterRegex(['a', 'b'])")
            ]:
            self.assertEqual(str(Regex.Regex(regex).ast), str_rep)


    def test_regex_parser_errors(self):
        for regex, text in [(r'[', r'unclosed character class'),
                            (r']', r'single closing bracket'),
                            (r'a|*', r"missing argument for \'\*\' operator"),
                            (r'*', r"missing argument for \'\*\' operator"),
                            (r'ab+|(cd*', r'missing closing paren'),
                            (r'ab+|cd)*', r'superfluous closing paren'),
                            (r'|+', r"missing argument for \'\+\' operator"),
                            (r'[+-][0-9]+', r"incomplete range in character class"),
                            (r'|?', r"missing argument for \'\?\' operator")]:
            self.assertRaisesRegex(Regex.RegexSyntaxError, text,
                                   Regex.Regex, regex)

    def test_bindings(self):
        self.assertEqual(str(Regex.Regex(r'{foo}',
                                         {'foo': Regex.CharacterRegex('b')}).ast),
                         "CharacterRegex(['b'])")

        # test that {name} is treated as a SEQ {foo} in trailing position
        self.assertEqual(str(Regex.Regex(r'a{foo}',
                                         {'foo': Regex.CharacterRegex('b')}).ast),
                         "SequenceRegex(CharacterRegex(['a']), CharacterRegex(['b']))")

        self.assertRaisesRegex(Regex.RegexSyntaxError, 'unbound named pattern {baz}',
                               Regex.Regex, r'{baz}')

        self.assertRaisesRegex(Regex.RegexSyntaxError, "comma in named regex reference",
                               Regex.Regex, r'{baz,}', bindings={'baz': None})


