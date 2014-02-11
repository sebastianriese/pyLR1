
import unittest

from .. import regex as Regex

class RegexParserTestCase(unittest.TestCase):

    @unittest.skip("XXX: update to character filters")
    def test_regex_parser(self):

        for regex, str_rep in [
            (r'[]', "CharacterRegex(Empty())"),
            (r'', "EmptyRegex()"),
            (r'|a', "OrRegex(EmptyRegex(), CharacterRegex(Character('a')))"),
            (r'a|', "OrRegex(CharacterRegex(Character('a')), EmptyRegex())"),
            (r'a|b*', "OrRegex(CharacterRegex(Character('a')),"
             " RepeatorRegex(CharacterRegex(Character('b'))))"),
            (r'a{3}', "SequenceRegex(CharacterRegex(Character('a')),"
             " SequenceRegex(CharacterRegex(Character('a')), "
             "CharacterRegex(Character('a'))))"),
            (r'a{3,}', "SequenceRegex(CharacterRegex(Character('a')),"
             " SequenceRegex(CharacterRegex(Character('a')), "
             "SequenceRegex(CharacterRegex(Character('a')),"
             " RepeatorRegex(CharacterRegex(Character('a'))))))"),
            (r'a{1,2}', "SequenceRegex(CharacterRegex(Character('a')),"
             " OrRegex(CharacterRegex(Character('a')), EmptyRegex()))")]:
            self.assertEqual(str(Regex.Regex(regex).ast), str_rep)

    # XXX: update to character filters, or check by matching the
    # contructed filters, though this would not be clean as it would
    # actually also check the function of the filters
    @unittest.skip("XXX: update to character filters")
    def test_char_class_operators(self):
        for regex, str_rep in [
            # basic function
            (r'[a-f]{&}[c-z]', "CharacterRegex(['c', 'd', 'e', 'f'])"),
            (r'[a-k]{-}[d-z]', "CharacterRegex(['a', 'b', 'c'])"),
            (r'[abc]{|}[efg]',
             "CharacterRegex(['a', 'b', 'c', 'e', 'f', 'g'])"),
            # associativity and precedence
            (r'a{|}a{-}a', "CharacterRegex(Empty())"),
            (r'a{-}a{&}a', "CharacterRegex(Empty())"),
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
                                         {'foo': Regex.EmptyRegex()}).ast),
                         "EmptyRegex()")

        # test that {name} is treated as a SEQ {foo} in trailing position
        self.assertEqual(str(Regex.Regex(r'a{foo}',
                                         {'foo': Regex.EmptyRegex()}).ast),
                         "SequenceRegex(CharacterRegex(Character('a')), EmptyRegex())")

        self.assertRaisesRegex(Regex.RegexSyntaxError, 'unbound named pattern {baz}',
                               Regex.Regex, r'{baz}')

        self.assertRaisesRegex(Regex.RegexSyntaxError, "comma in named regex reference",
                               Regex.Regex, r'{baz,}', bindings={'baz': None})
