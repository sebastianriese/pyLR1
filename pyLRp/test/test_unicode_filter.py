
import unittest

from pyLRp.unicode.filter import *

class UnicodeFilterTest(unittest.TestCase):

    def test_equal_predicate(self):
        a = Range('a', 'z')
        b = Character('b')
        B = Character('b')
        e = Empty()
        all_ = All()

        self.assertNotEqual(a, b)
        self.assertNotEqual(a, B)
        self.assertNotEqual(e, b)
        self.assertNotEqual(e, all_)
        self.assertEqual(b, B)

    def test_operations(self):
        a = Range('a', 'z')
        b = Character('A')
        c = Category('Lu')
        d = Character('D')
        e = Character('E')
        f = Character('F')
        na, nb, nc, nd, ne, nf = (Negation(i) for i in (a, b, c, d, e, f))

        self.assertEqual(~a, Negation(a))
        self.assertEqual(~~a, a)
        self.assertEqual(a & c,
                         CharacterFilter([[a, c]]))
        self.assertEqual(~(a & c),
                         CharacterFilter([[Negation(a)],
                                          [Negation(c)]]))
        self.assertEqual(~((a & b) | (c & d) | (e & f)),
                         CharacterFilter([[na, nc, ne], [na, nc, nf],
                                          [na, nd, ne], [na, nd, nf],
                                          [nb, nc, ne], [nb, nc, nf],
                                          [nb, nd, ne], [nb, nd, nf]]))
        self.assertEqual(((c & d) | (e & f)) & (a | b),
                         CharacterFilter([[c, d, a], [c, d, b], [e, f, a],
                                          [e, f, b]]))
