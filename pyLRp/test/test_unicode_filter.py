
import unittest

from pyLRp.unicode.filter import *

class UnicodeFilterTest(unittest.TestCase):

    def test_negation(self):
        self.assertEqual(Negation(Negation(Character('c'))),
                         Character('c'))

    def test_normalization(self):
        self.assertEqual(Union(Negation(
            Intersection(Character('c'), Character('d')))).normalize(),
            Union(Negation(Character('c')), Negation(Character('d'))))
