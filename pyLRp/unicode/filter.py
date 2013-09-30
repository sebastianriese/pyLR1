"""
Character filters, used to build up the alphabet for the unicode
lexer.

from, to and character values must be given consistently either as
unicode strings or numbers.
"""

# TODO: use more datasources/compile your own database
import unicodedata
from itertools import chain, product

from ..core import AutoAccept
from ..alphabet import Alphabet


# DRAFT IDEA:
#
# Keep the filter always in normal form, on addition
# of a new constraint, just juggle the code
# this greatly reduces complexity!
# There is only one container: the normalized expression
# which allows operations to roll in conditions
# the normalized expression is of the form:
# (a & b & c) | (a & d & c)
# where a, b, c, d is a simple predicate or it's negation
# any Boolean expression may be brought to this form which
# is very useful for our purposes.

class CharacterFilter(metaclass=AutoAccept):

    _subclasses_ = []

    def __eq__(self, other):
        return isinstance(other, type(self))

    def __hash__(self):
        return id(type(self))

    @property
    def empty(self):
        return False

    def normalize(self):
        return self

    def simplify(self):
        return self

    def match(self, char):
        return False

class Union(CharacterFilter):

    def __init__(self, *children):
        self._children = frozenset(children)

    def __eq__(self, other):
        return isinstance(other, Union) and \
            self._children == other._children

    def __hash__(self):
        return id(type(self)) ^ hash(self._children)

    def __str__(self):
        return "Union({})".format(', '.join(map(str, self._children)))

    @property
    def empty(self):
        return all(child.empty for child in self._children)

    def normalize(self):
        normalized_children = (child.normalize() for child in self._children)

        new_children = []
        for child in normalized_children:
            if isinstance(child, Union):
                new_children += child._children
            else:
                new_children.append(child)

        result = Union(*new_children)
        if result.empty:
            return Empty()
        return result

    def match(self, char):
        return any(child.match(char) for child in self._children)

class Intersection(CharacterFilter):

    def __init__(self, *children):
        self._children = frozenset(children)

    def __eq__(self, other):
        return isinstance(other, Instance) and \
            self._children == other._children

    def __hash__(self):
        return id(type(self)) ^ hash(self._children)

    def __str__(self):
        return "Intersection({})".format(', '.join(map(str, self._children)))

    @property
    def empty(self):
        return any(child.empty for child in self._children)

    def normalize(self):
        normalized_children = (child.normalize() for child in self._children)

        new_children = []
        for child in normalized_children:
            if isinstance(child, Intersection):
                new_children += child._children
            else:
                new_children.append(child)

        if not new_children:
            return All()

        result = Intersection(*new_children)
        if result.empty:
            return Empty()
        return result

    def simplify(self):
        # this is O(n^2) but it is short circuiting
        # and as A contradicts B is not transitive it
        # can not be optimized
        if any(chain(contradicts(a, b)
                     for (a, b) in product(self._children, repeat=2))):
            return Empty()
        else:
            return self

    def match(self, char):
        return all(child.match(char) for child in self._children)

class Empty(CharacterFilter):

    def __str__(self):
        return "Empty()"

    @property
    def empty(self):
        return True

    def match(self, char):
        return False

class All(CharacterFilter):

    def __str__(self):
        return "All()"

    @property
    def empty(self):
        return False

    def match(self, char):
        return True

class Range(CharacterFilter):

    def __init__(self, from_, to):
        self._from = from_
        self._to = to

    def __eq__(self, other):
        return isinstance(other, Range) and \
            self._from == other._from and self._to == other._to

    def __hash__(self):
        return id(type(self)) ^ hash(self._from) ^ hash(self._to)

    def __str__(self):
        return "Range({}, {})".format(self._from, self._to)

    @property
    def empty(self):
        return self._from > self._to

    def match(self, char):
        return self._from <= char <= self._to

class Character(CharacterFilter):

    def __init__(self, char):
        self._char = char

    def __eq__(self, other):
        return isinstance(other, Character) and \
            self._char == other._char

    def __hash__(self):
        return id(type(self)) ^ hash(self._char)

    def __str__(self):
        return "Character({})".format(repr(self._char))

    def match(self, char):
        return char == self._char

class Category(CharacterFilter):

    def __init__(self, category):
        self._category = category

    def __eq__(self, other):
        return isinstance(other, Category) and \
            self._category == other._category

    def __hash__(self):
        return id(type(self)) ^ hash(self._category)

    def __str__(self):
        return "Category({})".format(repr(self._category))

    def match(self, char):
        return self._category == unicodedata.category(char)

class Negation(CharacterFilter):

    def __new__(cls, child):
        """
        Directly dissolve double negations
        """
        if isinstance(child, Negation):
            # this is only safe, if there are no double negations
            # in existence: this is assured by this __new__ method
            # if there is no modification of self._child
            # otherwise the __init__ method of the returned
            # negation will be called
            return child._child
        else:
            return super().__new__(cls)

    def __init__(self, child):
        self._child = child

    def __eq__(self, other):
        return isinstance(other, Negation) and self._child == other._child

    def __hash__(self):
        return id(type(self)) ^ hash(self._child)

    def __str__(self):
        return "Negation({})".format(str(self._child))

    def normalize(self):
        normal_child = self._child.normalize()

        if isinstance(normal_child, Intersection):
            return Union(*(Negation(subchild)
                for subchild in normal_child._children))
        elif isinstance(normal_child, Union):
            return Intersection(*(Negation(subchild)
                for subchild in normal_child._children))
        else:
            return Negation(normal_child)

    def match(self, char):
        return not self._child.match(char)

CharacterFilterVisitor = CharacterFilter.base_visitor()

CONTRADICTIONS = {
    (Union, None): lambda a, b: all(contradicts(A, b) for A in a._children),
    (Intersection, None): lambda a, b: any(contradicts(A, b)
                                           for A in a._children),
    (Character, Character): lambda a, b: a._char != b._char,
    (Character, Range): lambda a, b: not (b._from <= a._char <= b._to),
    (Range, Range): lambda a, b: b._to < a._from or a._to < b._from,
    (Category, Category): lambda a, b: a._category != b._category,
    (All, Empty): lambda a, b: True,
    (All, None): lambda a, b: False,
    (Empty, None): lambda a, b: True
}

def contradicts(a, b):
    if (a, b) in CONTRADICTIONS:
        return CONTRADICTIONS[a, b](a, b)
    elif (b, a) in CONTRADICTIONS:
        return CONTRADICTIONS[b, a](b, a)
    elif (a, None) in CONTRADICTIONS:
        return CONTRADICTIONS[a, None](a, b)
    elif (b, None) in CONTRADICTIONS:
        return CONTRADICTIONS[b, None](b, a)
    else:
        return False

class UnicodeFilterAlphabet(Alphabet):

    def __len__(self):
        return len(self._symbols)

    def __iter__(self):
        return iter(self._symbols)

    def __getitem__(self, index):
        return self._symbols[index]

    def __init__(self, transitions):
        self._symbols = self._close(transitions)

    def _close(self, transitions):
        pass
