"""
Character filters, used to build up the alphabet for the unicode
lexer.

from, to and character values must be given consistently either as
unicode strings or numbers.
"""

# TODO: use more datasources/compile your own database
import unicodedata
from itertools import chain, product
from functools import partial

from ..alphabet import Alphabet


# How the filters are represented:
#
# Keep the filter always in normal form, on addition of a new
# constraint, just juggle back to normal form this greatly reduces
# complexity!
#
# There is only one container: the normalized expression which allows
# operations to roll in conditions the normalized expression is of the
# form:
# (a & b & c) | (a & d & c)
# where a, b, c, d is a simple predicate or its negation any Boolean
# expression may be brought to this form which is very useful for our
# purposes.

class CharacterFilter:

    def __init__(self, groups):
        self._matchers = frozenset(frozenset(group) for group in groups)

    def __str__(self):
        return "CharacterFilter({})".format(str(self._matchers))

    def __eq__(self, other):
        return isinstance(other, CharacterFilter) and \
            self._matchers == other._matchers

    def __or__(self, other):
        if isinstance(other, CharacterFilter):
            return CharacterFilter(self._matchers | other._matchers)
        elif isinstance(other, CharaterMatcher):
            return CharacterFilter(self._matchers | set(set([other])))
        else:
            raise TypeError

    def __and__(self, other):
        # multiply out the or operations
        if isinstance(other, CharacterFilter):
            return CharacterFilter(a | b for a, b in product(self._matchers,
                                                             other._matchers))
        elif isinstance(other, CharacterMatcher):
            other_set = frozenset([other])
            return ChararacterFilter(mine | other_set
                                     for mine in self._matchers)

    def __sub__(self, other):
        return self & ~other

    def __xor__(self, other):
        return (self | other) - (self & other)

    def __invert__(self):
        # use de morgan's rules to flip the operations
        # then multiply out the or-operations
        negated = map(partial(map, lambda x: ~x), self._matchers)
        return CharacterFilter(product(*negated))

    @property
    def empty(self):
        return all(any(m.empty for m in a) for a in self._matchers)

    def match(self, char):
        return any(all(m.match(char) for m in a) for a in self._matcher)


class CharacterMatcher:

    def __eq__(self, other):
        return isinstance(other, type(self))

    def __hash__(self):
        return hash(type(self))

    def __invert__(self):
        return Negation(self)

    def __and__(self, other):
        if isinstance(other, CharacterMatcher):
            return CharacterFilter([[self, other]])
        elif isinstance(other, CharacterFilter):
            return other & self

    def __or__(self, other):
        if isinstance(other, CharacterMatcher):
            return CharacterFilter([[self], [other]])
        elif isinstance(other, CharacterFilter):
            return other | self

    def __sub__(self, other):
        return self & ~other

    def __xor__(self, other):
        return (self | other) - (self & other)

    @property
    def empty(self):
        return False

    def match(self, char):
        raise NotImplementedError


class Negation(CharacterMatcher):

    def __init__(self, matcher):
        self._matcher = matcher

    def __str__(self):
        return "Negation({})".format(str(self._matcher))

    def __eq__(self, other):
        return isinstance(other, type(self))

    def __hash__(self):
        return hash(super()) ^ hash(self._matcher)

    def __invert__(self):
        return self._matcher

    def match(self, char):
        return not self._matcher.match(char)


class Empty(CharacterMatcher):

    def __str__(self):
        return "Empty()"

    def __invert__(self):
        return All()

    @property
    def empty(self):
        return True

    def match(self, char):
        return False


class All(CharacterMatcher):

    def __str__(self):
        return "All()"

    def __invert__(self):
        return Empty()

    def match(self, char):
        return True


class Range(CharacterMatcher):

    def __init__(self, from_, to):
        self._from = from_
        self._to = to

    def __eq__(self, other):
        return isinstance(other, Range) and \
            self._from == other._from and self._to == other._to

    def __hash__(self):
        return hash(super()) ^ hash(self._from) ^ hash(self._to)

    def __str__(self):
        return "Range({}, {})".format(self._from, self._to)

    @property
    def empty(self):
        return self._from > self._to

    def match(self, char):
        return self._from <= char <= self._to


class Character(CharacterMatcher):

    def __init__(self, char):
        self._char = char

    def __eq__(self, other):
        return isinstance(other, Character) and \
            self._char == other._char

    def __hash__(self):
        return hash(super()) ^ hash(self._char)

    def __str__(self):
        return "Character({})".format(repr(self._char))

    def match(self, char):
        return char == self._char


class Category(CharacterMatcher):

    def __init__(self, category):
        self._category = category

    def __eq__(self, other):
        return isinstance(other, Category) and \
            self._category == other._category

    def __hash__(self):
        return hash(super()) ^ hash(self._category)

    def __str__(self):
        return "Category({})".format(repr(self._category))

    def match(self, char):
        return self._category == unicodedata.category(char)


class Property(CharacterMatcher):

    def __init__(self, prop, value):
        self._property = prop
        self._value = value

    def __eq__(self, other):
        return isinstance(other, Property) and \
            self._property == other._property and \
            self._value == other._value

    def __hash__(self):
        return hash(super()) ^ hash(self._property) ^ hash(self._value)

    def __str__(self):
        return "Property({}, {})".format(self._property, self._value)

    def match(self, char):
        raise NotImplementedError

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
