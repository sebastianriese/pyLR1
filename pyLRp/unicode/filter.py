"""
Character filters, used to build up the alphabet for the unicode
lexer.

from, to and character values must be given consistently either as
unicode strings or numbers.
"""

# TODO: use more datasources/compile your own database
from itertools import chain, product, repeat
from functools import partial
from abc import ABCMeta, abstractproperty, abstractmethod

from ..alphabet import Alphabet, ByteAlphabet

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

# XXX: the non-composite nature of the patterns is *not* fun
# XXX: we also need solely &-connected filters with assigned truth values

class CharacterFilter:

    @classmethod
    def any_from_string(cls, string):
        return cls([Character(c)] for c in string)

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
        elif isinstance(other, CharacterMatcher):
            return CharacterFilter(self._matchers |
                                   frozenset([frozenset([other])]))
        else:
            raise TypeError

    def __and__(self, other):
        # multiply out the or operations
        if isinstance(other, CharacterFilter):
            return CharacterFilter(a | b for a, b in product(self._matchers,
                                                             other._matchers))
        elif isinstance(other, CharacterMatcher):
            other_set = frozenset([other])
            return CharacterFilter(mine | other_set
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

    @property
    def single(self):
        # XXX: not nice to return None here but as the basic
        # operations with Any and Empty are optimized, this does not
        # break the regex parser (where we ask for single when
        # evaluating ranges)
        return None

    def atoms(self):
        for and_chain in self._matchers:
            for filter in and_chain:
                # TODO: replace this by yield from as soon
                # as pre Python-3.3 has vanished
                for a in filter.atoms():
                    yield a

    def match(self, char):
        return any(all(m.match(char) for m in a) for a in self._matchers)

    def map_values(self, mapping):
        return any(all(m.map_values(mapping) for m in a)
                   for a in self._matchers)

class AbstractCharacterFilterValue:

    def fulfills(self, char_filter):
        pass

    def matches(self, char):
        pass


class CharacterFilterValues(AbstractCharacterFilterValue):

    def __init__(self, filters, truth):
        """
        ``filters`` is a iterable of CharacterMatchers
        ``truth`` is a iterable of booleans of the same (finite!) length
        the length requirement is *not* checked, then the length
        of the shorter sequence is chosen.
        """

        self._filters = dict(zip(filters, truth))

    def fulfills(self, char_filter):
        return char_filter.map_values()

    def matches(self, char):
        return all(filter_.match(char) == value
                   for filter_, value in self._filters.items())

class SingleCharacterFilterValue(AbstractCharacterFilterValue):

    def __init__(self, char):
        """
        The symbol for the single character ``char``.

        As all other predicates may be resolved for ``char``,
        this sets the truth value of all transitions. Characters
        are therefore optimized out.
        """
        self._char = char

    def fullfills(self, char_filter):
        return char_filter.match(self._char)

    def matches(self, char):
        return char == self._char

class CharacterMatcher:

    def __eq__(self, other):
        raise NotImplementedError

    def __hash__(self):
        raise NotImplementedError

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

    @property
    def single(self):
        return False

    def atoms(self):
        yield self

    def match(self, char):
        raise NotImplementedError

    def map_values(self, mapping):
        return mapping[self]

class Negation(CharacterMatcher):

    def __init__(self, matcher):
        self._matcher = matcher

    def __str__(self):
        return "Negation({})".format(str(self._matcher))

    def __eq__(self, other):
        return isinstance(other, Negation) and self._matcher == other._matcher

    def __hash__(self):
        return hash(type(self)) ^ hash(self._matcher)

    def __invert__(self):
        return self._matcher

    def atoms(self):
        yield self._matcher

    def match(self, char):
        return not self._matcher.match(char)

    def map_values(self, mapping):
        return not self._matcher.map_values(mapping)

class Empty(CharacterMatcher):

    def __str__(self):
        return "Empty()"

    def __eq__(self, other):
        return isinstance(other, Empty)

    def __hash__(self):
        return hash(Empty)

    def __or__(self, other):
        return other

    def __and__(self, other):
        return self

    def __xor__(self, other):
        return other

    def __sub__(self, other):
        return self

    def __invert__(self):
        return All()

    def atoms(self):
        return iter([])

    @property
    def empty(self):
        return True

    def match(self, char):
        return False

    def map_values(self, mapping):
        return False

class All(CharacterMatcher):

    def __str__(self):
        return "All()"

    def __eq__(self, other):
        return isinstance(other, All)

    def __hash__(self):
        return hash(All)

    def __or__(self, other):
        return self

    def __and__(self, other):
        return other

    def __xor__(self, other):
        return ~other

    def __sub__(self, other):
        return ~other

    def __invert__(self):
        return Empty()

    def atoms(self):
        return iter([])

    def match(self, char):
        return True

    def map_values(self, mapping):
        return True

class Range(CharacterMatcher):

    def __init__(self, from_, to):
        self._from = from_
        self._to = to

    def __eq__(self, other):
        return isinstance(other, Range) and \
            self._from == other._from and self._to == other._to

    def __hash__(self):
        return hash(type(self)) ^ hash(self._from) ^ hash(self._to)

    def __str__(self):
        return "Range({}, {})".format(self._from, self._to)

    @property
    def empty(self):
        return self._from > self._to

    @property
    def single(self):
        if self._from == self._to:
            return self._from
        else:
            return None

    def match(self, char):
        return self._from <= char <= self._to


class Character(CharacterMatcher):

    def __init__(self, char):
        self._char = char

    def __eq__(self, other):
        return isinstance(other, Character) and \
            self._char == other._char

    def __hash__(self):
        return hash(type(self)) ^ hash(self._char)

    def __str__(self):
        return "Character({})".format(repr(self._char))

    @property
    def single(self):
        return self._char

    def match(self, char):
        return char == self._char

class Dot(CharacterMatcher):

    def __str__(self):
        return "Dot()"

    def __eq__(self, other):
        return isinstance(other, Dot)

    def __hash__(self):
        return hash(Dot)

    def match(self, char):
        return char != '\n'

class Property(CharacterMatcher):

    def __init__(self, data, prop, value=True):
        self._data = data
        self._property = prop
        self._value = value

    def __eq__(self, other):
        return isinstance(other, Property) and \
            self._property == other._property and \
            self._value == other._value

    def __hash__(self):
        return hash(type(self)) ^ hash(self._property) ^ hash(self._value)

    def __str__(self):
        return "Property({}, {})".format(self._property, self._value)

    def match(self, char):
        return self._data.property(self._property, char) == self._value


class AlphabetStrategy(metaclass=ABCMeta):
    """
    Strategies for mapping filters to alphabets. Includes later
    alphabet handling, such as cooperation when constructing
    equivalence classes of symbols in the lextable.
    """

    @abstractproperty
    def alphabet(self):
        raise NotImplementedError

    @abstractmethod
    def alphabetize(self, nfa):
        pass

class FoldASCIIAlphabetStrategy(AlphabetStrategy):

    def __init__(self):
        pass

    @property
    def alphabet(self, alpha=ByteAlphabet()):
        return alpha

    def alphabetize(self, nfa):
        def alphabet_map(cond):
            for i in range(0x100):
                # XXX: consistent use of chr vs. codepoint
                if cond.match(chr(i)):
                    yield chr(i)
        return nfa.map_labels(alphabet_map)

class UTF8AlphabetStrategy(AlphabetStrategy):

    @property
    def alphabet(self, alpha=ByteAlphabet()):
        return alpha

    def alphabetize(self, nfa):
        pass

class PredicateAlphabetStrategy(AlphabetStrategy):

    def __init__(self):
        self._predicates = set()
        self._alphabet = []
        self._abstract_alphabet = None

    @property
    def alphabet(self):
        return UniodeFilterAlphabet(len(self._alphabet))

    def alphabetize(self, nfa):
        nfa.traverse(self._collect_predicates)
        self._construct_alphabet()
        return nfa.map_labels(self._map_alphabet)

    def _collect_predicates(self, from_, cond, to):
        # TODO: keep only distinguishing forms of predicates
        # for example if two predicates only occure together in
        # transitions handle them as though they were a single
        # predicate, this moves part of
        # pyLRp.lextable.Lextable.create_equivalence_classes
        # here thereby making to_DFA significantly faster
        # to only keep distinguishing forms the .atom() mechanism
        # cannot be maintained, making the code much more complex
        # for now this will work: unless this proves to be a real
        # bottleneck we will not implement the complex variant.
        for filter in cond.atoms():
            self._predicates.add(filter)

    def _construct_alphabet(self):
        # single out characters
        chars = []
        for p in list(self._predicates):
            if isinstance(p, Character):
                self._predicates.remove(p)
                chars.append(p)

        predicates = list(self._predicates)
        filters = chars + predicates
        self._predicates = None

        for c in chars:
            self._alphabet.append(len(self._alphabet,
                                      SingleCharacterFilterValue(c.single)))

        # assign all combinations of truth values to the other
        # predicates
        for v in product((False, True), repeat=len(predicates)):
            v = chain(repeat(False, len(chars)), v)
            self._alphabet.append((len(self._alphabet),
                                   CharacterFilterValues(filters, v)))


    def flat_mapping(self):
        num = len(self._chars)
        chars = self._chars
        filters = self._filters
        for i in range(0x110000):
            if chr(i) in self.chars:
                yield self.chars[chr(i)]

            # TODO: is index calculation faster than dict-lookup
            # otherwise create a dict value-tuple to alphabet entry
            # which would be cleaner, more robust and easier to understand
            # contra: much more mem
            index = 0
            for filter in filters:
                index *= 2
                # efficiency hack for: if ...: index += 1
                # via n + True == n + 1, n + False == n + 0
                index += filter.match(chr(i))
            index += len(chars)
            yield index

    def _map_alphabet(self, filter_):
        for symbol, filter_values in self._alphabet:
            if filter_values.fulfills(filter_):
                yield symbol

class UnicodeFilterAlphabet(Alphabet):

    def __len__(self):
        return len(self._symbols)

    def __iter__(self):
        return iter(self._symbols)

    def __getitem__(self, index):
        return self._symbols[index]

    def __init__(self, symbols):
        self._symbols = symbols
