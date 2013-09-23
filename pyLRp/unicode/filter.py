"""
Character filters, used to build up the alphabet for the unicode lexer.
"""

# TODO: use more datasources/compile your own database
import unicodedata

from ..core import AutoAccept

class CharacterFilter(metaclass=AutoAccept):

    _subclasses_ = []

    @property
    def empty(self):
        return False

    def normalize(self):
        return self

    def match(self, char):
        return False

class Union(CharacterFilter):

    def __init__(self, *children):
        self._children = children

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
        self._children = children

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

        result = Intersection(*new_children)
        if result.empty:
            return All()
        return result

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

    def __str__(self):
        return "Range({}, {})".format(self._from, self._to)

    @property
    def empty(self):
        return self._from > self._to

    def match(self, char):
        return self._from <= ord(char) <= self._to

class Character(CharacterFilter):

    def __init__(self, char):
        self._char = char

    def __str__(self):
        return "Character({})".format(repr(self._char))

    def match(self, char):
        return char == self._char

class Category(CharacterFilter):

    def __init__(self, category):
        self._category = category

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
            return child._child
        else:
            return super().__new__(cls)

    def __init__(self, child):
        self._child = child

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
