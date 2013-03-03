
from .core import CantHappen, Singleton

class Symbol(object):
    """Base class for all types symbols in the system (terminal, meta,
    undef and empty)."""

    def __init__(self, name):
        self._name = name

    def __str__(self):
        # use self.name to allow overiding by subclasses
        return self.name

    @property
    def name(self):
        return self._name

    @property
    def is_s_token(self):
        return False

    @property
    def is_empty(self):
        """Return whether the symbol is the empty symbol."""
        return False

    def productions(self):
        """Return an iterator over the list of productions"""
        return iter([])

    def first(self, visited=None):
        """The FIRST-set of the symbol."""
        raise NotImplementedError()

    def reduces_to_empty(self, visited=None):
        """Return whether the symbol can be reduced to the empty
        symbol."""
        return False


class EOF(Symbol):
    """
    The EOF symbol.
    """

    def __init__(self):
        super(EOF, self).__init__("$EOF")

    def first(self, visited=None):
        return set([self])


class Error(Symbol):
    """
    The Error symbol. This is the terminal symbol emitted on invalid
    lexemes.
    """

    def __init__(self):
        super(Error, self).__init__("$ERROR")

    def first(self, visited=None):
        return set([self])


class Undef(Symbol):
    """
    The Undef symbol used in the LALR(1) lookahead
    construction algorithm
    """

    def __init__(self):
        super(Undef, self).__init__("$UNDEF")

    def first(self, visited=None):
        return set([self])


class Empty(Symbol, metaclass=Singleton):
    """
    The empty terminal symbol.  The class is a singleton, in order to
    make many of the methods of the other classes work you should not
    instanciate it. Use the Instance class method for retrieving the
    singleton instance.
    """

    instance = None

    def __init__(self):
        super(Empty, self).__init__("$Empty")

    def first(self, visited=None):
        return set([self])

    def reduces_to_empty(self, visited=None):
        # empty is not allowed in productions
        raise CantHappen()

    @property
    def is_empty(self):
        return True

class Terminal(Symbol):
    """The Terminal symbol class."""

    def __init__(self, name, stoken):
        super(Terminal, self).__init__(name)
        self.stoken = stoken

    def first(self, visited=None):
        return set([self])

    @property
    def is_s_token(self):
        return self.stoken

class Meta(Symbol):
    """
    The Metasymbol class. This stores the grammar for the symbol.
    """

    def __init__(self, name):
        super(Meta, self).__init__(name)
        self._prod = []
        self._first = None
        self._reduces_to_empty = None

    def productions(self):
        return iter(self._prod)

    def add_prod(self, prod):
        prod.left = self
        self._prod.append(prod)

    def first(self, visited=None):
        # if self.first is not None:
        #     return self.first

        result = set()

        if visited is None: visited = frozenset()

        for prod in self._prod:
            result |= prod.first(visited | set([self]))

        # if len(visited) == 0:
        #     self.first = result

        return result

    def reduces_to_empty(self, visited=None):
        if self._reduces_to_empty is not None:
            return self._reduces_to_empty

        if visited is None:
            visited = frozenset()

        for prod in self._prod:

            for sub in prod:
                if sub in visited:
                    continue

                if not sub.reduces_to_empty(visited | set([self])):
                    # this production doesn't reduce to empty (because
                    # one subsymbol doesn't)
                    break
            else:
                # all subsymbols in this production reduced to empty,
                # therefore the symbol may reduce to empty
                if len(visited) == 0:
                    self._reduces_to_empty = True

                return True

        # no production for this symbol does reduce to empty
        if len(visited) == 0:
            self._reduces_to_empty = False

        return False

