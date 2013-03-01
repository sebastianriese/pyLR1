
from .core import CantHappen

class Symbol(object):
    """Base class for all types symbols in the system (terminal, meta,
    undef and empty)."""

    def __init__(self, name):
        self.name = name

    def __str__(self):
        return self.Name()

    def Name(self):
        return self.name

    def IsSToken(self):
        return False

    def Productions(self):
        """Return an iterator over the list of productions"""
        return iter([])

    def First(self, visited=None):
        """The FIRST-set of the symbol."""
        raise NotImplementedError()

    def ReducesToEmpty(self, visited=None):
        """Return whether the symbol can be reduced to the empty
        symbol."""
        return False

    def Productions(self):
        return iter([])

    def IsEmpty(self):
        """Return whether the symbol is the empty symbol."""
        return False

class EOF(Symbol):
    """
    The EOF symbol.
    """

    def __init__(self):
        super(EOF, self).__init__("$EOF")

    def First(self, visited=None):
        return set([self])

class Error(Symbol):
    """
    The Error symbol. This is the terminal symbol emitted on invalid
    lexemes.
    """

    def __init__(self):
        super(Error, self).__init__("$ERROR")

    def First(self, visited=None):
        return set([self])

class Undef(Symbol):
    """
    The Undef symbol used in the LALR(1) lookahead
    construction algorithm
    """

    def __init__(self):
        super(Undef, self).__init__("$UNDEF")

    def First(self, visited=None):
        return set([self])


class Empty(Symbol):
    """
    The empty terminal symbol.  The class is a singleton, in order to
    make many of the methods of the other classes work you should not
    instanciate it. Use the Instance class method for retrieving the
    singleton instance.
    """

    instance = None

    def __init__(self):
        super(Empty, self).__init__("$Empty")

    @classmethod
    def Instance(clazz):
        """Return the singleton instance, create it, if neccessary."""
        if not clazz.instance:
            clazz.instance = Empty()

        return clazz.instance

    def First(self, visited=None):
        return set([self])

    def ReducesToEmpty(self, visited=None):
        # empty is not allowed in productions
        raise CantHappen()

    def IsEmpty(self):
        return True

class Terminal(Symbol):
    """The Terminal symbol class."""

    def __init__(self, name, stoken):
        super(Terminal, self).__init__(name)
        self.stoken = stoken

    def First(self, visited=None):
        return set([self])

    def IsSToken(self):
        return self.stoken

class Meta(Symbol):
    """
    The Metasymbol class. This stores the grammar for the symbol.
    """

    def __init__(self, name):
        super(Meta, self).__init__(name)
        self.prod = []
        self.first = None
        self.reduces_to_empty = None

    def Productions(self):
        return iter(self.prod)

    def AddProd(self, prod):
        prod.left = self
        self.prod.append(prod)

    def Productions(self):
        # the copying is just a safety measure ...
        return self.prod[:]

    def First(self, visited=None):
        # if self.first is not None:
        #     return self.first

        result = set()

        if visited is None: visited = frozenset()

        for prod in self.prod:
            result |= prod.first(visited | set([self]))

        # if len(visited) == 0:
        #     self.first = result

        return result

    def ReducesToEmpty(self, visited=None):

        if self.reduces_to_empty is not None:
            return self.reduces_to_empty

        if visited is None:
            visited = frozenset()

        for prod in self.prod:

            for sub in prod:
                if sub not in visited and not sub.ReducesToEmpty(visited | set([self])):
                    # this production doesn't reduce to empty (because
                    # one subsymbol doesn't)
                    break
            else:
                # all subsymbols in this production reduced to empty,
                # therefore the symbol may reduce to empty

                if len(visited) == 0:
                    self.reduces_to_empty = True

                return True

        # no production for this symbol does reduce to empty
        if len(visited) == 0:
            self.reduces_to_empty = False

        return False

