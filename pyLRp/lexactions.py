
import operator
from functools import reduce

from .core import AutoAccept

class LexingAction(object, metaclass=AutoAccept):
    """
    Lexing actions.

    Take care these do not get dictionary keys or set members (or
    anything they are required to have a constant hash for or `==` based
    on `id`) while they might change.

    Rationale: They are compared and hashed for their members because
    we will make them unique, before writing them to the output file.
    """

    _subclasses_ = []

    def __init__(self):
        pass

    def accept(self):
        raise NotImplementedError()

    def __eq__(self, other):
        return self.__class__ == other.__class__ \
            and self.__dict__ == other.__dict__

    def __hash__(self):
        # TODO: find better solution than xor, it destroys a lot of
        # the hashes because there will be many hash(x) == id(x)
        # objects and the addresses id(x) will tend to be in a narrow
        # region.
        return reduce(operator.__xor__,
                      map(hash, self.__dict__.items()),
                      id(self.__class__))

class Debug(LexingAction):

    def __init__(self, text):
        super(Debug, self).__init__()
        self._text = text

    def __str__(self):
        return "Debug(" + repr(self._text) + ")"

    @property
    def text(self):
        return self._text

class List(LexingAction):

    def __init__(self, lst=None):
        super(List, self).__init__()
        self._list = lst or []

    def __str__(self):
        return "List([" + ", ".join(map(str, self._list)) + "])"

    def __iter__(self):
        return iter(self._list)

    def append(self, action):
        self._list.append(action)

    # we have to implement this because lists
    # do not hash well
    def __hash__(self):
        return reduce(operator.__xor__,
                      map(hash, self._list),
                      id(self.__class__))

class Begin(LexingAction):

    def __init__(self, state):
        super(Begin, self).__init__()
        self._state = state

    def __repr__(self):
        return "Begin(%s)" % self.state

    @property
    def state(self):
        return self._state

class Push(LexingAction):

    def __init__(self, state):
        super(Push, self).__init__()
        self._state = state

    def __repr__(self):
        return "Push(%s)" % self.state

    @property
    def state(self):
        return self._state

class Pop(LexingAction):

    def __init__(self):
        super(Pop, self).__init__()

    def __repr__(self):
        return "Pop()"

class Restart(LexingAction):

    def __init__(self):
        super(Restart, self).__init__()

    def __repr__(self):
        return "Restart()"

class Continue(LexingAction):

    def __init__(self):
        super(Continue, self).__init__()

    def __repr__(self):
        return "Continue()"

class Token(LexingAction):

    def __init__(self, name):
        super(Token, self).__init__()
        self._name = name

    def __repr__(self):
        return "Token('%s')" % self.name

    @property
    def name(self):
        return self._name

class Function(LexingAction):

    def __init__(self, name):
        super().__init__()
        self._name = name

    def __repr__(self):
        return "Function('%s')" % self.name

    @property
    def name(self):
        return self._name


class GetMatch(LexingAction):

    def __init__(self):
        super(GetMatch, self).__init__()

    def __repr__(self):
        return "GetMatch()"

LexingActionVisitor = LexingAction.base_visitor()
