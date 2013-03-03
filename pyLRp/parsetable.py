
from .core import AutoAccept

class LRAction(metaclass=AutoAccept):
    @property
    def is_shift(self):
        return False

    @property
    def is_reduce(self):
        return False

    def __init__(self, prec, num_in_file):
        self._prec = prec
        self._num_in_file = num_in_file

    @property
    def assoc(self):
        return self._prec

    @property
    def number_in_file(self):
        return self._num_in_file

    def accept(self, visitor):
        raise NotImplementedError()


class Shift(LRAction):
    @property
    def is_shift(self):
        return True

    def __init__(self, newstate, prec, n):
        super(Shift, self).__init__(prec, n)
        self._newstate = newstate

    def __str__(self):
        return "s%d" % self._newstate

    @property
    def next(self):
        return self._newstate

class Reduce(LRAction):

    @property
    def is_reduce(self):
        return True

    def __init__(self, reduction, prec, n):
        super(Reduce, self).__init__(prec, n)
        self._reduction = reduction

    def __str__(self):
        return "r%d" % self._reduction

    @property
    def red(self):
        return self._reduction

LRActionVisitor = LRAction.base_visitor()

class ParseTable(object):
    """
    A LR parse table.
    """

    def __init__(self, actiontable, gototable, start, rules):
        self._start = start
        self._actiontable = actiontable
        self._gototable = gototable
        self._rules = rules

    def rules(self):
        return iter(self._rules)

    def actiontable(self):
        return iter(self._actiontable)

    def gototable(self):
        return iter(self._gototable)

    @property
    def start(self):
        return self._start

    def print(self):
        for i, rule in enumerate(self._rules):
            print("(%d) %s" % (i, str(rule)))

        for aline, gline in zip(self._gototable, self._actiontable):
            for entry in aline:
                print(str(entry).center(5), end=' ')

            for entry in gline:
                print(str(entry).center(5), end=' ')
            print("")
