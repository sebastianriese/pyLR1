
from .core import AutoAccept

class LRAction(metaclass=AutoAccept):

    def IsShift(self): return False
    def IsReduce(self): return False

    def __init__(self, prec, numInFile):
        self.prec = prec
        self.numInFile = numInFile

    def GetAssoc(self): return self.prec
    def NumberInFile(self): return self.numInFile

    def Accept(self, visitor):
        raise NotImplementedError()

class Shift(LRAction):
    def IsShift(self): return True

    def __init__(self, newstate, prec, n):
        super(Shift, self).__init__(prec, n)
        self.newstate = newstate

    def __str__(self):
        return "s%d" % self.newstate

    def Next(self):
        return self.newstate

class Reduce(LRAction):
    def IsReduce(self): return True

    def __init__(self, reduction, prec, n):
        super(Reduce, self).__init__(prec, n)
        self.reduction = reduction

    def __str__(self):
        return "r%d" % self.reduction

    def Red(self):
        return self.reduction

LRActionVisitor = LRAction.base_visitor()

class ParseTable(object):
    """
    A LR parse table.
    """

    def __init__(self, actiontable, gototable, start, rules):
        self.start = start
        self.actiontable = actiontable
        self.gototable = gototable
        self.rules = rules

    def Actiontable(self):
        return self.actiontable

    def Gototable(self):
        return self.gototable

    def Start(self):
        return self.start

    def Rules(self):
        return self.rules

    def Print(self):

        i = 0

        for rule in self.rules:
            print("(%d) %s" % (i, str(rule)))
            i += 1



        giter = iter(self.gototable)
        aiter = iter(self.actiontable)
        try:
            while True:
                gline = next(giter)
                aline = next(aiter)
                for entry in aline:
                    entrystr = ""
                    first = True


                    entrystr += str(entry)
                    print(entrystr.center(5), end=' ')

                for entry in gline:
                    print(str(entry).center(5), end=' ')
                print("")

        except StopIteration:
                pass
