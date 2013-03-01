
import abc

from .pyblob import PyBlob, PyText, PyStackvar, PySuite, PyNewline
from .symbol import *
from .parsetable import *

class Production(object):
    """A production in a grammar. Productions with left set to None
    may be used as arbitrary symbol strings.

    Public attributes:
    * ``left`` the symbol which is derived, only write this if
               you are a parser or ``Meta``
    * ``assoc`` the associativity assigned to this rule
    * ``number`` the number of this production in the reduction vector
    * ``action`` the semantic action associated with the reduction
    * ``number_in_file`` readonly, the number of the production
                         in the source file
    """

    # these constants define the possible types of associativity
    NONE = 0
    LEFT = 1
    RIGHT = 2
    NONASSOC = 3

    def __init__(self, left, syms, number = -1):
        self.left = left
        self._syms = list(syms)
        self._number_in_file = number
        self.assoc = Production.NONE, 0
        self.action = None
        self.number = None

        # number in the reduction rules vector
        self.number = None
        # self.first = None

    def __iter__(self):
        return iter(self._syms)

    def __str__(self):
        text =  str(self.left) + " <- "

        for sub in self:
            text += str(sub) + " "

        return text

    def __len__(self):
        return len(self._syms)

    # important note: this number is completely independent of the
    # number used to represent  the production in the parse table!
    # This one is  used  exclusivley to resolve  conflicts in the
    # parse  tables  (earlier  declaration  ->  higer  precedence)
    @property
    def number_in_file(self):
        return self._number_in_file

    def add_sym(self, sym):
        self._syms.append(sym)

    def first(self, visited=None):
        # if self.first is not None:
        #     return self.first

        if visited is None:
            visited = frozenset()

        result = set()

        for sub in self._syms:
            if sub  not in visited:
                result |= sub.First(visited | set([self])) - set([Empty.Instance()])

            if not sub.ReducesToEmpty():
                break

        else:
            result.add(Empty.Instance())

        # if len(visited) == 0:
        #     self.first = result

        return result

    def __getitem__(self, index):
        if isinstance(index, slice):
            return Production(None, self._syms[index])
        else:
            return self._syms[index]

    def concat(self, elem):
        """
        Return a new Production with left=None and
        syms=self.syms+[elem].  The main use of this is to evaluate
        the FIRST set of the concatenation.
        """

        if elem.IsEmpty():
            return Production(None, self)

        return Production(None, self._syms + [elem])


class LR1Item(object):
    """A LR(1) item (production, position, lookahead set)"""

    def __init__(self, prod, pos, la):
        self.prod = prod
        self.pos = pos
        self.la = frozenset(la)

    def __str__(self):
        text =  (self.prod.left.Name() or "None") + " <- "
        count = 0

        for sub in self.prod:
            if count == self.pos:
                text += ". "

            text += (sub.Name() or "None") + " "
            count += 1

        if count == self.pos:
            text += ". "

        text += "{ "

        for sub in self.la:
            text += (sub.Name() or "None") + " "

        text += "}"

        return text

    closure = dict()

    @classmethod
    def FromCore(clazz, lr0, la):
        return clazz(lr0.prod, lr0.pos, la)

    def __hash__(self):
        return hash(self.prod) \
            ^ hash(self.pos) \
            ^ hash(self.la)

    def __eq__(self, other):
        return self.prod == other.prod \
            and self.pos == other.pos \
            and self.la == other.la

    def InKernel(self):
        return self.pos != 0 or (self.prod.left.Name() == "$START")

    def AfterDot(self):
        try:
            return self.prod[self.pos]
        except IndexError:
            return None

    def IsReduce(self):
        return self.AfterDot() is None

    def Prod(self):
        return self.prod

    def Pos(self):
        return self.pos

    def Core(self):
        return LR1Item(self.prod, self.pos, frozenset())

    def SetLookahead(self, la):
        if (self.prod,self.pos,self.la) in self.closure:
            # the buffered closure is no longer valid, once
            # a new lookahead set is assigned
            del self.closure[(self.prod,self.pos,self.la)]

        self.la = frozenset(la)

    def Lookahead(self):
        return self.la

    def Goto(self, symbol):
        afterDot = self.AfterDot()
        result = set()

        if afterDot == symbol:
            result |= LR1Item(self.prod, self.pos+1, self.la).Closure()

        return result

    def Closure(self, visited=None):
        # possibly the buffering is buggy
        if (self.prod,self.pos,self.la) in self.closure:
             return self.closure[(self.prod,self.pos,self.la)]

        if visited is None:
            visited = frozenset()

        closure = set([self])
        afterDot = self.AfterDot()
        recurses = False

        if afterDot:
            laset = set()

            for la in self.la:
                firstconcat = self.prod[self.pos+1:].concat(la)
                laset |= firstconcat.first()

            for prod in afterDot.Productions():

                if self not in visited:
                    elem = LR1Item(prod, 0, laset)
                    closure |= elem.Closure(visited | set([self]))
                else:
                    recurses = True

        if not recurses:
            self.closure[(self.prod,self.pos,self.la)] = closure

        return closure

    def TransitionsTo(self, other):
        """
        Determine whether the LR item generates `other` on transition.
        """

        if self.IsReduce():
            return False

        return self.Prod() == other.Prod() and self.Pos() + 1 == other.Pos()

class StateTransition(object):
    """
    A transition from a LR state to another LR state
    """

    def __init__(self, symbol, state):
        self.symbol = symbol
        self.state = state

    def __eq__(self, other):
        return self.symbol == other.symbol \
            and self.state == other.state

    def __hash__(self):
        return hash(self.symbol) ^ hash(self.state)

    def Symbol(self):
        return self.symbol

    def State(self):
        return self.state

class StateTransitionGraph(object, metaclass=abc.ABCMeta):

    def __init__(self, grammar, logger):
        """
        An *LR(1) state transition graph, this has the behaviour
        common to LALR(1), LR(1), SLR(1), ... transition graphs.
        """

        self.logger = logger

        self.grammar = grammar
        self.states = []

        self.conflicts = 0

        self.start = None

        # require the $RECOVER terminal symbol used during
        # error recovery of the parser
        self.grammar.RequireTerminal("$RECOVER")

    def ReportNumOfConflicts(self):
        if self.conflicts:
            self.logger.warning(str(self.conflicts) + " conflict(s) found!")

    @abc.abstractmethod
    def Construct(self):
        """
        Construct the *LR(1) automaton.
        """
        pass

    def NormalizeItemSet(self, elements):
        """
        Normalize the item set.

        Normal means:

        * each core occurs only once
        * the lookahead set assigned to a core is the union of the
          ones assigned to the occurences of core before

        Returns the normalized item set.
        """
        cores = {}
        for elem in elements:
            if elem.Core() not in cores:
                cores[elem.Core()] = set()

            cores[elem.Core()] |= elem.Lookahead()

        elements = set()
        for core in cores:
            elements.add(LR1Item.FromCore(core, cores[core]))
        cores = None

        return elements

    def RequireState(self, elements):
        """
        Check whether a state having the given elements already
        exists. If it does exist return it, otherwise create the new
        state and recursively determine its sub states.
        """

        elements = self.NormalizeItemSet(elements)

        # do we already have this state?
        for state in self.states:
            if state.elements == elements:
                return state

        # instanciate the new state
        state = self.GenerateState(len(self.states), elements)
        self.states.append(state)
        state.GenerateSubStates()
        return state

    @abc.abstractmethod
    def GenerateState(self, number, elements):
        """
        Generate an appropriate `LR1StateGraphElement`. Where `number`
        is the assigned id number and `elements` is the associated set
        of LR1Items.
        """
        pass

    def ResolveConflict(self, state, old, new):
        """
        Resolve a parse table conflict.

        The `state` argument is the LR(1) graph state causing the
        conflict, `old` and `new` are the action already in the table
        respective the proposed action.

        For reduce/reduce-conflicts the production later in file takes
        precedence and a warning is issued.

        For shift/reduce-conflicts the precedence declarations are
        used to resolve the conflict. If no precedence is declared
        a warning is issued and the shift action is chosen.

        Returns the preceding action.
        """
        if old is None:
            return new

        if old.IsReduce():
            self.logger.info(str(state))
            self.logger.warning("Default to the first reduce for reduce/reduce-conflict")
            self.conflicts += 1
            if old.NumberInFile() > new.NumberInFile():
                return new
            else:
                return old

        elif old.IsShift():
            assoc, prec = old.GetAssoc()
            associ, preci = new.GetAssoc()

            # shift wins over reduce by default
            if assoc == Production.NONE:
                self.logger.info(str(state))
                self.logger.warning("Default to shift for shift/reduce-conflict")
                self.conflicts += 1
                return old

            elif assoc == Production.NONASSOC:
                # generate an error entry for nonassoc
                if preci > prec:
                    return new
                elif preci == prec:
                    # XXX: can there be a situation where this None is
                    # mistaken for: nothing so far and then an action
                    # is written though there are three nonassoc
                    # productions of equal precedence
                    # yes, but this required a reduce/reduce conflict in the
                    # first place, I better fix that!
                    return None
                else:
                    return old

            elif assoc == Production.LEFT:
                if preci >= prec:
                    return new
                else:
                    return old

            elif assoc == Production.RIGHT:
                if preci > prec:
                    return new
                else:
                    return old
            else:
                raise CantHappen()


    def Kernels(self):
        """
        Reduce the item sets to their kernels
        (needed for LALR lookahead generation)
        """
        for state in self.states:
            state.Kernel()

    def CloseKernels(self):
        """
        Complete the sets to their closure again
        after they where reduced to their kernels
        """

        for state in self.states:
            state.Close()

    def CreateParseTable(self, terminals, metas):
        """
        Create the parse table from the LR graph. Requires two mappings
        from `Symbol` objects to their respective numbers: One of them
        for the terminals and another for the meta-symbols.

        They can be created from the `Syntax` object by calling:

            termsyms = frozenset([Syntax.TERMINAL, Syntax.EOF, Syntax.ERROR])
            syn.SymTableMap(filt=lambda x: x.SymType() in termsyms,
                            value=lambda x: x.Number())

            syn.SymTableMap(filt=lambda x: x.SymType() == Syntax.META,
                            value=lambda x: x.Number())

        The function returns a `Parsetable` object.
        """
        atable = []
        jtable = []

        rules = []

        # populate the rules vector
        for meta in sorted(metas, key=lambda meta: metas[meta]):
            for rule in meta.Productions():
                rule.number = len(rules)
                rules.append(rule)

        for state in self.states:
            # append the current row to the action- and jumptables
            acur = [None] * len(terminals)
            jcur = [None] * len(metas)

            atable.append(acur)
            jtable.append(jcur)

            # fill goto table and write shifts to the action table
            for trans, prods in state.Transitions().items():
                symb = trans.Symbol()
                tstate = trans.State()

                if symb in metas:
                    jcur[metas[symb]] = tstate.Number()

                elif symb in terminals:
                    assoc = Production.NONE, -1
                    prec = -1

                    # XXX: this is differnent from the bison/yacc
                    # behaviour as all shifts from a production with
                    # precedence gain higher precedence for shifts,
                    # choosing the yacc/bison way would make it
                    # unnecessary to record all the transition prods
                    # TODO: work out the consequences, which model
                    # is more intuitive, what are the differences,
                    # where does it matter (obviously it does not
                    # matter in most cases)
                    for item in prods:
                        nprec = item.Prod().number_in_file
                        if nprec > prec:
                            prec = nprec
                            assoc = item.Prod().assoc

                    acur[terminals[symb]] = Shift(tstate.Number(),
                                                  assoc, prec)
                else:
                    print(state, file=sys.stderr)
                    print(str(symb), file=sys.stderr)
                    raise CantHappen()

            # write reductions to the action table
            for item in state.Reductions():
                prod = item.Prod()
                reduceAction = Reduce(prod.number,
                                      prod.assoc,
                                      prod.number_in_file)

                for la in item.Lookahead():
                    acur[terminals[la]] = \
                        self.ResolveConflict(state,
                                             acur[terminals[la]],
                                             reduceAction)

        return ParseTable(atable, jtable, self.start.Number(), rules)

class LALR1StateTransitionGraph(StateTransitionGraph):

    def __init__(self, grammar, logger):
        """
        The LALR(1) State Transition Graph.
        """
        super(LALR1StateTransitionGraph, self).__init__(grammar, logger)

    def Propagate(self):
        """
        Generate the lookahead sets.

        The other parts of this computation are done in the
        `LALR1StateTransitionGraphElement`.

        For details on the algorithm see the Dragon Book.
        """

        self.Kernels()

        # determine token generation and propagation
        for state in self.states:
            state.DeterminePropagationAndGeneration()

        # add EOF to the "$START <- start ." lookahead set
        for item in self.start.Elements():
            if item.Prod().left == self.grammar.RequireMeta("$START"):
                item.SetLookahead(set([self.grammar.RequireEOF()]))

        # set the spontaneously generated lookahead tokens
        for state in self.states:
            state.Generate()

        # propagate the lookahead tokens
        propagated = True
        while propagated:
            propagated = False

            for state in self.states:
                propagated = state.Propagate() or propagated

        self.CloseKernels()

    def GenerateState(self, number, elements):
        return LALR1StateTransitionGraphElement(self, number, elements)

    def Construct(self):

        # construct the starting point (virtual starting node) and use
        # the RequireElement-method to build up the tree

        prod = Production(self.grammar.RequireMeta("$START"),
                          [self.grammar.Start()], -1)

        prod.action = PyText("raise Accept()")

        self.grammar.RequireMeta("$START").AddProd(prod)

        # we use an empty lookahead set to generate the LR(0) automaton
        start = LR1Item(prod,0,set([]))

        self.start = self.RequireState(start.Closure())

        # calculate the LALR(1) lookahead sets
        self.Propagate()


class LR1StateTransitionGraph(StateTransitionGraph):
    """
    The LR(1) State Transition Graph.
    """

    def __init__(self, grammar, logger):
        super(LR1StateTransitionGraph, self).__init__(grammar, logger)

    def Construct(self):

        prod = Production(self.grammar.RequireMeta("$START"),
                          [self.grammar.Start()], -1)
        prod.action = PyText("raise Accept()")

        self.grammar.RequireMeta("$START").AddProd(prod)

        start = LR1Item(prod,0,set([self.grammar.RequireEOF()])).Closure()

        self.start = self.RequireState(start)

    def GenerateState(self, number, elements):
        return LR1StateTransitionGraphElement(self, number, elements)

class LR1StateTransitionGraphElement(object):

    def __init__(self, graph, number, elements):
        self.number = number
        self.graph = graph
        self.elements = elements
        self.transitions = dict()

    def __str__(self):
        lines = []
        lines.append("state: " + str(self.number))

        lines.append("elements:")

        for elem in self.elements:
            lines.append(str(elem))

        lines.append("transitions:")
        for trans in self.transitions:
            lines.append((trans.Symbol().Name() or "None") + " -> " + str(trans.State().number))

        return '\n'.join(lines)

    def Elements(self):
        return self.elements

    def Reductions(self):
        """
        A generator yielding the reduction items in this LR state.
        """
        for elem in self.elements:
            if elem.IsReduce():
                yield elem

    def Transitions(self):
        """
        Return the state transitions.
        """
        return self.transitions

    def Number(self):
        """
        Return the number.
        """
        return self.number

    def Kernel(self):
        """
        Reduce the item set to the Kernel items
        """
        res = set()

        for elem in self.elements:
            if elem.InKernel():
                res.add(elem)

        self.elements = res

    def Close(self):
        """
        Complete the item set to its closure
        """
        res = set()

        for elem in self.elements:
            res |= elem.Closure()

        self.elements = self.graph.NormalizeItemSet(res)

    def GenerateSubStates(self):
        """
        Determine the substates of this state and add them to the
        transition graph.

        Sort the elements by order in file for predictable results.
        """

        for elem in sorted(self.elements,
                           key=lambda elem: elem.Prod().number_in_file):

            if elem.AfterDot():
                goto = set()

                for cur in self.elements:
                    goto |= cur.Goto(elem.AfterDot())

                trans = StateTransition(elem.AfterDot(), self.graph.RequireState(goto))
                if trans not in self.transitions:
                    self.transitions[trans] = set()

                self.transitions[trans].add(elem.Core())

class LALR1StateTransitionGraphElement(LR1StateTransitionGraphElement):

    def __init__(self, graph, number, elements):
        """
        A State in a LALR(1) automaton.
        """
        super(LALR1StateTransitionGraphElement, self).__init__(graph, number, elements)

        self.lapropagation = []
        self.lageneration = []

    def DeterminePropagationAndGeneration(self):
        """
        Determine where and how the LA entries are generated or
        propagate.

        For a detailed explanation of the algorithm see the Dragon
        Book.
        """

        undef = self.graph.grammar.RequireUndef()

        for item in self.elements:

            item.SetLookahead(frozenset([undef]))
            cls = item.Closure()

            for other in cls:
                symb = other.AfterDot()
                if symb is not None:

                    for trans in self.transitions:
                        if trans.Symbol() == symb:
                            stateTo = trans.State()

                            for itemTo in stateTo.Elements():

                                if other.TransitionsTo(itemTo):

                                    for la in other.Lookahead():

                                        if la is undef:
                                            # print "Propagate", self.Number(), stateTo.Number(), item, "->", itemTo
                                            self.lapropagation.append((item, itemTo))

                                        else:
                                            # print "Generate", itemTo, ":", la, "(", item, ")"
                                            stateTo.lageneration.append((itemTo, la))

            item.SetLookahead(frozenset())

    def Generate(self):
        """
        Do the LA entry generation.
        """
        for item, symb in self.lageneration:
            newLa = set(item.Lookahead())
            newLa.add(symb)
            item.SetLookahead(newLa)

    def Propagate(self):
        """
        Do the LA entry propagation.
        """
        propagated = False
        for item, to in self.lapropagation:
            newLa = to.Lookahead() | item.Lookahead()

            if newLa != to.Lookahead():
                to.SetLookahead(newLa)
                propagated = True

        return propagated
