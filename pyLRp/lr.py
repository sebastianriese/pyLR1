
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

    def __init__(self, left, syms, number=-1):
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
                result |= sub.first(visited | set([self])) - set([Empty()])

            if not sub.reduces_to_empty():
                break

        else:
            result.add(Empty())

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

        if elem.is_empty:
            return Production(None, self)

        return Production(None, self._syms + [elem])


class LR1Item(object):
    """A LR(1) item (production, position, lookahead set)

    The public accessors are:
    * lookahead, the lookahead set
    * prod (readonly), the production from the grammar
    * pos (readonly), the position of the mark in the production
    """

    def __init__(self, prod, pos, la):
        self._prod = prod
        self._pos = pos
        self._lookahead = frozenset(la)

    def __str__(self):
        text =  (self.prod.left.name or "None") + " <- "
        dotted = False
        for count, sub in enumerate(self._prod):
            if count == self._pos:
                text += ". "
                dotted = True

            text += (sub.name or "None") + " "

        if not dotted:
            text += ". "

        text += "{ "

        for sub in self._lookahead:
            text += (sub.name or "None") + " "

        text += "}"

        return text

    _closure = dict()

    @classmethod
    def from_core(cls, lr0, la):
        """
        Reconstruct an item set from its core (that is LR(0) item) and
        lookahead set.
        """
        return cls(lr0.prod, lr0.pos, la)

    def __hash__(self):
        return hash(self._prod) \
            ^ hash(self._pos) \
            ^ hash(self._lookahead)

    def __eq__(self, other):
        return self._prod == other._prod \
            and self._pos == other._pos \
            and self._lookahead == other._lookahead

    def in_kernel(self):
        """
        Return whether this LR(1) item is part of the Kernel (either
        it is a $START production or the position mark is not in the
        first place)
        """
        return self._pos != 0 or (self._prod.left.name == "$START")

    def after_dot(self):
        """
        Return the symbol that immediately follows the mark. If the
        mark is behind the last symbol of the production return None.
        """
        try:
            return self._prod[self._pos]
        except IndexError:
            return None

    def is_reduce(self):
        """
        Return wheter this is a reduce production (the mark is after
        the last symbol).
        """
        return self.after_dot() is None

    @property
    def prod(self):
        return self._prod

    @property
    def pos(self):
        return self._pos

    @property
    def lookahead(self):
        return self._lookahead

    @lookahead.setter
    def lookahead(self, la):
        if (self._prod, self._pos, self._lookahead) in self._closure:
            # the buffered closure is no longer valid, once a new
            # lookahead set is assigned
            del self._closure[(self._prod, self._pos, self._lookahead)]

        self._lookahead = frozenset(la)

    def core(self):
        """
        Return the LR(0) item which results, when you strip this LR(1)
        item of its lookahead set.
        """
        return LR1Item(self._prod, self._pos, frozenset())

    def goto(self, symbol):
        """
        Calculate the GOTO set of ``symbol`` with respect to this
        production.
        """
        after_dot = self.after_dot()
        result = set()

        if after_dot == symbol:
            result |= LR1Item(self._prod, self._pos+1, self._lookahead).closure()

        return result

    def closure(self, visited=None):
        """
        Calculate the CLOSURE of the LR(1) item set containing this
        item.
        """
        # possibly the buffering is buggy
        if (self._prod, self._pos, self._lookahead) in self._closure:
             return self._closure[(self._prod, self._pos, self._lookahead)]

        if visited is None:
            visited = frozenset()

        closure = set([self])
        after_dot = self.after_dot()
        recurses = False

        if after_dot:
            laset = set()

            for la in self._lookahead:
                firstconcat = self.prod[self.pos+1:].concat(la)
                laset |= firstconcat.first()

            for prod in after_dot.productions():

                if self not in visited:
                    elem = LR1Item(prod, 0, laset)
                    closure |= elem.closure(visited | set([self]))
                else:
                    recurses = True

        if not recurses:
            self._closure[(self._prod, self._pos, self._lookahead)] = closure

        return closure

    def transitions_to(self, other):
        """
        Determine whether the LR item generates `other` on transition.
        """

        if self.is_reduce():
            return False

        return self._prod == other._prod and self._pos + 1 == other._pos


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
        self.grammar.symtable.require_recover()

    def report_num_of_conflicts(self):
        if self.conflicts:
            self.logger.warning(str(self.conflicts) + " conflict(s) found!")

    @abc.abstractmethod
    def construct(self):
        """
        Construct the *LR(1) automaton.
        """
        pass

    def normalize_item_set(self, elements):
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
            if elem.core() not in cores:
                cores[elem.core()] = set()

            cores[elem.core()] |= elem.lookahead

        elements = set()
        for core in cores:
            elements.add(LR1Item.from_core(core, cores[core]))
        cores = None

        return elements

    def require_state(self, elements):
        """
        Check whether a state having the given elements already
        exists. If it does exist return it, otherwise create the new
        state and recursively determine its sub states.
        """

        elements = self.normalize_item_set(elements)

        # do we already have this state?
        for state in self.states:
            if state.same_state_by_elements(elements):
                return state

        # instanciate the new state
        state = self.generate_state(len(self.states), elements)
        self.states.append(state)
        state.generate_substates()
        return state

    @abc.abstractmethod
    def generate_state(self, number, elements):
        """
        Generate an appropriate `LR1StateGraphElement`. Where `number`
        is the assigned id number and `elements` is the associated set
        of LR1Items.
        """
        pass

    def resolve_conflict(self, state, old, new):
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

        if old.is_reduce:
            self.logger.info(str(state))
            self.logger.warning("Default to the first reduce for "
                                "reduce/reduce-conflict")
            self.conflicts += 1
            if old.number_in_file > new.number_in_file:
                return new
            else:
                return old

        elif old.is_shift:
            assoc, prec = old.assoc
            associ, preci = new.assoc

            # shift wins over reduce by default
            if assoc == Production.NONE:
                self.logger.info(str(state))
                self.logger.warning("Default to shift for "
                                    "shift/reduce-conflict")
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


    def kernels(self):
        """
        Reduce the item sets to their kernels
        (needed for LALR lookahead generation)
        """
        for state in self.states:
            state.kernel()

    def close_kernels(self):
        """
        Complete the sets to their closure again
        after they where reduced to their kernels
        """

        for state in self.states:
            state.close()

    def create_next_table(self):
        """
        Create a table mapping states to a reduced set of symbols which are
        acceptable in those states.

        Symbols which occur on the beginning of productions whose meta symbol
        is acceptable as next symbol are not included.
        """

        next_table = {}
        for state in self.states:
            changed = True
            transition_mapping = {}
            in_rhs = set()
            for elem in state.elements():
                after_dot = elem.after_dot()
                if after_dot is None:
                    continue
                transition_mapping.setdefault(
                    elem.prod.left,
                    set()
                ).add(elem.after_dot())
                in_rhs.add(elem.after_dot())

            while changed:
                new_in_rhs = set()
                for rhs_item in in_rhs:
                    try:
                        del transition_mapping[rhs_item]
                    except KeyError:
                        pass
                for rhs in transition_mapping.values():
                    new_in_rhs |= rhs
                changed = new_in_rhs != in_rhs
                in_rhs = new_in_rhs

            next_table[state] = frozenset(in_rhs)

        return next_table

    def create_parse_table(self, terminals, metas):
        """
        Create the parse table from the LR graph. Requires two mappings
        from `Symbol` objects to their respective numbers: One of them
        for the terminals and another for the meta-symbols.

        They can be created from the `Symtable` object by calling its
        ``terminals`` resp. ``metas`` methods.

        The function returns a `Parsetable` object.
        """
        atable = []
        jtable = []

        rules = []

        # populate the rules vector
        for meta in sorted(metas, key=lambda meta: metas[meta]):
            for rule in meta.productions():
                rule.number = len(rules)
                rules.append(rule)

        for state in self.states:
            # append the current row to the action- and jumptables
            acur = [None] * len(terminals)
            jcur = [None] * len(metas)

            atable.append(acur)
            jtable.append(jcur)

            # fill goto table and write shifts to the action table
            for trans, prods in state.transitions():
                symb = trans.symbol
                tstate = trans.state

                if symb in metas:
                    jcur[metas[symb]] = tstate.number

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
                        nprec = item.prod.number_in_file
                        if nprec > prec:
                            prec = nprec
                            assoc = item.prod.assoc

                    acur[terminals[symb]] = Shift(tstate.number,
                                                  assoc, prec)
                else:
                    print(state, file=sys.stderr)
                    print(str(symb), file=sys.stderr)
                    raise CantHappen()

            # write reductions to the action table
            for item in state.reductions():
                prod = item.prod
                reduceAction = Reduce(prod.number,
                                      prod.assoc,
                                      prod.number_in_file)

                for la in item.lookahead:
                    acur[terminals[la]] = \
                        self.resolve_conflict(state,
                                              acur[terminals[la]],
                                              reduceAction)

        return ParseTable(atable, jtable, self.start.number, rules)


class LALR1StateTransitionGraph(StateTransitionGraph):

    def __init__(self, grammar, logger):
        """
        The LALR(1) State Transition Graph.
        """
        super(LALR1StateTransitionGraph, self).__init__(grammar, logger)

    def propagate(self):
        """
        Generate the lookahead sets.

        The other parts of this computation are done in the
        `LALR1StateTransitionGraphElement`.

        For details on the algorithm see the Dragon Book.
        """

        self.kernels()

        # determine token generation and propagation
        for state in self.states:
            state.determine_propagation_and_generation()

        # add EOF to the "$START <- start ." lookahead set
        for item in self.start.elements():
            if item.prod.left == self.grammar.symtable.define_meta("$START"):
                item.lookahead = set([self.grammar.symtable.require_EOF()])

        # set the spontaneously generated lookahead tokens
        for state in self.states:
            state.generate()

        # propagate the lookahead tokens
        propagated = True
        while propagated:
            propagated = False

            for state in self.states:
                propagated = state.propagate() or propagated

        self.close_kernels()

    def generate_state(self, number, elements):
        return LALR1StateTransitionGraphElement(self, number, elements)

    def construct(self):

        # construct the starting point (virtual starting node) and use
        # the RequireElement-method to build up the tree

        prod = Production(self.grammar.symtable.define_meta("$START"),
                          [self.grammar.grammar.start_symbol], -1)

        prod.action = PyText("raise Accept()")

        self.grammar.symtable.define_meta("$START").add_prod(prod)

        # we use an empty lookahead set to generate the LR(0) automaton
        start = LR1Item(prod, 0, set([]))

        self.start = self.require_state(start.closure())

        # calculate the LALR(1) lookahead sets
        self.propagate()


class LR1StateTransitionGraph(StateTransitionGraph):
    """
    The LR(1) State Transition Graph.
    """

    def __init__(self, grammar, logger):
        super(LR1StateTransitionGraph, self).__init__(grammar, logger)

    def construct(self):

        prod = Production(self.grammar.symtable.define_meta("$START"),
                          [self.grammar.grammar.start_symbol], -1)
        prod.action = PyText("raise Accept()")

        self.grammar.symtable.define_meta("$START").add_prod(prod)

        start = LR1Item(prod, 0, set([self.grammar.symtable.require_EOF()])).closure()

        self.start = self.require_state(start)

    def generate_state(self, number, elements):
        return LR1StateTransitionGraphElement(self, number, elements)


class LR1StateTransitionGraphElement(object):

    def __init__(self, graph, number, elements):
        self._number = number
        self.graph = graph
        self._elements = elements
        self._transitions = dict()

    def __str__(self):
        lines = []
        lines.append("state: " + str(self._number))

        lines.append("elements:")
        for elem in self._elements:
            lines.append(str(elem))

        lines.append("transitions:")
        for trans in self._transitions:
            lines.append((trans.symbol.name or "None") +
                         " -> " + str(trans.state.number))

        return '\n'.join(lines)

    def same_state_by_elements(self, elements):
        """
        Return whether the set `elements` is the same as the elements
        in this state.
        """
        return elements == self._elements

    def elements(self):
        return iter(self._elements)

    def reductions(self):
        """
        A generator yielding the reduction items in this LR state.
        """
        return filter(lambda elem: elem.is_reduce(), self._elements)

    def transitions(self):
        """
        Return the state transitions.
        """
        return self._transitions.items()

    @property
    def number(self):
        """
        Return the number.
        """
        return self._number


    def kernel(self):
        """
        Reduce the item set to the Kernel items
        """
        res = set()

        for elem in self._elements:
            if elem.in_kernel():
                res.add(elem)

        self._elements = res

    def close(self):
        """
        Complete the item set to its closure
        """
        res = set()

        for elem in self._elements:
            res |= elem.closure()

        self._elements = self.graph.normalize_item_set(res)

    def generate_substates(self):
        """
        Determine the substates of this state and add them to the
        transition graph.

        Sort the elements by order in file for predictable results.
        """

        for elem in sorted(self._elements,
                           key=lambda elem: elem.prod.number_in_file):

            if elem.after_dot():
                goto = set()

                for cur in self._elements:
                    goto |= cur.goto(elem.after_dot())

                trans = StateTransition(elem.after_dot(),
                                        self.graph.require_state(goto))

                if trans not in self._transitions:
                    self._transitions[trans] = set()

                self._transitions[trans].add(elem.core())

class LALR1StateTransitionGraphElement(LR1StateTransitionGraphElement):

    def __init__(self, graph, number, elements):
        """
        A State in a LALR(1) automaton.
        """
        super(LALR1StateTransitionGraphElement, self).__init__(graph, number,
                                                               elements)

        self._lapropagation = []
        self._lageneration = []

    def determine_propagation_and_generation(self):
        """
        Determine where and how the LA entries are generated or
        propagate.

        For a detailed explanation of the algorithm see the Dragon
        Book.
        """

        undef = self.graph.grammar.symtable.require_undef()

        for item in self._elements:

            item.lookahead = frozenset([undef])
            cls = item.closure()

            for other in cls:
                symb = other.after_dot()
                if symb is None:
                    continue

                for trans in self._transitions:
                    if trans.symbol != symb:
                        continue

                    state_to = trans.state

                    for item_to in state_to.elements():

                        if other.transitions_to(item_to):

                            for la in other.lookahead:
                                if la is undef:
                                    self._lapropagation.append((item, item_to))
                                else:
                                    state_to._lageneration.append((item_to, la))

            item.lookahead = frozenset()

    def generate(self):
        """
        Do the LA entry generation.
        """
        for item, symb in self._lageneration:
            new_lookahead = set(item.lookahead)
            new_lookahead.add(symb)
            item.lookahead = new_lookahead

    def propagate(self):
        """
        Do the LA entry propagation.
        """
        propagated = False
        for item, to in self._lapropagation:
            new_lookahead = to.lookahead | item.lookahead

            if new_lookahead != to.lookahead:
                to.lookahead = new_lookahead
                propagated = True

        return propagated
