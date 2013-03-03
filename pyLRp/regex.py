
from .nfa import NFAState

class RegexAST(object):
    """An AST representing a regular expression."""

    def NFA(self):
        raise NotImplementedError()

class CharacterRegex(RegexAST):

    def __init__(self, chars):
        self.chars = frozenset(chars)

    def __str__(self):
        return "CharacterRegex({})".format(list(self.chars))

    def NFA(self):
        start = NFAState()
        end = NFAState()

        start.add_transitions(self.chars, end)

        return start, end

class SequenceRegex(RegexAST):

    def __init__(self, regex1, regex2):
        self.regex1, self.regex2 = regex1, regex2

    def __str__(self):
        return "SequenceRegex(%s, %s)" % (str(self.regex1), str(self.regex2))

    def NFA(self):
        nfa1s, nfa1e = self.regex1.NFA()
        nfa2s, nfa2e = self.regex2.NFA()

        # chain the end of the first automaton to the start of the
        # second one with an epsilon transition
        nfa1e.add_transition('', nfa2s)

        return nfa1s, nfa2e

class OptionRegex(RegexAST):

    def __init__(self, regex):
        self.regex = regex

    def __str__(self):
        return "OptionRegex(%s)" % str(self.regex)

    def NFA(self):

        nfas, nfae = self.regex.NFA()

        nfas.add_transition('', nfae)

        return nfas, nfae

class RepeatorRegex(RegexAST):

    def __init__(self, regex):
        self.regex = regex

    def __str__(self):
        return "RepeatorRegex(%s)" % str(self.regex)

    def NFA(self):
        nfas, nfae = NFAState(), NFAState()
        nfars, nfare = self.regex.NFA()

        nfas.add_transition('', nfae)
        nfas.add_transition('', nfars)
        nfare.add_transition('', nfars)
        nfare.add_transition('', nfae)

        return nfas, nfae

class OrRegex(RegexAST):

    def __init__(self, regex1, regex2):
        self.regex1, self.regex2 = regex1, regex2

    def __str__(self):
        return "OrRegex(%s, %s)" % (str(self.regex1), str(self.regex2))

    def NFA(self):

        nfa1s, nfa1e = self.regex1.NFA()
        nfa2s, nfa2e = self.regex2.NFA()
        start, end = NFAState(), NFAState()

        start.add_transition('', nfa1s)
        start.add_transition('', nfa2s)

        nfa1e.add_transition('', end)
        nfa2e.add_transition('', end)

        return start, end

class RegexSyntaxError(Exception):
    pass

class Regex(object):
    """A regular expression with an NFA representation."""

    ESCAPES = {
        'n' : '\n',
        't' : '\t',
        'f' : '\f',
        'v' : '\v',
        'r' : '\r',
        's' : ' \n\t\v\r\f',
        'd' : '0123456789',
        'w' : 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ013456789_'
        }

    def ParseEscape(self, iterator):
        char = next(iterator)

        if char == 'x':
            string = ''
            string += next(iterator)
            string += next(iterator)
            return set(chr(int(string, base=16)))

        return set(self.ESCAPES.get(char, char))

    def ParseChrClass(self, iterator):
        try:
            first = True
            chars = set()
            prev = None
            group = False
            negate = False

            while True:
                char = next(iterator)
                if first:
                    first = False
                    if char == '^':
                        negate = True
                        chars = set(chr(i) for i in range(256))
                        continue

                if char == ']':
                    return chars

                elif char == '-':
                    if prev is None:
                        raise StopIteration()
                    else:
                        group = True
                    continue

                cset = set()
                if char == '\\':
                    cset |= self.ParseEscape(iterator)
                else:
                    cset |= set(char)

                if group:
                    if len(cset) != 1:
                        raise StopIteration()

                    if len(prev) != 1:
                        raise StopIteration()

                    # use tuple unpacking to elegantly extract the
                    # single values from the sets
                    c, = cset
                    p, = prev

                    for char in range(ord(p) + 1, ord(c)):
                        cset.add(chr(char))

                    group = False

                prev = cset

                if negate:
                    chars -= cset
                else:
                    chars |= cset

        except StopIteration:
            raise RegexSyntaxError("unclosed character class")

    def ParseBrace(self, iterator):
        res = ['']
        # we rely on the fact, that (iter(iterator) is iterator)
        # which is specified in the python stdlib docs
        for chr in iterator:
            if chr == '}':
                res[-1] = res[-1].strip()
                try:
                    res = [int(entry) if entry else None for entry in res]
                except ValueError:
                    if len(res) != 1:
                        raise RegexSyntaxError("comma in named regex reference")
                    return (6, res[0])
                else:
                    return (7, res)
            elif chr == ',':
                res[-1] = res[-1].strip()
                res.append('')
            else:
                res[-1] += chr

        raise RegexSyntaxError("unclosed brace expression")

    def lex(self):
        # tokens: CHR ([...], \...,.) - 0, OP (+ ? *) - 1, ( - 2, | - 3, ) - 4
        tokens = []

        iterator = iter(self.regex)
        try:
            while True:
                char = next(iterator)
                if char == '\\':
                    tokens.append((0, self.ParseEscape(iterator)))
                elif char == '[':
                    tokens.append((0, self.ParseChrClass(iterator)))
                elif char == ']':
                    raise RegexSyntaxError("single closing bracket")
                elif char in ('+', '?', '*'):
                    tokens.append((1, char))
                elif char == '|':
                    tokens.append((3, '|'))
                elif char == '(':
                    tokens.append((2, '('))
                elif char == ')':
                    tokens.append((4, ')'))
                elif char == '.':
                    tokens.append((0, set(chr(i) for i in range(0,256)) - set('\n')))
                elif char == '{':
                    tokens.append(self.ParseBrace(iterator))
                elif char == '}':
                    raise RegexSyntaxError("single closing brace")
                else:
                    tokens.append((0, set(char)))

        except StopIteration:
            tokens.append((5, ''))
            return tokens

    def Parse(self, bindings):

        tokens = iter(self.lex())
        current_token = next(tokens)

        def ParseOr():
            nonlocal current_token

            first = ParseChain()
            if first is None:
                first = CharacterRegex([''])

            if current_token[0] == 3:
                current_token = next(tokens)
                second = ParseOr()
                return OrRegex(first, second)

            return first


        def ParseChain():
            first = ParseOp()
            if first is None:
                return None
            else:
                second = ParseChain()
                if second is None:
                    return first
                else:
                    return SequenceRegex(first, second)

        def ParseOp():
            nonlocal current_token

            basic = ParseBasic()
            if basic is None:
                return None

            token, lexeme = current_token
            if token == 1:
                if lexeme == '+':
                    res = SequenceRegex(basic, RepeatorRegex(basic))

                elif lexeme == '*':
                    res = RepeatorRegex(basic)

                elif lexeme == '?':
                    res = OptionRegex(basic)

                else:
                    # this is a bug in the implementation!
                    raise CantHappen()
                current_token = next(tokens)
            elif token == 7:
                try:
                    start = lexeme[0]
                    if start <= 0:
                        raise ValueError

                    if len(lexeme) == 1:
                        # exactly {n} times
                        res = basic
                        for i in range(1, start):
                            res = SequenceRegex(basic, res)
                    elif len(lexeme) == 2:
                        stop = lexeme[1]

                        if stop is not None:
                            # between {n, m} times
                            if stop <= 0:
                                raise ValueError

                            res = basic
                            for i in range(1, start):
                                res = SequenceRegex(basic, res)

                            if stop > start:
                                opt_basic = OrRegex(basic, CharacterRegex(['']))
                                for i in range(start, stop):
                                    res = SequenceRegex(res, opt_basic)
                            elif start == stop:
                                res = res1
                            else:
                                raise RegexSyntaxError("m greater than n in {m,n}-style repeator")

                        else:
                            # more than {n, } times
                            res = RepeatorRegex(basic)
                            for i in range(start):
                                res = SequenceRegex(basic, res)
                    else:
                        raise RegexSyntaxError("too many numbers in repetition operator")
                except ValueError:
                    raise RegexSyntaxError("item in brace repitition operator not a positive integer")
                current_token = next(tokens)
            else:
                res = basic

            return res

        def ParseBasic():
            nonlocal current_token
            token, lexeme = current_token

            if token == 0:
                res = CharacterRegex(lexeme)
                current_token = next(tokens)
                return res

            elif token == 2:
                current_token = next(tokens)
                res = ParseOr()
                if current_token[0] != 4:
                    raise RegexSyntaxError("missing closing paren")

                current_token = next(tokens)
                return res
            elif token == 6:
                try:
                    res = bindings[lexeme]
                except KeyError:
                    raise RegexSyntaxError("unbound named pattern {{{}}}".format(lexeme))
                current_token = next(tokens)
                return res
            else:
                return None

        res = ParseOr()

        token, lexeme = current_token
        if token == 1:
            raise RegexSyntaxError("missing argument for '{}' operator".format(lexeme))
        elif token == 4:
            raise RegexSyntaxError("superfluous closing paren")
        elif token == 5: # parsed up to EOF, we are happy
            return res
        else:
            raise CantHappen()

    def __init__(self, regex, bindings=None):
        self.regex = regex
        self.ast = self.Parse(bindings or {})

    def NFA(self):
        return self.ast.NFA()
