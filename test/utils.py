
import io
import sys
import logging
import unittest

import pyLRp

# perhaps I should just use logging.shutdown
# and reinitialize afterwards, I am afraid
# they don't die this way
def counted_make_logger(name):
    LOGGER_COUNTER = 0
    def get_logger():
        nonlocal LOGGER_COUNTER
        res = logging.getLogger('{}{}'.format(name, LOGGER_COUNTER))
        LOGGER_COUNTER += 1
        return res
    return get_logger

unique_logger = counted_make_logger('pyLRtest')

class CheckingHandler(logging.Handler):

    def __init__(self, logmessages):
        """
        A handler to check the emitted messages with a coroutine
        `logmessages`.  `next` is once applied to `logmessages`,
        afterwards the logging records are passed to it via `.send()`.

        This is used to verify logmessages generated on the logger the
        `CheckingHandler` is added to.

        If `logmessages` raises *StopIteration* an assertion will
        fail. For more specific error messages add something like:

            def logchecker():
                while True:
                    yield
                    self.fail("unexpected log entry")

        where `logchecker` is a closure in a method of your test case.
        """
        super().__init__()
        self.checker = logmessages
        next(self.checker)

    def emit(self, record):
        try:
            self.checker.send(record)
        except StopIteration:
            assert False

class FailOnLogHandler(logging.Handler):

    def __init__(self, test_case):
        """
        A handler designed to fail, whenever anything is
        logged. `test_case` is the instance of a `TestCase` to which
        the failure shall be reported.
        """
        super().__init__()
        self.test_case = test_case

    def emit(self, record):
        """
        Fail if warnings are logged
        """
        self.test_case.fail("unexpected log message during build: {}"
                            .format(record.getMessage()))

class ParseResultTestCase(unittest.TestCase):
    """
    A test case should inherit from this class, if it verfies the
    results of parsing.

    XXX: rename methods assertParseResultEq, assertParseSyntaxError ?
    """

    def verify_parse_result(self, parser, source, result):
        """
        Verify the result of parsing `source` with the generated
        module `parser` produces `result`
        """
        ast = parser["Parser"](parser["Lexer"](source, string=True)).Parse()
        self.assertEqual(ast, result)

    def verify_syntax_error(self, parser, source):
        """
        Verify the result of parsing `source` with the generated
        module `parser` raises `parser["SyntaxError"]`
        """
        with self.assertRaises(parser["SyntaxError"]):
            parser["Parser"](parser["Lexer"](source, string=True)).Parse()


class FailOnLogTestCase(unittest.TestCase):

    def compile(self, source, listing=None, trace=False):
        self.logger = unique_logger()
        self.logger.addHandler(FailOnLogHandler(self))
        return compile(self.logger, source, listing=listing, trace=trace)


def compile(logger, source, listing=None, trace=False):
    """
    Compile the given parser spec down to a python module

    We might want to code this sequence in pyLRp, because anyone
    using the lib from code wants this! Break up the Syntax class.
    """
    codelines = source.split('\n')

    parser = pyLRp.Parser(codelines, logger)
    syn = parser.Parse()
    del parser

    syn.RequireError()
    parseTable = None
    if syn.Start() is not None:
        graph = pyLRp.LALR1StateTransitionGraph(syn, logger)
        graph.Construct()

        termsyms = frozenset([pyLRp.Syntax.TERMINAL,
                              pyLRp.Syntax.EOF,
                              pyLRp.Syntax.ERROR])
        parseTable = graph.CreateParseTable(
            syn.SymTableMap(filt=lambda x: x.SymType() in termsyms,
                            value=lambda x: x.Number()),
            syn.SymTableMap(filt=lambda x: x.SymType() == pyLRp.Syntax.META,
                            value=lambda x: x.Number())
            )
        graph.ReportNumOfConflicts()
        # for state in graph.states:
        #     print(str(state))
        del graph
    else:
        syn.RequireEOF()

    lexer = pyLRp.LexerConstructor(syn, logger)
    lexer.ConstructDFAs()
    lexer.DropNFA()
    lexer.Optimize()
    lexer.CreateLexTables()
    lexer.DropDFA()
    lexer.ConstructEquivalenceClasses()

    code = io.StringIO()
    w = pyLRp.Writer(code, logger,
                     lines=False, trace=trace, debug=trace,
                     deduplicate=True, python3=True)
    w.Write(syn, parseTable, lexer)
    result = {}

    # create a listing for debugging purposes
    if listing is not None:
        for slice in listing:
            print('\n'.join("{:4d}:{}".format(slice.start+relline,src)
                            for relline, src
                            in enumerate(code.getvalue().split('\n')[slice])))

    # compile the generated lexer and parser
    exec(code.getvalue(), result)
    return result, syn.SymTable()
