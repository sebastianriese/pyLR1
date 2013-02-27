
import re
import sys
import logging
import argparse
import tempfile
import shutil

from . import __version__
from .lr import LALR1StateTransitionGraph, LR1StateTransitionGraph
from .syntax import Syntax
from .lexer import *
from .writers.pywriter import Writer

class CountingLogger(logging.getLoggerClass()):

    class ErrorsOccured(Exception):
        pass

    def __init__(self, name):
        """
        A logger that counts errors.

        `name` is passed on.
        """
        super().__init__(name)
        self.errors = 0

    def raiseOnErrors(self):
        """
        Raise the exception `ErrorsOccured` of there were errors.
        """
        if self.errors > 0:
            raise CountingLogger.ErrorsOccured()

    def exitOnErrors(self, exitCode=1):
        """
        Exit if there were errors.
        """
        sys.exit(exitCode)

    def loggedErrors(self):
        """
        Return true if there were errors.
        """
        return bool(self.errors)

    def error(self, msg, *args, **kwargs):
        self.errors += 1
        super().error(msg, *args, **kwargs)


arg_parser = argparse.ArgumentParser(
    version=__version__,
    prog='pyLRp',
    formatter_class=argparse.RawDescriptionHelpFormatter,
    description="A pure python LALR(1)/LR(1) parser generator and lexer generator.")

arg_parser.add_argument("-o", "--output-file",
                        dest="ofile",
                        help="Set the output file to OFILE [default: derived from infile]")

arg_parser.add_argument("-l", "--line-tracking",
                        dest="lines",
                        action='store_true',
                        default=False,
                        help="Enable line tracking in the generated parser")

arg_parser.add_argument("-L", "--lalr",
                        dest="lalr",
                        action='store_true',
                        default=False,
                        help="Generate a LALR(1) parser instead of a LR(1) parser")

arg_parser.add_argument("-g", "--print-graph",
                        dest="graph",
                        action='store_true',
                        default=False,
                        help="Print the LR state graph to stdout")

arg_parser.add_argument("--print-lextable",
                        action='store_true',
                        default=False,
                        help="Print the lextables to stdout")

arg_parser.add_argument("-D", "--not-deduplicate",
                        dest="deduplicate",
                        action='store_false',
                        default=True,
                        help="Compress tables by reusing identical lines")

arg_parser.add_argument("-d", "--debug",
                        dest='debug',
                        action='store_true',
                        default=False,
                        help="Write debug information to the generated file")

arg_parser.add_argument("-f", "--fast",
                        dest="fast",
                        action='store_true',
                        default=False,
                        help="Fast run: generates larger and possibly slower parsers, but takes less time")

arg_parser.add_argument("-q", "--quiet",
                        dest="quiet",
                        action='store_true',
                        default=False,
                        help="Print less info")

arg_parser.add_argument("-T", "--trace",
                        dest="trace",
                        action='store_true',
                        default=False,
                        help="Generate a parser that prints out a trace of its state")

arg_parser.add_argument("--self-hosting", action='store_true', default=False)

py_version = arg_parser.add_mutually_exclusive_group()

py_version.add_argument("-3", "--python3",
                        dest="python3",
                        action='store_true',
                        default=True,
                        help="Generate python3 compatible parser [default]")

py_version.add_argument("-2", "--python2",
                        dest="python3",
                        action='store_false',
                        default=True,
                        help="Generate python2 compatible parser")


arg_parser.add_argument("infile",
                        help="The parser specification to process")

args = arg_parser.parse_args()

# determine the name of the output file if it is not given
# explicitly
if not args.ofile:
    m = re.match(r'(.*\.py)LRp?$', args.infile)
    if m:
        args.ofile = m.group(1)
    else:
        args.ofile = args.infile + '.py'

# setup logging for error reporting
logging.basicConfig(format="{msg}", style="{")
logging.setLoggerClass(CountingLogger)
logger = logging.getLogger('pyLR1')
logger.setLevel(logging.WARNING if args.quiet else logging.INFO)

# parse the input file
try:
    infile = open(args.infile, 'rt')
except IOError as e:
    print(str(e), file=sys.stderr)
    sys.exit(1)

if args.self_hosting:
    from .parsers.pyLRparser import Parser, Lexer
    p = Parser(Lexer(infile, filename=args.infile))
    p.Parse()
    syn = p.syntax
else:
    from .parsers.bootstrap import Parser
    p = Parser(infile, logger)
    syn = p.Parse()
    del p
infile.close()

if logger.loggedErrors():
    sys.exit(1)

# construct the parser
parseTable = None

# XXX: should we be more strict here and not generate a parser
# when no %parser section is present but error on an empty
# %parser section
if syn.Start() is not None:
    if args.lalr:
        graph = LALR1StateTransitionGraph(syn, logger)
    else:
        graph = LR1StateTransitionGraph(syn, logger)

    graph.Construct()

    if args.graph:
        for state in graph.states:
            print(str(state))

    termsyms = frozenset([Syntax.TERMINAL, Syntax.EOF, Syntax.ERROR])
    parseTable = graph.CreateParseTable(
        syn.SymTableMap(filt=lambda x: x.SymType() in termsyms,
                        value=lambda x: x.Number()),
        syn.SymTableMap(filt=lambda x: x.SymType() == Syntax.META,
                        value=lambda x: x.Number())
        )
    graph.ReportNumOfConflicts()
    del graph
else:
    # generate the tokens required by the parser
    # and used for special lexer conditions
    syn.RequireEOF()

# construct the lexer
lexer = LexerConstructor(syn, logger)

lexer.ConstructDFAs()
lexer.DropNFA()

if not args.fast:
    lexer.Optimize()

lexer.CreateLexTables()
lexer.DropDFA()

if args.print_lextable:
    lexer.PrintTables()

if not args.fast:
    lexer.ConstructEquivalenceClasses()

if logger.loggedErrors():
    sys.exit(1)

# write lexer and parser
try:
    with tempfile.TemporaryFile(mode="w+t") as temp_gen:
        writer = Writer(temp_gen, logger,
                        lines=args.lines,
                        trace=args.trace,
                        deduplicate=args.deduplicate,
                        debug=args.debug,
                        python3=args.python3)

        writer.Write(syn, parseTable, lexer)

        if logger.loggedErrors():
            print("error: ", e, file=sys.stderr)
            sys.exit(1)

        with open(args.ofile, "wt") as fo:
            temp_gen.seek(0)
            shutil.copyfileobj(temp_gen, fo)
except Exception as e:
    print("error: ", e, file=sys.stderr)
    sys.exit(1)