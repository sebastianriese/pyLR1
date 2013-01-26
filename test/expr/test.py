#!/usr/bin/python3

from subprocess import call
from glob import glob

PY3 = '/usr/bin/python3'
PYLRP = "../../pyLRp.py"

call([PY3, PYLRP, '-lL3', '-o', 'expr.py', 'expr.pyLRp'])

import expr

for testcase in glob('*.expr'):
    print(testcase, expr.Parser(expr.Lexer(testcase)).Parse())
