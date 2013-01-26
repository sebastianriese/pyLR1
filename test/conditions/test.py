#!/usr/bin/python3

from subprocess import call
from glob import glob

PY3 = '/usr/bin/python3'
PYLRP = "../../pyLRp.py"

call([PY3, PYLRP, '-lL3', '-o', 'cond.py', 'cond.pyLRp'])

import cond

for testcase in glob('*.cond'):
    print(testcase)
    print(cond.Lexer(testcase).lexAll())
    cond.Parser(cond.Lexer(testcase)).Parse()
