#!/usr/bin/python3

from subprocess import call
from glob import glob

PY3 = '/usr/bin/python3'
PYLRP = "../../pyLRp.py"

for testcase in glob('*.pyLRp'):
    call([PY3, PYLRP, '-lL2', '-o', '/dev/null', testcase])
