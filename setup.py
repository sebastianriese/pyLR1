from distutils.core import setup
import distutils.command.build_py

import subprocess

import pyLRp

class build_pyLRp(distutils.command.build_py.build_py):

    def run(self):
        subprocess.call(['python3', '-m', 'pyLRp',
                         '-lLd3', '--bootstrap',
                         'pyLRp/parsers/pyLRparser.pyLRp'])
        super().run()

setup(name='pyLRp',
      version=pyLRp.__version__,
      description='A pure python lexer and {LA,}LR(1) parser generator',
      author='Sebastian Riese',
      author_email='sebatian.riese.mail@web.de',
      url='https://github.com/sebastianriese/pyLR1/',
      packages=['pyLRp', 'pyLRp.parsers', 'pyLRp.writers', 'pyLRp.test'],
      license='MIT',
      cmdclass={'build_py': build_pyLRp}
      )
