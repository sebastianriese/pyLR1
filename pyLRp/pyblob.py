
from .core import AutoAccept

class PyBlob(object, metaclass=AutoAccept):
    pass

class PySuite(PyBlob):
    def __init__(self):
        self.code = []

    def add(self, blob):
        self.code.append(blob)

class PyNewline(PyBlob):
    pass

class PyText(PyBlob):
    def __init__(self, text):
        self.text = text

class PyStackvar(PyBlob):

    def __init__(self, text=None, num=None, result=False):
        self.text = text
        self.num = num
        self.result = result

PyBlobVisitor = PyBlob.base_visitor()

# XXX: where does this class belong?
class PyBlobStackVarMapVisitor(PyBlobVisitor):

    def __init__(self, varmap):
        self.varmap = varmap

    def VisitPySuite(self, suite):
        for fragment in suite.code:
            fragment.Accept(self)

    def VisitPyText(self, text):
        pass

    def VisitPyNewline(self, newline):
        pass

    def VisitPyStackvar(self, stackvar):
        if stackvar.text == '$$':
            stackvar.result = True
        else:
            stackvar.num = self.varmap(stackvar.text)
