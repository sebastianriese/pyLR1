
from .core import AutoAccept

class PyBlob(object, metaclass=AutoAccept):

    def accept(self, visitor):
        raise NotImplementedError()

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

    def __init__(self, text=None, num=None, result=False, position=None):
        self.position = positions
        self.text = text
        self.num = num
        self.result = result

PyBlobVisitor = PyBlob.base_visitor()

# XXX: where does this class belong?
class PyBlobStackVarMapVisitor(PyBlobVisitor):

    def __init__(self, varmap):
        self.varmap = varmap

    def visit_PySuite(self, suite):
        for fragment in suite.code:
            fragment.accept(self)

    def visit_PyText(self, text):
        pass

    def visit_PyNewline(self, newline):
        pass

    def visit_PyStackvar(self, stackvar):
        if stackvar.text == '$$':
            stackvar.result = True
        else:
            stackvar.num = self.varmap(stackvar.text)

