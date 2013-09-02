
from .core import AutoAccept

class PyBlob(object, metaclass=AutoAccept):
    _subclasses_ = []

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
        self.position = position
        self.text = text
        self.num = num
        self.result = result

PyBlobVisitor = PyBlob.base_visitor()
