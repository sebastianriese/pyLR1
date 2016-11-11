
from .core import AutoAccept

class PyBlob(object, metaclass=AutoAccept):
    _subclasses_ = []

    def accept(self, visitor):
        raise NotImplementedError()

class PySuite(PyBlob):
    def __repr__(self):
        return "PyBlob({})".format(repr(self.code))

    def __init__(self, code=None):
        if code is None:
            self.code = []
        else:
            self.code = code

    def add(self, blob):
        self.code.append(blob)

    def flatten(self):
        res = [None]
        for item in self.code:
            if isinstance(item, PyText):
                if isinstance(res[-1], PyText):
                    res[-1] = PyText(res[-1].text + item.text)
                    continue
            res.append(item)
        self.code = res[1:]

class PyNewline(PyBlob):
    def __repr__(self):
        return "PyNewline()"

class PyText(PyBlob):
    def __init__(self, text):
        self.text = text

    def __repr__(self):
        return "PyText({})".format(repr(self.text))

class PyStackvar(PyBlob):

    def __repr__(self):
        return "PyStackvar({}, {}, {}, {})".format(repr(self.text),
                                                   repr(self.num),
                                                   repr(self.result),
                                                   repr(self.position))

    def __init__(self, text=None, num=None, result=False, position=None):
        self.position = position
        self.text = text
        self.num = num
        self.result = result

PyBlobVisitor = PyBlob.base_visitor()
