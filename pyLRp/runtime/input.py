import sys
from io import StringIO
import mmap

class Position(object):
    def __init__(self, file, line0, col0, line1, col1):
        self.file  = file
        self.line0 = line0
        self.col0  = col0
        self.line1 = line1
        self.col1  = col1

    def Add(self, oth):
        return Position(self.file, self.line0, self.col0, oth.line1, oth.col1)

    def __str__(self):
        return "{:s} Line {:d}:{:d} - {:d}:{:d}".format(
            self.file, self.line0, self.col0, self.line1, self.col1)

class EndOfFile(Exception):
    pass

class InputBuffer(object):

    def __init__(self):
        self._mapping = lambda x: x

    def mark(self):
        """
        Remember this position as the latest possible match.
        """
        raise NotImplementedError()

    def step(self):
        """
        Step forward one input character and return the new character.
        raises `EndOfFile` when no further characters are ready.
        """

    def discard(self):
        """
        Discard the currently marked text. Equivalent to `extract` and
        ignoring the return value.
        """
        self.extract()

    def set_mapping(self, mapping):
        """
        Set the mapping input symbol to DFA symbol.
        """
        self._mapping = mapping

    def extract(self):
        """
        Extract the current text and perform line-counting. Returns
        the tuple `token, position`.
        """
        raise NotImplementedError()

    def not_stepped(self):
        """
        Return *True* if there was no call to `step` that did not
        raise `EndOfFile`. Return *False* otherwise.
        """
        raise NotImplementedError()

    def pos(self):
        """
        Return the current position.
        """

class BlockInputBuffer(InputBuffer):
    pass

class FullFileInputBuffer(InputBuffer):

    def __init__(self, buffer, size, filename, encoding='utf-8'):
        super().__init__()
        self._buffer = buffer
        self._size = size
        self._filename = filename
        self._root = 0
        self._pos = 0
        self._encoding = encoding

        self._line = 1
        self._start_of_line = 0

    def step(self):
        if self._pos == self._size:
            raise EndOfFile
        cur = self._mapping(self._buffer[self._pos])
        self._pos += 1
        return cur

    def not_stepped(self):
        return self._root == self._pos

    def pos(self):
        return Position(self._filename,
                        self._line,
                        self._pos - self._start_of_line,
                        self._line,
                        self._pos - self._start_of_line)

    def mark(self):
        self._mark = self._pos

    def discard(self):
        self.extract()

    def extract(self):
        text = self._buffer[self._root:self._mark].decode(self._encoding)

        # calculate line numbers
        line0 = self._line
        sol0 = self._start_of_line
        self._line += text.count('\n')
        sol1 = text.rfind('\n')
        if sol1 != -1:
            self.start_of_line = self._root + sol1 + 1
        pos = Position(self._filename,
                       line0,
                       self._root - sol0,
                       self._line,
                       self._mark - self._start_of_line)

        # reset buffer position markers
        self._pos = self._mark
        self._root = self._mark

        return text, pos


class MmapInputBuffer(FullFileInputBuffer):

    def __init__(self, fname_or_object, filename='<>', close=True, slurp=False):

        if isinstance(fname_or_object, str):
            close = True
            filename = fname_or_object
            fname_or_object = open(fname_or_object, 'rb')

        try:
            buffer = mmap.mmap(fname_or_object.fileno(), 0,
                               access=mmap.ACCESS_READ)
            size = buffer.size()
        except mmap.error:
            if slurp:
                buffer = fname_or_object.read()
                size = len(buffer)
            else:
                raise

        super().__init__(buffer, size, filename)

        if close:
            fname_or_object.close()

class StringInputBuffer(FullFileInputBuffer):

    def __init__(self, string, filename='<string>'):
        super().__init__(string, len(string), filename)


class InteractiveInputBuffer(InputBuffer):

    def __init__(self):
        super().__init__()
        self.file = sys.stdin.buffer
        self.buffer = bytearray()
        self.mark = 0

        def stepper():
            while True:
                yield self.file.read(1)

        self.stepper = stepper()
        self.mapping = lambda x: x

    def set_mapping(self, mapping):
        self.mapping = mapping

    def step(self):
        self.buffer.append(next(self.stepper))
        return self.mapping(self.buffer[-1])

    def mark(self):
        self.mark = len(self.buffer)

    def discard(self):
        self.extract()

    def extract(self):

        def stepper():
            for b in self.buffer:
                yield b
            while True:
                yield self.file.read(1)

        res = bytes(self.buffer[:self.mark])
        self.buffer = self.buffer[self.mark:]
        self.stepper = stepper()
        return res, None

class InteractiveUnicodeInputBuffer(InputBuffer):

    def __init__(self):
        super().__init__()
        self.file = sys.stdin
        self.buffer = StringIO()
        self.mark = 0

    def extract(self):
        string = self.buffer.getvalue()
        self.buffer = StringIO(string[self.mark:])
        return string[:self.mark], None
