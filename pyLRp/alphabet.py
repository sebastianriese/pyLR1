
from .core import Singleton
from abc import ABCMeta, abstractmethod, abstractproperty

class Alphabet(metaclass=ABCMeta):

    @abstractmethod
    def __len__(self):
        return 0

    @abstractmethod
    def __getitem__(self, index):
        raise NotImplementedError

    @abstractmethod
    def __iter__(self):
        raise StopIteration

class Epsilon(metaclass=Singleton):
    pass

class ByteAlphabet(Alphabet):

    def __len__(self):
        return 256

    def __iter__(self):
        for i in range(0, 256):
            yield chr(i)

    def __getitem__(self, index):
        if 0 <= index < 256:
            return chr(index)
        else:
            raise IndexError
