
from .core import Singleton
from abc import ABCMeta, abstractmethod, abstractproperty

class Alphabet(metaclass=ABCMeta):

    @abstractmethod
    def __len__(self):
        return 0

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
