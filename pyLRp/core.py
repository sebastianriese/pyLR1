
import abc

class CantHappen(Exception):
    """
    Exception raised in code branches that should never be reached.
    """
    def __init__(self):
        super().__init__("""It seems you just found a bug

Please report this.""")

class AutoAccept(type):

    def __new__(cls, name, bases, dict):
        """
        Provide automagical VisitorBase and Accept generation with
        completeness checking for subclasses.
        """
        if 'Accept' not in dict:
            dict['Accept'] = cls._make_accept(name)

        # setup portable subclass tracking
        # XXX: maybe this should be weaklist
        # or ordered set
        dict['_subclasses_'] = []

        res = super().__new__(cls, name, bases, dict)

        for base in bases:
            if isinstance(base, AutoAccept):
                base._register_subclass(res)

        return res

    def _register_subclass(self, subclass):
        self._subclasses_.append(subclass)

    @staticmethod
    def _make_accept(name):
        visitor_name = "Visit" + name
        def accept(self, visitor):
            return getattr(visitor, visitor_name)(self)
        return accept

    @staticmethod
    def _make_visit():
        def visit(self, obj):
            pass
        return visit

    @staticmethod
    def _make_visit_any():
        def visit(self, obj):
            return obj.Accept(self)
        return visit

    def base_visitor(self):
        dict = {}
        for subclass in self._subclasses_:
            dict["Visit" + subclass.__name__] = abc.abstractmethod(self._make_visit())
        dict["Visit"] = self._make_visit_any()

        return abc.ABCMeta(self.__name__+"Visitor", (object,), dict)
