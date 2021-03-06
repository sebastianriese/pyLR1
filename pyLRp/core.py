
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

        The base class of the hierarchy has to define the
        `_subclasses_` attribute as an empty list.
        """
        if 'accept' not in dict:
            dict['accept'] = cls._make_accept(name)

        res = super().__new__(cls, name, bases, dict)

        res._register_subclass_recurse(res, set())

        return res

    def _register_subclass(cls, subclass, marked):
        if hasattr(cls, '_subclasses_'):
            cls._subclasses_.append(subclass)
        else:
            cls._register_subclass_recurse(subclass, marked)

    def _register_subclass_recurse(cls, subclass, marked):
        marked.add(cls)
        for base in cls.__bases__:
            if isinstance(base, AutoAccept) and base not in marked:
                base._register_subclass(subclass, marked)

    @staticmethod
    def _make_accept(name):
        visitor_name = "visit_" + name
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
            return obj.accept(self)
        return visit

    def base_visitor(self):
        dict = {}
        for subclass in self._subclasses_:
            dict["visit_" + subclass.__name__] = \
                abc.abstractmethod(self._make_visit())
        dict["visit"] = self._make_visit_any()

        return abc.ABCMeta(self.__name__+"Visitor", (object,), dict)


class SingletonInitError(Exception):
    pass


class Singleton(type):

    def __new__(cls, name, bases, dict):
        dict['_instance_'] = None
        return super().__new__(cls, name, bases, dict)

    def configure(cls, *args, **kwargs):
        """
        Construct the singleton instance with the given arguments.

        If there alread is an instance an error is raised.
        """
        if cls._instance_ is not None:
            raise SingletonInitError("Cannot configure a singleton if"
                                     " there already is an instance")
        cls._instance_ = super().__call__(*args, **kwargs)

    def __call__(cls, *args, **kwargs):
        """
        Retrieve the singleton instance.

        If there is no instance create it with no arguments. If you
        supply arguments an error will be raised. If you want to
        configure your singleton class with arguments, then use the
        `configure` method of the singleton class like::

            MySingleton.configure(arg, barg, kwarg=spam)
        """
        if args or kwargs:
            raise SingletonInitError("When retrieving a singleton instance"
                                     " you must not supply arguments")

        if cls._instance_ is None:
            cls._instance_ = super().__call__()
