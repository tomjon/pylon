# -*- coding: utf-8 -*-

# PYthon LOgic eNgine (finding facts in second-order logic systems)
#
# Exists(x) s.t. W(x) and A(x, 'this')
#
# where W(x) iff x is a (real) word
#   and A(x, y) iff x is an anagram of y

# Second example:
#
# Exists(x) s.t. W(x) and A(x, y) and W(y)

# So a predicate impl will have to indicate what it's capable of doing, and some sort of score for how efficiently
# it can do it.

# A Predicate has to implement 2 iterators:
#   1. iterate your true/false (concrete) facts
#   2. evaluate P(x1), P(x2), ..
# For example a Predicate with Real domain might not be able to do (1), only (2) so for example, x > y
# (1), if used, happens before (2)

# TODO:
#
# 1. 'Difficulty' API
# 2a. On top of (1), stop doing iter_domain when it gets too difficult/too far, restart later
# 2b. Or instead of (1), pause doing iter_domain when it gets far enough, do eval() of rest of expr, restart later
# 3. Implement iter_domain(true/false only) [caches on the expr?]
#
# These might need or imply:
#
# 4. Global value cache (rather than per-expression) that you can then control (maybe)
# 5. Is shorting inside the iter_domain() loop correct?

#FIXME negative expression handling not currently very sensible
#FIXME __repr__ for negative expressions

import inspect
from collections import OrderedDict


class Sentinel:

    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return "@{0}".format(self.name)


# sentinels
_no_argument = Sentinel("No argument")
_free = Sentinel("Free")


class Variable:
    """ A variable that can be free or bound (free means is currently has no
        value, bound means it currently has a value).
    """

    def __init__(self):
        self.v = _free

    def __call__(self, v=_no_argument):
        if v is _no_argument:
          return self.v
        self.v = v

    def is_free(self):
      return self.v is _free

    def free(self):
      self.v = _free

    def __repr__(self):
        return "[%s]" % self.v if not self.is_free() else "[]"


class Predicate:
    """ A predicate is a truth function, which splits its domain into true and false
        parts (sets).
    
        Calling it, e.g. P(x), returns a PredicateExpr object, which is the actual
        object that does the hard work. This is so that we can use P(x) in an
        expression and still get back to the predicate.
        
        Here, x is a 'fact' - which is in fact any Python tuple, possibly containing
        free or bound Variables.
    """

    def __init__(self, name=None):
        self.name = name

    def __call__(self, *fact):
        return PredicateExpr(self, fact)

    def iter_domain(self, fact):
        yield True # if not overridden, indicates predicate can not enumerate domain, and passes the current fact along


class DomainError (Exception):

    def __init__(self, v):
        self.v = v

    def __str__(self):
        return "{0} is not in the domain".format(self.v)


class SetPredicate (Predicate):
    """ A predicate defined by a set of true/false values.
    """

    def __init__(self, values={}, name=None):
        Predicate.__init__(self)
        self.name = name
        items = [(k if isinstance(k, tuple) else (k,), v) for k, v in values.items()]
        self.values = OrderedDict(sorted(items, key=lambda t: t[0]))

    def set(self, key, value):
        self.values[key] = value

    def eval(self, z):
        value = self.values.get(z)
        if value is None:
            raise DomainError(z)
        return value

    def iter_domain(self, fact):
        # fact may contain Variables which must be enumerated over the domain
        for t in self.values:
            for x, v in zip(fact, t):
                if isinstance(x, Variable):
                    if x.is_free():
                        x(v)
                    elif x() != v:
                        break
                elif x != v:
                    break
            else:
                yield True
                continue
            yield False


class FnPredicate (Predicate):
    """ A predicate which defines truth based on a function of the arguments.
    """

    def __init__(self, f, name=None):
        self.f = f
        self.name = name

    def eval(self, z):
        return self.f(*z)


class Expr:
    """ Base class for expressions.
    """

    def __init__(self, name=None):
        self.negative = False
        # these are for diagnostics:
        self.collector = None
        self.name = name

    def __invert__(self):
        self.negative = not self.negative
        return self

    def __and__(self, f):
        return BinaryExpr(True, self, f)

    def __or__(self, f):
        return BinaryExpr(False, self, f)

    def __bool__(self):
        return self.eval()

    def collect(self, collector):
        self.collector = collector
        return self

    def __repr__(self):
        if self.name is not None:
            return self.name
        return "{0}@{1}".format(self.__class__.__name__, id(self))


class PredicateExpr (Expr):
    """ A predicate expression, created by calling a predicate, for instance P(x).
    
        >>> P = SetPredicate({ "foo": True, "bar": False })
        >>> bool(P("baz"))
        Traceback (most recent call last):
         ...
        DomainError: ('baz',) is not in the domain
        >>> bool(P("foo"))
        True
        >>> bool(P("bar"))
        False

        Boolean operations are supported:
        >>> bool(~P("foo"))
        False
        >>> bool(~P("bar"))
        True
        >>> bool(P("foo") | P("bar"))
        True
        >>> bool(~(P("foo") | P("bar")))
        False
        >>> bool(P("foo") & ~P("bar"))
        True
        >>> bool(~P("foo") & ~P("bar"))
        False
    """

    def __init__(self, p, fact):
        super().__init__(p.name)
        self.p = p # the Predicate
        self.fact = fact
        self.values = {}

    def eval(self):
        z = tuple(x() if isinstance(x, Variable) else x for x in self.fact)
        cached = z in self.values
        if cached:
            v = self.values[z]
        else:
            v = self.p.eval(z)
            self.values[z] = v
        if self.collector is not None:
            self.collector.eval(self, z, v, cached)
        return self.negative ^ v

    def iter_domain(self):
        f = tuple(x for x in self.fact if isinstance(x, Variable) and x.is_free())
        for v in self.p.iter_domain(self.fact):
            if v is True:
                if self.collector is not None:
                    self.collector.domain(self, self.fact)
                yield
            for x in f:
                x.free()

    def is_free(self):
        for x in self.fact:
            if isinstance(x, Variable) and x.is_free():
                return True
        return False


class BinaryExpr (Expr):

    def __init__(self, op, e, f):
        super().__init__()
        self.op = op # True for AND, False for OR
        self.e = e
        self.f = f

    def iter_domain(self):
        """ Short circuiting.
        
            >>> P = SetPredicate({'foo': True, 'bar': False}, name="P")
            >>> Q = SetPredicate({'A': True, 'B': True}, name="Q")
            >>> debug(Exists(lambda x, y: P(x) & Q(y), name="E"))
            ([bar]) in P
            P(bar) = False
            ([foo]) in P
            P(foo) = True
            ([A]) in Q
            P(foo) = True [cached]
            Q(A) = True
            E => ('foo', 'A')
            ([B]) in Q
            P(foo) = True [cached]
            Q(B) = True
            E => ('foo', 'B')
            Evaluates to True
        """
        #FIXME should choose the order based on difficulties and cope with NOPE
        for _ in self.e.iter_domain():
            if not self.e.is_free():
                v = self.e.eval()
                if self.short(v):
                    continue
            for __ in self.f.iter_domain():
                yield
        # iter each expression, keeping step with domain value 'difficulties'
        # to this end, iter_domain implementations can yield a 'difficulty' value, None meaning 'trivial'
        # ??? we will cache the domains here, on the stack
        #e_v, f_v = None, None
        #while True:
        #    for e_v in self.e.iter_domain():
        #        if e_v is not None and (f_v is None or e_v > f_v):
        #            break

    def is_free(self):
        return self.e.is_free() or self.f.is_free()

    def eval(self):
        if self.op:
            return self.e.eval() and self.f.eval() # we should check for 'difficulty' here
        else:
            return self.e.eval() or self.f.eval() # we should check for 'difficulty' here

    def short(self, v):
        return self.op ^ v

    def __invert__(self):
        self.negative = not self.negative # actually, this is ignored
        # operate De Morgan's law
        self.op = not self.op
        self.e = ~self.e
        self.f = ~self.f
        return self

    def collect(self, collector):
        super().collect(collector)
        self.e.collect(collector)
        self.f.collect(collector)


class Rule:
    """ Truth function for defining a predicate in terms of an expression:
        >>> Q = SetPredicate({ (1, 2): True, (3, 4): False, (1, 1): False, (2, 1): False })
        >>> R = Rule(lambda x: Q(1, x))
        >>> bool(R(2))
        True
        >>> bool(R(1))
        False
        >>> bool(R(1) | R(2))
        True
        >>> S = Rule(lambda x, y: Q(x, y) | Q(y, x))
        >>> bool(S(1, 2))
        True
        >>> bool(S(2, 1))
        True
        >>> bool(S(2, 1) & S(1, 2))
        True
        >>> bool(S(3, 4))
        Traceback (most recent call last):
         ...
        DomainError: (4, 3) is not in the domain
        >>> bool(~S(1, 2))
        False
    """

    def __init__(self, f):
        self.f = f

    def __call__(self, *fact):
        return RuleExpr(self.f(*fact))


class RuleExpr (Expr):

    def __init__(self, expr):
        super().__init__()
        self.expr = expr

    def eval(self):
        return self.negative ^ self.expr.eval()

    def iter_domain(self):
        return
        yield

    def collect(self, collector):
        super().collect(collector)
        self.expr.collect(collector)

    def is_free(self):
        return self.expr.is_free()

    def __repr__(self):
        return "[Rule:%s]" % repr(self.fact)


class Quantifier (Expr):
    """ For example:
    
        >>> P = SetPredicate({ "A": True, "B": True }, name="P")
        >>> debug(Exists(lambda x: P(x), name="E"))
        ([A]) in P
        P(A) = True
        E => ('A',)
        ([B]) in P
        P(B) = True
        E => ('B',)
        Evaluates to True

        Caching needs to be mindful of variables from outside the lambda:
    
        >>> Q = SetPredicate({ "a": True, "b": True }, name="Q")
        >>> debug(Exists(lambda x: Exists(lambda y: P(x) & Q(y), name="Inner"), name="Outer"))
        ([A]) in P
        P(A) = True
        ([a]) in Q
        P(A) = True [cached]
        Q(a) = True
        Inner => ('a',)
        Outer => ('A',)
        ([b]) in Q
        P(A) = True [cached]
        Q(b) = True
        Inner => ('b',)
        Outer => ('A',)
        ([B]) in P
        P(B) = True
        ([a]) in Q
        P(B) = True [cached]
        Q(a) = True [cached]
        Inner => ('a',)
        Outer => ('B',)
        ([b]) in Q
        P(B) = True [cached]
        Q(b) = True [cached]
        Inner => ('b',)
        Outer => ('B',)
        Evaluates to True
    """

    def __init__(self, f, op, name):
        super().__init__()
        self.fact = tuple(Variable() for _ in range(len(inspect.getargspec(f).args)))
        self.expr = f(*self.fact)
        self.op = op
        self.values = {}
        self.name = name

    def eval(self):
        z = tuple(x() if isinstance(x, Variable) else x for x in self.fact)
        if z in self.values:
            v = self.values[z]
        else:
            v = self._eval()
        return self.negative ^ v

    def _eval(self):
        v = not self.op
        for x in self.iter_domain():
            v = self.op
            if self.collector is None or self.collector.quantifier_short():
                break
        return v

    def iter_domain(self):
        for _ in self.expr.iter_domain():
            if not self.op ^ self.expr.eval(): # xor
                z = tuple(x() if isinstance(x, Variable) else x for x in self.fact)
                self.values[z] = self.op
                if self.collector is not None:
                    self.collector.quantifier_value(self, z)
                yield z

    def collect(self, collector):
        super().collect(collector)
        self.expr.collect(collector)


class Exists (Quantifier):
    """ Existence quantifier "there exists".
        >>> Q = SetPredicate({ (1, 2): True, (3, 4): False, (1, 1): True, (2, 1): True, (2, 2): True }, name="Q")
        >>> bool(Exists(lambda x: Q(x, 2)))
        True
        >>> bool(Exists(lambda x: Q(x, 6)))
        False
        >>> bool(Exists(lambda x: Q(3, x)))
        False
        >>> debug(Exists(lambda x: Q(x, x), name="E"))
        ([1],[1]) in Q
        Q(1,1) = True
        E => (1,)
        ([2],[2]) in Q
        Q(2,2) = True
        E => (2,)
        Evaluates to True
        >>> debug(Exists(lambda x, y: Q(x, x) & Q(x, y), name="E"))
        ([1],[1]) in Q
        Q(1,1) = True
        ([1],[1]) in Q
        Q(1,1) = True [cached]
        Q(1,1) = True
        E => (1, 1)
        ([1],[2]) in Q
        Q(1,1) = True [cached]
        Q(1,2) = True
        E => (1, 2)
        ([2],[2]) in Q
        Q(2,2) = True
        ([2],[1]) in Q
        Q(2,2) = True [cached]
        Q(2,1) = True
        E => (2, 1)
        ([2],[2]) in Q
        Q(2,2) = True [cached]
        Q(2,2) = True
        E => (2, 2)
        Evaluates to True
        >>> debug(Exists(lambda x, y: Q(x, y) & Q(y, x), name="E")) #FIMXE is caching working as expected, below?
        ([1],[1]) in Q
        Q(1,1) = True
        ([1],[1]) in Q
        Q(1,1) = True [cached]
        Q(1,1) = True
        E => (1, 1)
        ([1],[2]) in Q
        Q(1,2) = True
        ([2],[1]) in Q
        Q(1,2) = True [cached]
        Q(2,1) = True
        E => (1, 2)
        ([2],[1]) in Q
        Q(2,1) = True
        ([1],[2]) in Q
        Q(2,1) = True [cached]
        Q(1,2) = True
        E => (2, 1)
        ([2],[2]) in Q
        Q(2,2) = True
        ([2],[2]) in Q
        Q(2,2) = True [cached]
        Q(2,2) = True
        E => (2, 2)
        ([3],[4]) in Q
        Q(3,4) = False
        Evaluates to True
        >>> bool(Exists(lambda x: ~Q(9, x)))
        False
        >>> debug(Exists(lambda x: ~Q(3, x), name="E"))
        (3,[4]) in Q
        Q(3,4) = False
        E => (4,)
        Evaluates to True
        >>> bool(Exists(lambda x: Q(x, 2)) & ~Exists(lambda x: Q(x, 6)))
        True
        
        >>> R = SetPredicate({ (0, ): True, (1, ): True }, name="R")
        >>> debug(Exists(lambda x, y: R(x) & R(y), name="E"))
        ([0]) in R
        R(0) = True
        ([0]) in R
        R(0) = True [cached]
        R(0) = True
        E => (0, 0)
        ([1]) in R
        R(0) = True [cached]
        R(1) = True
        E => (0, 1)
        ([1]) in R
        R(1) = True
        ([0]) in R
        R(1) = True [cached]
        R(0) = True [cached]
        E => (1, 0)
        ([1]) in R
        R(1) = True [cached]
        R(1) = True [cached]
        E => (1, 1)
        Evaluates to True

        Predicates can refuse the iter_domain() call.
        >>> R = SetPredicate({ (4, ): True })
        >>> T = FnPredicate(lambda x, y: x < y)
        >>> bool(Exists(lambda x: R(x) & T(x, 5)))
        True
        >>> S = SetPredicate({ (7, ): True })
        >>> bool(Exists(lambda x, y: R(x) & T(x, y) & S(y)))
        True
        >>> bool(~Exists(lambda x, y: R(x) & T(x, y) & S(y)))
        False
    """
    def __init__(self, f, name=None):
        super().__init__(f, True, name)


class All (Quantifier):
    """ For All quantifier "for all".
        >>> Q = SetPredicate({ (1, 2): True, (3, 4): False, (1, 1): True, (2, 1): True, (2, 2): True })
        >>> bool(All(lambda x: Q(x, x)))
        True
        >>> bool(All(lambda x: Q(3, x)))
        False
        
        For All as Predicate.
        >>> P = SetPredicate({ (1, 2): True, (3, 4): True, (1, 1): True, (2, 1): True, (2, 2): True }, name="P")
        >>> debug(All(lambda x: All(lambda y: P(x, y), name="Inner"), name="Outer"))
        ([1],[1]) in P
        P(1,1) = True
        ([1],[2]) in P
        P(1,2) = True
        ([2],[1]) in P
        P(2,1) = True
        ([2],[2]) in P
        P(2,2) = True
        ([3],[4]) in P
        P(3,4) = True
        Evaluates to True
    """
    def __init__(self, f, name=None):
        super().__init__(f, False, name)


class Collector:

    def __init__(self, filter=None):
        self.filter = filter

    def eval(self, expr, z, v, cached):
        if self.filter is None or expr.name in self.filter:
            print("{0}({1}) = {2}{3}".format(expr, ','.join(str(x) for x in z), v, ' [cached]' if cached else ''))

    def domain(self, expr, fact):
        if self.filter is None or expr.name in self.filter:
            print("({1}) in {0}".format(expr, ','.join(str(x) for x in fact)))

    def quantifier_short(self):
        return False

    def quantifier_value(self, expr, x):
        if self.filter is None or expr.name in self.filter:
            print("{0} => {1}".format(expr, x))


def debug(expr, filter=None):
    c = Collector(filter)
    expr.collect(c)
    print("Evaluates to", bool(expr))


if __name__ == '__main__':
    import doctest
    doctest.testmod()

