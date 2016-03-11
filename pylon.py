# -*- coding: utf-8 -*-

# PYthon LOgic eNgine (finding facts in second-order logic systems)
#
# Exists(x) s.t. W(x) and A(x, 'this')
#
# where W(x) iff x is a (real) word
#   and A(x, y) iff x is an anagram of y

# Solution: iterate True elements of the domain of A, and check W
# ??The domain of A is all words.?? If you have A(x,y) then y is an 'init parameter' of A(x)

# Second example (yeah not a very good one, but perhaps instructive):
#
# Exists(x) s.t. W(x) and A(x, y) and W(y)

# So a predicate impl will have to indicate what it's capable of doing, and some sort of score for how efficiently
# it can do it.

# A Predicate has to implement 3 iterators,
# for it will be asked, in order:
# [ 1. iterate your true/false (concrete) facts ]
#   2. iterate your domain
#   3. fine, you can't do either of those, so evaluate P(x1), P(x2), ..
# For example a Predicate with Real domain might not be able to do 1 or 2, just 3 by evaluating
# for example x > y

import inspect


class Sentinel:

    def __init__(self, name):
        self.name = name

    def __str__(self):
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

    def __init__(self):
        pass

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

    def __init__(self, values={}):
        Predicate.__init__(self)
        self.values = dict((k if isinstance(k, tuple) else (k,), v) for k, v in values.items())

    def set(self, key, value):
        self.values[key] = value

    def eval(self, z):
        #FIXME you might want a version of eval that returns None instead of raising, but haven't needed it yet
        #FIXME in fact, could rename this __bool__ ;)
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

    def __init__(self, f):
        self.f = f

    def eval(self, z):
        return self.f(*z)


class Expr:
    """ Root class for expression trees (formed by operators and predicates).
    """

    def __invert__(self):
        return NegExpr(self)

    def __and__(self, f):
        return AndExpr(self, f)

    def __or__(self, f):
        return OrExpr(self, f)

    def __bool__(self):
        return self.eval()


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
        self.p = p # the Predicate
        self.fact = fact

    def eval(self):
        z = tuple(x() if isinstance(x, Variable) else x for x in self.fact)
        return self.p.eval(z)

    def iter_domain(self):
        f = tuple(x for x in self.fact if isinstance(x, Variable) and x.is_free())
        for v in self.p.iter_domain(self.fact):
            if v:
                yield
            for x in f:
                x.free()

    def __repr__(self):
        return "[%s]" % repr(self.fact)


class NegExpr (Expr):

    def __init__(self, e):
        self.e = e

    def eval(self):
        return not self.e.eval()

    def iter_domain(self):
        for _ in self.e.iter_domain():
            yield

    def __repr__(self):
        return "~%s" % self.e


class BinaryExpr (Expr):

    def __init__(self, e, f, ops):
        self.e = e
        self.f = f
        self.ops = ops

    def iter_domain(self):
        #FIXME should choose the order based on difficulties and cope with NOPE
        for _ in self.e.iter_domain():
            #FIXME if self.e.fact now contains no free variables, we can evaluate it... store the evaluation on the expr itself?
            for __ in self.f.iter_domain():
                yield

    def __repr__(self):
        return "%s %s %s" % (self.e, self.ops, self.f)


class AndExpr (BinaryExpr):

    def __init__(self, e, f):
        BinaryExpr.__init__(self, e, f, "&")

    def eval(self):
        return self.e.eval() and self.f.eval() # we should check for 'difficulty' here


class OrExpr (BinaryExpr):

    def __init__(self, e, f):
        BinaryExpr.__init__(self, e, f, "|")

    def eval(self):
        return self.e.eval() or self.f.eval() # we should check for 'difficulty' here


class Rule:
    """ Truth function for defining a predicate as being 'iff' another:
        >>> Q = SetPredicate({ (1, 2): True, (3, 4): False, (1, 1): False, (2, 1): False })
        >>> R = Rule(lambda x: Q(1, x))   #FIXME not done! so the domain/truth iterators for R's function defer to Q's function: whats your domain with a fixed? (Q|a)
        >>> bool(R(2)) # what about lambda x, y: Q(y, 1, x)
        True
        >>> bool(R(1))
        False
        >>> bool(R(1) | R(2))
        True
        >>> S = Rule(lambda x, y: Q(x, y) | Q(y, x))
        >>> bool(S(2, 1))
        True
        >>> bool(S(3, 4))
        Traceback (most recent call last):
         ...
        DomainError: (4, 3) is not in the domain
    """

    def __init__(self, f):
        self.f = f

    def __call__(self, *fact):
        return RuleExpr(self.f(*fact))


class RuleExpr (Expr):

    def __init__(self, expr):
        self.expr = expr

    def eval(self):
        return self.expr.eval()

    def iter_domain(self):
        return
        yield

    def __repr__(self):
        return "[Rule:%s]" % repr(self.fact)


class Quantifier (Expr):

    def __init__(self, f, value):
        self.f = f
        self.value = value

    def eval(self):
        for x in iter(self):
            return self.value
        return not self.value

    def __iter__(self):
        v = tuple(Variable() for _ in range(len(inspect.getargspec(self.f).args)))
        expr = self.f(*v)
        for _ in expr.iter_domain():
            if not self.value ^ expr.eval(): # xor
                yield tuple(x() if isinstance(x, Variable) else x for x in v)


class Exists (Quantifier):
    """ Existence quantifier "there exists".
        >>> Q = SetPredicate({ (1, 2): True, (3, 4): False, (1, 1): True, (2, 1): True, (2, 2): True })
        >>> bool(Exists(lambda x: Q(x, 2)))
        True
        >>> bool(Exists(lambda x: Q(x, 6)))
        False
        >>> bool(Exists(lambda x: Q(3, x)))
        False
        >>> for fact in Exists(lambda x: Q(x, x)): print(fact)
        (1,)
        (2,)
        >>> for fact in Exists(lambda x, y: Q(x, x) & Q(x, y)): print(fact)
        (1, 2)
        (1, 1)
        (2, 1)
        (2, 2)
        >>> for fact in Exists(lambda x, y: Q(x, y) & Q(y, x)): print(fact)
        (1, 2)
        (1, 1)
        (2, 1)
        (2, 2)
        >>> bool(Exists(lambda x: ~Q(9, x)))
        False
        >>> for fact in Exists(lambda x: ~Q(3, x)): print(fact)
        (4,)
        >>> bool(Exists(lambda x: Q(x, 2)) & ~Exists(lambda x: Q(x, 6)))
        True
        
        >>> R = SetPredicate({ (0, ): True, (1, ): True })
        >>> for fact in Exists(lambda x, y: R(x) & R(y)): print(fact)
        (0, 0)
        (0, 1)
        (1, 0)
        (1, 1)
        
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
    def __init__(self, f):
        super().__init__(f, True)


class All (Quantifier):
    """ For All quantifier "for all".
        >>> Q = SetPredicate({ (1, 2): True, (3, 4): False, (1, 1): True, (2, 1): True, (2, 2): True })
        >>> bool(All(lambda x: Q(x, x)))
        True
        >>> bool(All(lambda x: Q(3, x)))
        False
    """
    def __init__(self, f):
        super().__init__(f, False)


if __name__ == '__main__':
    import doctest
    doctest.testmod()

