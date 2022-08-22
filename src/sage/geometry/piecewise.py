# coding=utf-8
from sage.rings.polynomial.polynomial_element import Polynomial, is_Polynomial
from sage.sets.real_set import InternalRealInterval, RealSet
from collections import defaultdict
from heapq import merge
import bisect

class PiecewiseFunction:
    def __init__(self, function_pieces):
        """
        Piecewise polynomial

        EXAMPLES::

            sage: R.<t> = QQ[]
            sage: f1 = 1 - t
            sage: f2 = t^4 - t^2
            sage: D1 = RealSet([0, 1], [4, 5])
            sage: D2 = RealSet([2, 3], [6, 7])
            sage: p = piecewise([[D1, f1], [D2, f2]]); p
            piecewise(t |--> -t + 1 on [0, 1] ∪ [4, 5], t |--> t^4 - t^2 on [2, 3] ∪ [6, 7]; t)
        """
        self.domain_list = []
        self.func_list = []
        self.var = None
        input_func_type = None
        p = {}
        for i, (domain, func) in enumerate(function_pieces):
            if not isinstance(domain, RealSet):
                try:
                    domain = RealSet(domain)
                except:
                    raise ValueError(
                        "Invalid domain. Should be transformed to RealSet, but got {domain_type} for {domain_value}.".format(
                            domain_type=type(domain), domain_value=domain))
            if domain.is_empty():
                continue
            if not is_Polynomial(func):
                raise ValueError("Invalid func. Should be type Polynomial, got {func_type} for {func_value}.".format(
                    func_type=type(func), func_value=func))
            if input_func_type is None:
                input_func_type = type(func)
            elif type(func) != input_func_type:
                raise ValueError("Inconsistant function types. Should be {first_type}, got {curr_type}".format(
                    first_type=input_func_type, curr_type=type(func)))
            if self.var is None:
                self.var = func.args()[0]
            elif func.args()[0] != self.var:
                raise ValueError("Inconsistant variable. Should be {0}, got {1}".format(self.var, func.args()[0]))

            non_point = []
            for interval in domain:
                if interval.is_point():
                    value = func(interval._lower)
                    # this value could not be Integer or Rational
                    # this could be LazyWrapper
                    if hasattr(value, "_value"):
                        value = value._value
                    func_ = value + 0*func
                    if func_ in p:
                        i = p[func_]
                        self.domain_list[i] = self.domain_list[i].union(interval)
                    else:
                        self.domain_list.append(RealSet(interval))
                        self.func_list.append(func_)
                        p[func_] = len(self.domain_list) - 1
                else:
                    non_point.append(interval)

            if non_point:
                if func in p:
                    i = p[func]
                    self.domain_list[i] = RealSet.union_of_realsets(*([self.domain_list[i]] + non_point))
                else:
                    self.domain_list.append(RealSet.union_of_realsets(*non_point))
                    self.func_list.append(func)
                    p[func] = len(self.domain_list) - 1

        del p
        if not RealSet.are_pairwise_disjoint(*self.domain_list):
            raise ValueError("Invalid domain. Should be mutually disjoint.")

        self.support = RealSet.union_of_realsets(*self.domain_list)
        self._end_points = None
        self._end_points_list = None


    def _init_end_points(self):
        self._end_points = {}
        # [(x, epsilon), delta, i]
        self._end_points_list = [self._iterator(real_set, i) for i, real_set in enumerate(self.domain_list)]
        self._end_points_list = list(merge(*self._end_points_list))
        for i, (dom, func) in enumerate(zip(self.domain_list, self.func_list)):
            for (x, epsilon), delta in dom._scan():
                if x not in self._end_points: self._end_points[x] = [None, [None, None]]
                func_val = func(x)
                # this delta is from RealSet._scan()
                if delta < 0:
                    self._end_points[x][1][1] = func_val
                    if epsilon == 0:
                        self._end_points[x][0] = func_val
                else:
                    self._end_points[x][1][0] = func_val
                    if epsilon == 1:
                        self._end_points[x][0] = func_val



    def __repr__(self):
        """
        Return a string representation

        OUTPUT:

        String.

        EXAMPLES::

            sage: R.<t> = QQ[]
            sage: f1 = 1 - t
            sage: D1 = RealSet([0, 1], [4, 5])
            sage: p = piecewise([[D1, f1]])
            sage: str(p)
            'piecewise(t |--> -t + 1 on [0, 1] ∪ [4, 5]; t)'
        """
        s = "piecewise("
        args = []
        for dom, func in zip(self.domain_list, self.func_list):
            args.append("{0} |--> {1} on {2}".format(self.var, func, dom))
        s += ", ".join(args) + '; {0})'.format(self.var)
        return s

    def __call__(self, *args, **kwds):
        r"""
        Piecewise functions

        INPUT:

        - ``function_pieces`` -- a list of pairs consisting of a
          domain and a symbolic function.

        - ``var=x`` -- a symbolic variable or ``None`` (default). The
        real variable in which the function is piecewise in.

        OUTPUT:

        A piecewise-defined function. A ``ValueError`` will be raised
        if the domains of the pieces are not pairwise disjoint.

        EXAMPLES::
            sage: R.<t> = QQ[]
            sage: my_abs = piecewise([((-1, 0), -t), ([0, 1], t)]);  my_abs
            piecewise(t|-->-t on (-1, 0), x|-->t on [0, 1]; t)
            sage: [ my_abs(i/5) for i in range(-4, 5)]
            [4/5, 3/5, 2/5, 1/5, 0, 1/5, 2/5, 3/5, 4/5]
        """
        val = None
        if len(args) == 1:
            val = args[0]
            if len(kwds) > 0:
                raise ValueError("Invalid input: Got more than 1 inputs")
        elif len(args) == 0:
            if str(self.var) in kwds:
                val = kwds[str(self.var)]
                if len(kwds) > 1:
                    print("Warning: more than one input detected, only {0}={1} used.".format(str(self.var), val))
            else:
                raise ValueError("Invalid input: No positional input for {0} detected.".format(str(self.var)))
        else:
            raise ValueError("Invalid input: More than 1 arguments detected.")

        for dom, func in zip(self.domain_list, self.func_list):
            if val in dom:
                return func(val)
        print("Warning: {0}={1} does not fall in any domain defined. Returned None type.".format(str(self.var), val))
        return None

    def __len__(self):
        """
        Return the number of "pieces"

        OUTPUT:

        Integer

        EXAMPLES::

            sage: f = piecewise([([0,0], sin(x)), ((0,2), cos(x))]);  f
            piecewise(x|-->sin(x) on {0}, x|-->cos(x) on (0, 2); x)
            sage: len(f)
            2
        """
        return len(self.func_list)

    def __iter__(self):
        """
        iter over piecewise function

        OUTPUT:

        domains and functions

        EXAMPLES::
            sage: R.<t> = QQ[]
            sage: f1 = 1 - t
            sage: f2 = t ^ 4 - t ^ 2
            sage: D1 = RealSet((-oo, 1), (4, 5))
            sage: D2 = RealSet([2, 3], x >= 6)
            sage: p = piecewise([[D1, f1], [D2, f2]])
            sage: for dom, func in p:
            ....:     print(dom, func)
            ....:
            (-oo, 1) ∪ (4, 5) -t + 1
            [2, 3] ∪ [6, +oo) t^4 - t^2
        """
        for dom, func in zip(self.domain_list, self.func_list):
            yield dom, func

    def __add__(self, other):
        """
        Add two identical domain piecewise function

        INPUT:

        - ``other`` -- Another piecewise function

        OUTPUT:

        A piecewise-defined function.

        EXAMPLES::

            sage: R.<t> = QQ[]
            sage: f1 = 1 - t
            sage: f2 = t^4 - t^2
            sage: f3 = t^2
            sage: f4 = 1-t^7
            sage: D1 = RealSet([0, 1], [4, 5])
            sage: D2 = RealSet([2, 3], [6, 7])
            sage: D3 = RealSet([0, 1], [4, 5])
            sage: D4 = RealSet([2, 3], [6, 7])
            sage: p = piecewise([[D1, f1], [D2, f2]])
            sage: q = piecewise([[D3, f3], [D4, f4]])
            sage: p+q
            piecewise(t |--> t^2 - t + 1 on [0, 1] ∪ [4, 5], t |--> -t^7 + t^4 - t^2 + 1 on [2, 3] ∪ [6, 7]; t)
        """
        if self.var != other.var:
            print("Invalid variables: Cannot add variable {0} with {1}".format(self.var, other.var))
            return None
        if type(other) == type(self):
            return self.piecewise_add(other)
        else:
            return PiecewiseFunction((dom, func + other) for dom, func in self.__iter__())

    __radd__ = __add__


    def __eq__(self, other):
        """
        Return if to piecewise functions are equal

        INPUT:

        - ``other`` -- Another piecewise function

        OUTPUT:

        Boolean

        EXAMPLES::
        sage: R.<t> = QQ[]
        sage: f1 = t
        sage: f2 = 2 - t
        sage: f3 = t
        sage: f4 = 2 - t
        sage: D1 = RealSet([0, 1])
        sage: D2 = RealSet((1, 2))
        sage: D3 = RealSet(RealSet.closed_open(0, 1))
        sage: D4 = RealSet(RealSet.closed_open(1, 2))
        sage: p = piecewise([[D1, f1], [D2, f2]]); p
        piecewise(t |--> t on [0, 1], t |--> -t + 2 on (1, 2); t)
        sage: q = piecewise([[D3, f3], [D4, f4]]); q
        piecewise(t |--> t on [0, 1), t |--> -t + 2 on [1, 2); t)
        sage: p==q
        True
        """

        if self.support != other.support or self.var != other.var or any(func != 0 * self.func_list[0] for _, func in (self - other)):
            return False
        return True

    def __neg__(self):
        """
        Return the negative of functions

        OUTPUT:

        A piecewise-defined function.

        EXAMPLES::

            sage: R.<t> = QQ[]
            sage: f1 = t
            sage: f2 = 2 - t
            sage: D1 = RealSet([0, 1])
            sage: D2 = RealSet((1, 2))
            sage: p = piecewise([[D1, f1], [D2, f2]]); p
            piecewise(t |--> t on [0, 1], t |--> -t + 2 on (1, 2); t)
            sage: -p
            piecewise(t |--> -t on [0, 1], t |--> t - 2 on (1, 2); t)
        """

        return PiecewiseFunction((dom, -func) for dom, func in self.__iter__())

    def __sub__(self, other):
        """
        Subtraction another identical domain's piecewise function

        INPUT:

        - ``other`` -- Another piecewise function

        OUTPUT:

        A piecewise-defined function.

        EXAMPLES::

            sage: R.<t> = QQ[]
            sage: f1 = 1 - t
            sage: f2 = t^4 - t^2
            sage: f3 = t^2
            sage: f4 = 1-t^7
            sage: D1 = RealSet([0, 1], [4, 5])
            sage: D2 = RealSet([2, 3], [6, 7])
            sage: D3 = RealSet([0, 1], [4, 5])
            sage: D4 = RealSet([2, 3], [6, 7])
            sage: p = piecewise([[D1, f1], [D2, f2]]); p
            piecewise(t |--> -t + 1 on [0, 1] ∪ [4, 5], t |--> t^4 - t^2 on [2, 3] ∪ [6, 7]; t)
            sage: q = piecewise([[D3, f3], [D4, f4]]); q
            piecewise(t |--> t^2 on [0, 1] ∪ [4, 5], t |--> -t^7 + 1 on [2, 3] ∪ [6, 7]; t)
            sage: p-q
            piecewise(t |--> -t^2 - t + 1 on [0, 1] ∪ [4, 5], t |--> t^7 + t^4 - t^2 - 1 on [2, 3] ∪ [6, 7]; t)
        """
        return self.__add__(other.__neg__())

    def __rsub__(self, other):
        return other.__add__(self.__neg__())

    def __mul__(self, other):
        r"""
        multiply two identical domain piecewise function

        INPUT:

        - ``other`` -- Another piecewise function

        OUTPUT:

        A piecewise-defined function.

        EXAMPLES::

            sage: R.<t> = QQ[]
            sage: f1 = 1 - t
            sage: f2 = t^4 - t^2
            sage: f3 = t^2
            sage: f4 = 1-t^7
            sage: D1 = RealSet([0, 1], [4, 5])
            sage: D2 = RealSet([2, 3], [6, 7])
            sage: D3 = RealSet([0, 1], [4, 5])
            sage: D4 = RealSet([2, 3], [6, 7])
            sage: p = piecewise([[D1, f1], [D2, f2]]); p
            piecewise(t |--> -t + 1 on [0, 1] ∪ [4, 5], t |--> t^4 - t^2 on [2, 3] ∪ [6, 7]; t)
            sage: q = piecewise([[D3, f3], [D4, f4]]); q
            piecewise(t |--> t^2 on [0, 1] ∪ [4, 5], t |--> -t^7 + 1 on [2, 3] ∪ [6, 7]; t)
            sage: p*q
            piecewise(t |--> -t^3 + t^2 on [0, 1] ∪ [4, 5], t |--> -t^11 + t^9 + t^4 - t^2 on [2, 3] ∪ [6, 7]; t)
        """
        if self.var != other.var:
            print("Invalid variables: Cannot add variable {0} with {1}".format(self.var, other.var))
            return None
        if type(other) == type(self):
            return self.piecewise_mul(other)
        else:
            return PiecewiseFunction((dom, func * other) for dom, func in self.__iter__())

    __rmul__ = __mul__

    # Other should be a number
    def __truediv__(self, other):
        """
        Divide by a scalar.

        INPUT:

        - ``other``: scalar

        OUTPUT:

        A piecewise-defined function.

        EXAMPLES::

            sage: R.<t> = QQ[]
            sage: f1 = 1 - t
            sage: f2 = t^4 - t^2
            sage: f3 = t^2
            sage: f4 = 1-t^7
            sage: D1 = RealSet([0, 1], [4, 5])
            sage: D2 = RealSet([2, 3], [6, 7])
            sage: D3 = RealSet([0, 1], [4, 5])
            sage: D4 = RealSet([2, 3], [6, 7])
            sage: p = piecewise([[D1, f1], [D2, f2]]); p
            piecewise(t |--> -t + 1 on [0, 1] ∪ [4, 5], t |--> t^4 - t^2 on [2, 3] ∪ [6, 7]; t)
            sage: p/2
            piecewise(t |--> -1/2*t + 1/2 on [0, 1] ∪ [4, 5], t |--> 1/2*t^4 - 1/2*t^2 on [2, 3] ∪ [6, 7]; t)
        """
        return PiecewiseFunction((dom, func / other) for dom, func in self.__iter__())

    def __pow__(self, power):

        """
        Power of piecewise function

        INPUT:

        - ``power``: scalar

        OUTPUT:

        A piecewise-defined function.

        EXAMPLES::

            sage: R.<t> = QQ[]
            sage: f1 = 1 - t
            sage: f2 = t^4 - t^2
            sage: f3 = t^2
            sage: f4 = 1-t^7
            sage: D1 = RealSet([0, 1], [4, 5])
            sage: D2 = RealSet([2, 3], [6, 7])
            sage: D3 = RealSet([0, 1], [4, 5])
            sage: D4 = RealSet([2, 3], [6, 7])
            sage: p = piecewise([[D1, f1], [D2, f2]]); p
            piecewise(t |--> -t + 1 on [0, 1] ∪ [4, 5], t |--> t^4 - t^2 on [2, 3] ∪ [6, 7]; t)
            sage: p^2
            piecewise(t |--> t^2 - 2*t + 1 on [0, 1] ∪ [4, 5], t |--> t^8 - 2*t^6 + t^4 on [2, 3] ∪ [6, 7]; t)
        """
        return PiecewiseFunction((dom, func ** power) for dom, func in self.__iter__())




    @staticmethod
    def _iterator(realset, i):
        """
        scan function for scan-line

        INPUT:

        - ``realset`` -- A collection of realsets
        - ``i`` -- integer

        OUTPUT:

        -  Generate events of the form ``((x, epsilon), delta), i``

        When ``x`` is the beginning of an interval ('on'):

        - ``epsilon`` is 0 if the interval is lower closed and 1 otherwise,
        - ``delta`` is 1

        When ``x`` is the end of an interval ('off'):

        - ``epsilon`` is 1 if the interval is upper closed and 0 otherwise,
        - ``delta`` is -1

        EXAMPLES::

            sage: D1 = RealSet([0, 2], [3, 5])
            sage: list(piecewise._iterator(D1, None))
            [(((0, 0), 1), None),
             (((2, 1), -1), None),
             (((3, 0), 1), None),
             (((5, 1), -1), None)]


        """
        for interval in realset:
            yield ((interval._lower, 1 - int(interval._lower_closed)), 1), i
            yield ((interval._upper, int(interval._upper_closed)), -1), i

    @staticmethod
    def finest_partitions(*real_set_collection):
        """
        Return the finest partitions

        INPUT:

        - ``*real_set_collection`` -- a list/tuple/iterable of :class:`RealSet`
          or data that defines one.

        OUTPUT:

        iterator of interval and index of interval

        EXAMPLES::
        sage: D1 = RealSet([0, 1], [4, 5])
        sage: D2 = RealSet([2, 3], [6, 7])
        sage: D3 = RealSet([0, 1], [4, 5])
        sage: D4 = RealSet([2, 3], [6, 7])
        sage: list( piecewise.finest_partitions(D1,D2,D3,D4))
        [([0, 1], (1, 0, 1, 0)),
         ([2, 3], (0, 1, 0, 1)),
         ([4, 5], (1, 0, 1, 0)),
         ([6, 7], (0, 1, 0, 1))]
        """
        scan = [PiecewiseFunction._iterator(real_set, i) for i, real_set in enumerate(real_set_collection)]
        indicator = [0] * len(scan)
        indicator_sum = 0
        scan = merge(*scan)
        prev_event = None

        for event, set_id in scan:
            (x, epsilon), delta = event
            if prev_event and event > prev_event:
                (x_, epsilon_), _ = prev_event
                yield RealSet(InternalRealInterval(x_, epsilon_ == 0, x, epsilon == 1)), tuple(indicator)
            indicator[set_id] += delta
            indicator_sum += delta

            prev_event = (x, epsilon), 1
            if indicator_sum == 0:
                prev_event = None

    def piecewise_add(self, other):
        r"""
        Add two identical domain piecewise function

        INPUT:

        - ``other`` -- Another piecewise function

        OUTPUT:

        A piecewise-defined function.

        EXAMPLES::

            sage: R.<t> = QQ[]
            sage: f1 = 1 - t
            sage: f2 = t^4 - t^2
            sage: f3 = t^2
            sage: f4 = 1-t^7
            sage: D1 = RealSet([0, 1], [4, 5])
            sage: D2 = RealSet([2, 3], [6, 7])
            sage: D3 = RealSet([0, 1], [4, 5])
            sage: D4 = RealSet([2, 3], [6, 7])
            sage: p = piecewise([[D1, f1], [D2, f2]])
            sage: q = piecewise([[D3, f3], [D4, f4]])
            sage: p.piecewise_add(q)
            piecewise(t |--> t^2 - t + 1 on [0, 1] ∪ [4, 5], t |--> -t^7 + t^4 - t^2 + 1 on [2, 3] ∪ [6, 7]; t)
        """

        if self.support != other.support:
            raise ValueError("Inconsistent domains. For union add or intersection add, please use piecewise_add_general")

        return self.piecewise_add_general(other, True)

    def piecewise_add_general(self, other, union=True):
        r"""
        Add two different domains piecewise function

        INPUT:

        - ``other`` -- Another piecewise function
        - ``union `` -- Boolean, if True, take union of two domain and add, False: add two function intersection part

        OUTPUT:

        A piecewise-defined function.

        EXAMPLES::

            sage: R.<t> = QQ[]
            sage: f1 = 1 - t
            sage: f2 = t^4 - t^2
            sage: f3 = t^2
            sage: f4 = 1-t^7
            sage: D1 = RealSet([0, 1], [4, 5])
            sage: D2 = RealSet([2, 3], [6, 7])
            sage: D3 = RealSet([-1, 0], [4, 5])
            sage: D4 = RealSet([2, 3], [7, 8])
            sage: p = piecewise([[D1, f1], [D2, f2]])
            sage: q = piecewise([[D3, f3], [D4, f4]])
            sage: p.piecewise_add_general(q, True)
            piecewise(t |--> t^2 on [-1, 0), t |--> t^2 - t + 1 on {0} ∪ [4, 5], t |--> -t + 1 on (0, 1], t |--> -t^7 + t^4 - t^2 + 1 on [2, 3] ∪ {7}, t |--> -t^7 + 1 on (7, 8], t |--> t^4 - t^2 on [6, 7); t)
            sage: p.piecewise_add_general(q, False)
            piecewise(t |--> t^2 - t + 1 on {0} ∪ [4, 5], t |--> -t^7 + t^4 - t^2 + 1 on [2, 3] ∪ {7}; t)
        """

        n_self = len(self.domain_list)
        result_pairs = []
        p = self.finest_partitions(*self.domain_list, *other.domain_list)
        for real_set, inds in p:
            new_pair = [real_set, 0]
            if not union and sum(inds) < 2: continue
            # i - index for realset, ind: True or False
            for i, ind in enumerate(inds):
                if ind > 0:
                    new_pair[1] += self.func_list[i] if i < n_self else other.func_list[i-n_self]
            result_pairs.append(new_pair)

        return PiecewiseFunction(result_pairs)

    @staticmethod
    def piecewise_sum_general(piecewise_collection, union=True):
        # R.<t> = QQ[]
        # p1 = piecewise([[[0, 2], t], [[3, 5], t^2], [[6, 7], 1 - t]])
        # p2 = piecewise([[(1, 4), t^3-t^2], [[5, 6], t], [[7, 7], -t]])
        # p3 = piecewise([[RealSet.closed_open(1, 2), (t+1)^2], [(3, +oo), (t+2)^3]])
        # p1.piecewise_sum_general([p1, p2, p3], True)
        # p1.piecewise_sum_general([p1, p2, p3], False)

        realset_cut = [0]
        for piecewise in piecewise_collection:
            realset_cut.append(len(piecewise) + realset_cut[-1])

        def get_realset_func_id(i):
            realset_id = bisect.bisect_right(realset_cut, i) - 1
            return realset_id, i - realset_cut[realset_id]

        result_pairs = []
        p = PiecewiseFunction.finest_partitions(*[dom for piecewise in piecewise_collection for dom, _ in piecewise])
        for real_set, inds in p:
            new_pair = [real_set, 0]
            if not union and sum(inds) < len(realset_cut)-1: continue
            # i - index for realset, ind: True or False
            for i, ind in enumerate(inds):
                if ind > 0:
                    realset_id, func_id = get_realset_func_id(i)
                    new_pair[1] += piecewise_collection[realset_id].func_list[func_id]
            result_pairs.append(new_pair)

        return PiecewiseFunction(result_pairs)

    def piecewise_mul(self, other):
        r"""
        multiply two identical domain piecewise function

        INPUT:

        - ``other`` -- Another piecewise function

        OUTPUT:

        A piecewise-defined function.

        EXAMPLES::

            sage: R.<t> = QQ[]
            sage: f1 = 1 - t
            sage: f2 = t^4 - t^2
            sage: f3 = t^2
            sage: f4 = 1-t^7
            sage: D1 = RealSet([0, 1], [4, 5])
            sage: D2 = RealSet([2, 3], [6, 7])
            sage: D3 = RealSet([0, 1], [4, 5])
            sage: D4 = RealSet([2, 3], [6, 7])
            sage: p = piecewise([[D1, f1], [D2, f2]])
            sage: q = piecewise([[D3, f3], [D4, f4]])
            sage: p.piecewise_mul(q)
            piecewise(t |--> -t^3 + t^2 on [0, 1] ∪ [4, 5], t |--> -t^11 + t^9 + t^4 - t^2 on [2, 3] ∪ [6, 7]; t)
            sage: D5 = RealSet([2, 3], [7, 8])
            sage: f = piecewise([[D3, f3], [D5, f4]])
            sage: p.piecewise_mul(f)
            ValueError: Inconsistent domains. For union multiplication or intersection multiplication, please use piecewise_mul_general
        """

        if self.support != other.support:
            raise ValueError("Inconsistent domains. For union multiplication or intersection multiplication, please use piecewise_mul_general")

        return self.piecewise_mul_general(other, union=True)

    def piecewise_mul_general(self, other, union=True):
        r"""
        multiply two different domains piecewise function

        INPUT:

        - ``other`` -- Another piecewise function
        - ``union `` -- Boolean, if True, take union of two domain the multiply, False: multiply two function intersection part

        OUTPUT:

        A piecewise-defined function.

        EXAMPLES::

            sage:R.<t> = QQ[]
            sage: f1 = 1 - t
            sage: f2 = t^4 - t^2
            sage: f3 = t^2
            sage: f4 = 1-t^7
            sage: D1 = RealSet([0, 1])
            sage: D2 = RealSet([2, 3])
            sage: D3 = RealSet([2, 3])
            sage: D4 = RealSet([7, 8])
            sage: p = piecewise([[D1, f1], [D2, f2]])
            sage: q = piecewise([[D3, f3], [D4, f4]])
            sage: p.piecewise_mul_general(q, True)
            piecewise(t |--> -t + 1 on [0, 1], t |--> t^6 - t^4 on [2, 3], t |--> -t^7 + 1 on [7, 8]; t)
            sage: p.piecewise_mul_general(q, False)
            piecewise(t |--> t^6 - t^4 on [2, 3]; t)
    """
        n_self = len(self.domain_list)
        result_pairs = []
        p = self.finest_partitions(*self.domain_list, *other.domain_list)
        for real_set, inds in p:
            new_pair = [real_set, 1]
            if not union and sum(inds) < 2: continue
            for i, ind in enumerate(inds):
                if ind > 0:
                    new_pair[1] *= self.func_list[i] if i < n_self else other.func_list[i - n_self]
            result_pairs.append(new_pair)

        return PiecewiseFunction(result_pairs)

    def is_continuous(self):
        r"""
        Return if the function is continuous

        OUTPUT:

        Boolean.

        EXAMPLES::
            sage: R.<t> = QQ[]
            sage: f1 = t
            sage: f2 = (t-1) ^ 2 + 1
            sage: f3 = 1 - t
            sage: D1 = RealSet([0, 1], [2, 3])
            sage: D2 = RealSet((1, 2))
            sage: D3 = RealSet((3, +oo))
            sage: p = piecewise([[D1, f1], [D2, f2], [D3, f3]])
            sage: q = piecewise([[D1, f1], [D2, f2]])
            sage: p.is_continuous()
            False
            sage: q.is_continuous()
            True
        """
        if not self._end_points:
            self._init_end_points()

        for point in self._end_points:
            val, (left, right) = self._end_points[point]
            if val:
                if (left is not None and left != val) or (right is not None and right != val):
                    return False
        return True

    def is_continuous_defined(self, xmin=0, xmax=1):
        r"""
        Return if the function is continuous at certain interval or point

        INPUT:

        - ``xmin`` -- the lower bound of interval
        - ``xmax `` -- the upper bound of interval

        OUTPUT:

        Boolean.

        EXAMPLES::
            sage: R.<t> = QQ[]
            sage: f1 = t
            sage: f2 = (t - 1) ^ 2 + 1
            sage: f3 = 1 - t
            sage: D1 = RealSet([0, 1], RealSet.closed_open(2, 3))
            sage: D2 = RealSet((1, 2))
            sage: D3 = RealSet(x >= 3)
            sage: p = piecewise([[D1, f1], [D2, f2], [D3, f3]])
            sage: p.is_continuous_defined(0, 2)
            True
            sage: p.is_continuous_defined(1, 3)
            False
            sage: p.is_continuous_defined(2, 4)
            False
            sage: p.is_continuous_defined(3, 4)
            True
        """

        if not self._end_points_list:
            self._init_end_points()
        # Should discuss whether it is reasonable to force
        # [xmin, xmax] totally included in domain
        if not RealSet([xmin, xmax]).is_subset(self.support):
            return False

        # O(log n) implementation
        ind = bisect.bisect_left(self._end_points_list, (((xmin, 0), -1), 0))
        seen = set()
        for i in range(ind, len(self._end_points_list)):
            ((point, epsilon), delta), idx = self._end_points_list[i]
            if point in seen:
                continue
            seen.add(point)
            val, (left, right) = self._end_points[point]
            if point == xmin and val != right:
                return False
            elif point == xmax and val != left:
                return False
            elif xmin < point < xmax and (val != left or val != right):
                return False
            elif point > xmax:
                return True
        return True


        # O(n) implementation
        # for point in self._end_points:
        #     val, (left, right) = self._end_points[point]
        #     if point == xmin and val != right:
        #         return False
        #     elif point == xmax and val != left:
        #         return False
        #     elif xmin < point < xmax and (val != left or val != right):
        #         return False
        #
        # return True

    def which_pair(self, x0):
        """
        Find Input x0 in which function

        INPUT:

        - ``x0``: a number in domain of piecewise function

        Returns:

        A piece in the piecewise function

        EXAMPLES::

            sage: R.<t> = QQ[]
            sage: f1 = 1 - t
            sage: f2 = t ^ 4 - t ^ 2
            sage: D1 = RealSet((-oo, 1), (4, 5))
            sage: D2 = RealSet([2, 3], x >= 6)
            sage: p = piecewise([[D1, f1], [D2, f2]])
            sage: p.which_pair(0)
            ((-oo, 1) ∪ (4, 5), -t + 1)
            sage: p.which_pair(1)
            Invalid input: x0 not in domain
            sage: p.which_pair(2)
            ([2, 3] ∪ [6, +oo), t^4 - t^2)
            sage: p.which_pair(3)
            ([2, 3] ∪ [6, +oo), t^4 - t^2)
            sage: p.which_pair(4)
            Invalid input: x0 not in domain
        """

        if not self._end_points:
            self._init_end_points()
        idx = bisect.bisect_left(self._end_points_list, (((x0, 1), -1), 0))
        if idx <= 0 or idx >= len(self._end_points_list):
            print("Invalid input: x0 not in domain")
            return None
        ((x, epsilon), delta), func_idx = self._end_points_list[idx]
        if delta < 0: return self.domain_list[func_idx], self.func_list[func_idx]
        else:
            print("Invalid input: x0 not in domain")
            return None

    def limits(self, x0):
        """
        Returns [function value at `x_0`, function value at `x_0^+`, function value at `x_0^-`].

        INPUT:

        -``x0``: A number in domain of piecewise function

        Returns:

        function value at `x_0`, function value at `x_0^+`, function value at `x_0^-`.

        EXAMPLES::

            sage: R.<t> = QQ[]
            sage: f1 = 1 - t
            sage: f2 = t ^ 4 + 1
            sage: D1 = RealSet((-oo, 1), (5, 6))
            sage: D2 = RealSet([1, 2], x >= 7)
            sage: p = piecewise([[D1, f1], [D2, f2]])
            sage: p.limits(1)
            (2, 0, 2)
            sage: p.limits(2)
            (17, 17, None)
            sage: p.limits(3)
            Invalid input: x0 not in domain
            sage: p.limits(5)
            (None, None, -4)
            sage: p.limits(6)
            (None, -5, None)
            sage: p.limits(7)
            (2402, None, 2402)
            sage: p.limits(8)
            (4097, 4097, 4097)
        """

        if not self._end_points:
            self._init_end_points()

        if x0 in self._end_points:
            return self._end_points[x0][0], self._end_points[x0][1][0], self._end_points[x0][1][1]
        else:
            result = self.which_pair(x0)
            if result:
                _, func = result
                func_val = func(x0)
                return func_val, func_val, func_val
            else:
                return None, None, None

    def derivative(self, var = None):
        """
        Derivative of piecewise function

        INPUT:

        - ``var``: the variable

        Returns:

        Piecewise function

        EXAMPLES::

            sage: R.<t> = QQ[]
            sage: f1 = 1 - t
            sage: f2 = t ^ 4 + 1
            sage: D1 = RealSet((-oo, 1), (5, 6))
            sage: D2 = RealSet([1, 2], x >= 7)
            sage: p = piecewise([[D1, f1], [D2, f2]]); p
            piecewise(t |--> -t + 1 on (-oo, 1) ∪ (4, 5), t |--> t^4 - t^2 on [2, 3] ∪ [6, +oo); t)
            sage: p.derivative()
            piecewise(t |--> -1 on (-oo, 1) ∪ (4, 5), t |--> 4*t^3 - 2*t on [2, 3] ∪ [6, +oo); t)
        """

        return PiecewiseFunction((dom, func._derivative(var)) for dom, func in self.__iter__())

    # def piecewise_add(self, other):
        #     """
        #     This is old version of piecewise_add. It takes advantage of disjointness of self.domain_list and other.domain_list.
        #     It utilize greedy method, instead of scan line. Please refer to this for future implementation.
        #
        #     Return a new piecewise function with domain the union
        #     of the original domains and functions summed. Undefined
        #     intervals in the union domain get function value `0`.
        #
        #     EXAMPLES::
        #
        #         sage: R.<t> = QQ[]
        #         sage: f1 = 1 - t
        #         sage: f2 = t^4 - t^2
        #         sage: f3 = t^2
        #         sage: f4 = 1-t^7
        #         sage: D1 = RealSet([0, 1], [4, 5])
        #         sage: D2 = RealSet([2, 3], [6, 7])
        #         sage: D3 = RealSet([1, 2], [3, 4])
        #         sage: D4 = RealSet([5, 6], [7, 8])
        #         sage: p = piecewise([[D1, f1], [D2, f2]])
        #         sage: q = piecewise([[D3, f3], [D4, f4]])
        #         sage: test = p + q
        #         sage: test
        #         piecewise(t |--> -t + 1 on [0, 1) ∪ (4, 5), t |--> t^2 - t + 1 on {1} ∪ {4}, t |--> t^2 on (1, 2) ∪ (3, 4), t |--> t^4 on {2} ∪ {3}, t |--> t^4 - t^2 on (2, 3) ∪ (6, 7), t |--> -t^7 - t + 2 on {5}, t |--> -t^7 + 1 on (5, 6) ∪ (7, 8], t |--> -t^7 + t^4 - t^2 + 1 on {6} ∪ {7}; t)
        #
        #         # RealSet.are_pairwise_disjoint(*[dom for dom, _ in test])
        #         # RealSet.union_of_realsets(*[dom for dom, _ in test])
        #         # other = PiecewiseFunction((dom, func) for dom, func in other)
        #     """
        #     int_func_dict = {}
        #     for dom, func_id in zip(self.domain_list, range(len(self.func_list))):
        #         for interval in dom:
        #             int_func_dict[interval] = (0, func_id)
        #     for dom, func_id in zip(other.domain_list, range(len(other.func_list))):
        #         for interval in dom:
        #             if interval in int_func_dict:
        #                 int_func_dict[interval] = (2, int_func_dict[interval][1], func_id)
        #             else:
        #                 int_func_dict[interval] = (1, func_id)
        #
        #     int_list = sorted(list(int_func_dict.keys()),
        #                       key=lambda x: (x.lower(), x.lower_open(), x.upper(), x.upper_closed()))
        #     result_pairs = defaultdict(list)
        #
        #     curr_interval = None
        #     curr_func = None
        #
        #     while len(int_list) > 0:
        #         next_interval = int_list.pop(0)
        #         next_func_info = int_func_dict[next_interval]
        #         if next_func_info[0] == 0:
        #             next_func = self.func_list[next_func_info[1]]
        #         elif next_func_info[0] == 1:
        #             next_func = other.func_list[next_func_info[1]]
        #         else:
        #             next_func = self.func_list[next_func_info[1]] + other.func_list[next_func_info[2]]
        #         if curr_interval is None:
        #             curr_interval = next_interval
        #             curr_func = next_func
        #             continue
        #         if next_interval.lower() > curr_interval.upper() or (
        #                 next_interval.lower() == curr_interval.upper() and not (
        #                 next_interval.lower_closed() and curr_interval.upper_closed())):
        #             result_pairs[curr_func].append(curr_interval)
        #             curr_interval, curr_func = next_interval, next_func
        #             continue
        #
        #         if not (
        #                 next_interval.lower() == curr_interval.lower() and next_interval.lower_closed() == curr_interval.lower_closed()):
        #             result_pairs[curr_func].append(RealSet.interval(lower=curr_interval.lower(),
        #                                                             upper=next_interval.lower(),
        #                                                             lower_closed=curr_interval.lower_closed(),
        #                                                             upper_closed=next_interval.lower_open())[0])
        #         if next_interval.upper() < curr_interval.upper() or (
        #                 next_interval.upper() == curr_interval.upper() and next_interval.upper_open() and curr_interval.upper_closed()):
        #             result_pairs[curr_func + next_func].append(RealSet.interval(lower=next_interval.lower(),
        #                                                                         upper=next_interval.upper(),
        #                                                                         lower_closed=next_interval.lower_closed(),
        #                                                                         upper_closed=next_interval.lower_closed())[
        #                                                            0])
        #             curr_interval = RealSet.interval(lower=next_interval.upper(),
        #                                              upper=curr_interval.upper(),
        #                                              lower_closed=next_interval.upper_open(),
        #                                              upper_closed=curr_interval.upper_closed())[0]
        #         elif next_interval.upper() > curr_interval.upper() or (
        #                 next_interval.upper() == curr_interval.upper() and next_interval.upper_closed() and curr_interval.upper_open()):
        #             result_pairs[curr_func + next_func].append(RealSet.interval(lower=next_interval.lower(),
        #                                                                         upper=curr_interval.upper(),
        #                                                                         lower_closed=next_interval.lower_closed(),
        #                                                                         upper_closed=curr_interval.upper_closed())[
        #                                                            0])
        #             curr_interval = RealSet.interval(lower=curr_interval.upper(),
        #                                              upper=next_interval.upper(),
        #                                              lower_closed=curr_interval.upper_open(),
        #                                              upper_closed=next_interval.upper_closed())[0]
        #             curr_func = next_func
        #         else:
        #             result_pairs[curr_func + next_func].append(RealSet.interval(lower=next_interval.lower(),
        #                                                                         upper=curr_interval.upper(),
        #                                                                         lower_closed=next_interval.lower_closed(),
        #                                                                         upper_closed=curr_interval.upper_closed())[
        #                                                            0])
        #             curr_interval = None
        #             curr_func = None
        #
        #     if curr_interval:
        #         result_pairs[curr_func].append(curr_interval)
        #
        #     return PiecewiseFunction((RealSet(*result_pairs[func]), func) for func in result_pairs)



piecewise = PiecewiseFunction
