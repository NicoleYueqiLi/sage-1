# coding=utf-8
from sage.rings.polynomial.polynomial_element import Polynomial, is_Polynomial
from sage.sets.real_set import RealSet
from collections import defaultdict


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
        for domain, func in function_pieces:
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
            self.domain_list.append(domain)
            self.func_list.append(func)
        if not RealSet.are_pairwise_disjoint(*self.domain_list):
            raise ValueError("Invalid domain. Should be mutually disjoint.")

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

            sage: my_abs = piecewise([((-1, 0), -x), ([0, 1], x)], var=x);  my_abs
            piecewise(x|-->-x on (-1, 0), x|-->x on [0, 1]; x)
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

        Integer.

        EXAMPLES::

            sage: f = piecewise([([0,0], sin(x)), ((0,2), cos(x))]);  f
            piecewise(x|-->sin(x) on {0}, x|-->cos(x) on (0, 2); x)
            sage: len(f)
            2
        """
        return len(self.func_list)

    def __iter__(self):
        for dom, func in zip(self.domain_list, self.func_list):
            yield dom, func

    def __add__(self, other):
        # should add a check on variables.
        if type(other) == type(self):
            return self.piecewise_add(other)
        else:
            return PiecewiseFunction((dom, func + other) for dom, func in self.__iter__())

    __radd__ = __add__

    def piecewise_add(self, other):
        """
        Return a new piecewise function with domain the union
        of the original domains and functions summed. Undefined
        intervals in the union domain get function value `0`.

        EXAMPLES::

            sage: R.<t> = QQ[]
            sage: f1 = 1 - t
            sage: f2 = t^4 - t^2
            sage: f3 = t^2
            sage: f4 = 1-t^7
            sage: D1 = RealSet([0, 1], [4, 5])
            sage: D2 = RealSet([2, 3], [6, 7])
            sage: D3 = RealSet([1, 2], [3, 4])
            sage: D4 = RealSet([5, 6], [7, 8])
            sage: p = piecewise([[D1, f1], [D2, f2]])
            sage: q = piecewise([[D3, f3], [D4, f4]])
            sage: test = p + q
            sage: test
            piecewise(t |--> -t + 1 on [0, 1) ∪ (4, 5), t |--> t^2 - t + 1 on {1} ∪ {4}, t |--> t^2 on (1, 2) ∪ (3, 4), t |--> t^4 on {2} ∪ {3}, t |--> t^4 - t^2 on (2, 3) ∪ (6, 7), t |--> -t^7 - t + 2 on {5}, t |--> -t^7 + 1 on (5, 6) ∪ (7, 8], t |--> -t^7 + t^4 - t^2 + 1 on {6} ∪ {7}; t)

            # RealSet.are_pairwise_disjoint(*[dom for dom, _ in test])
            # RealSet.union_of_realsets(*[dom for dom, _ in test])
            # other = PiecewiseFunction((dom, func) for dom, func in other)
        """
        int_func_dict = {}
        for dom, func_id in zip(self.domain_list, range(len(self.func_list))):
            for interval in dom:
                int_func_dict[interval] = (0, func_id)
        for dom, func_id in zip(other.domain_list, range(len(other.func_list))):
            for interval in dom:
                if interval in int_func_dict:
                    int_func_dict[interval] = (2, int_func_dict[interval][1], func_id)
                else:
                    int_func_dict[interval] = (1, func_id)

        int_list = sorted(list(int_func_dict.keys()),
                          key=lambda x: (x.lower(), x.lower_open(), x.upper(), x.upper_closed()))
        result_pairs = defaultdict(list)

        curr_interval = None
        curr_func = None

        while len(int_list) > 0:
            next_interval = int_list.pop(0)
            next_func_info = int_func_dict[next_interval]
            if next_func_info[0] == 0:
                next_func = self.func_list[next_func_info[1]]
            elif next_func_info[0] == 1:
                next_func = other.func_list[next_func_info[1]]
            else:
                next_func = self.func_list[next_func_info[1]] + other.func_list[next_func_info[2]]
            if curr_interval is None:
                curr_interval = next_interval
                curr_func = next_func
                continue
            if next_interval.lower() > curr_interval.upper() or (
                    next_interval.lower() == curr_interval.upper() and not (
                    next_interval.lower_closed() and curr_interval.upper_closed())):
                result_pairs[curr_func].append(curr_interval)
                curr_interval, curr_func = next_interval, next_func
                continue

            if not (
                    next_interval.lower() == curr_interval.lower() and next_interval.lower_closed() == curr_interval.lower_closed()):
                result_pairs[curr_func].append(RealSet.interval(lower=curr_interval.lower(),
                                                                upper=next_interval.lower(),
                                                                lower_closed=curr_interval.lower_closed(),
                                                                upper_closed=next_interval.lower_open())[0])
            if next_interval.upper() < curr_interval.upper() or (
                    next_interval.upper() == curr_interval.upper() and next_interval.upper_open() and curr_interval.upper_closed()):
                result_pairs[curr_func + next_func].append(RealSet.interval(lower=next_interval.lower(),
                                                                            upper=next_interval.upper(),
                                                                            lower_closed=next_interval.lower_closed(),
                                                                            upper_closed=next_interval.lower_closed())[
                                                               0])
                curr_interval = RealSet.interval(lower=next_interval.upper(),
                                                 upper=curr_interval.upper(),
                                                 lower_closed=next_interval.upper_open(),
                                                 upper_closed=curr_interval.upper_closed())[0]
            elif next_interval.upper() > curr_interval.upper() or (
                    next_interval.upper() == curr_interval.upper() and next_interval.upper_closed() and curr_interval.upper_open()):
                result_pairs[curr_func + next_func].append(RealSet.interval(lower=next_interval.lower(),
                                                                            upper=curr_interval.upper(),
                                                                            lower_closed=next_interval.lower_closed(),
                                                                            upper_closed=curr_interval.upper_closed())[
                                                               0])
                curr_interval = RealSet.interval(lower=curr_interval.upper(),
                                                 upper=next_interval.upper(),
                                                 lower_closed=curr_interval.upper_open(),
                                                 upper_closed=next_interval.upper_closed())[0]
                curr_func = next_func
            else:
                result_pairs[curr_func + next_func].append(RealSet.interval(lower=next_interval.lower(),
                                                                            upper=curr_interval.upper(),
                                                                            lower_closed=next_interval.lower_closed(),
                                                                            upper_closed=curr_interval.upper_closed())[
                                                               0])
                curr_interval = None
                curr_func = None

        if curr_interval:
            result_pairs[curr_func].append(curr_interval)

        return PiecewiseFunction((RealSet(*result_pairs[func]), func) for func in result_pairs)

    def __neg__(self):
        return PiecewiseFunction((dom, -func) for dom, func in self.__iter__())

    def __sub__(self, other):
        return self.__add__(other.__neg__())

    def __rsub__(self, other):
        return other.__add__(self.__neg__())


piecewise = PiecewiseFunction
