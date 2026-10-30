"""Finite-domain constraint solver: propagation to a fixpoint (AC-3 style queue), MRV/degree branching,
solution enumeration and branch-and-bound minimisation.

Constraints implement `propagate(dom)` that narrows the domains (dict var -> set) in place and returns the
set of variables it changed, or None when some domain becomes empty."""
import itertools
import math
from collections import defaultdict


class Constraint:
    scope = ()

    def propagate(self, dom):
        raise NotImplementedError

    def satisfied(self, assignment):
        raise NotImplementedError


def _restrict(dom, v, keep, changed):
    d = dom[v]
    new = {x for x in d if keep(x)}
    if len(new) != len(d):
        if not new:
            return False
        dom[v] = new
        changed.add(v)
    return True


class AllDifferent(Constraint):
    """Removes assigned values from the other variables, fails on pigeonhole violations, and assigns
    'hidden singles' when the variables must use every value of their union."""

    def __init__(self, scope):
        self.scope = list(scope)

    def propagate(self, dom):
        changed = set()
        while True:
            progress = False
            fixed = {}
            for v in self.scope:
                if len(dom[v]) == 1:
                    val = next(iter(dom[v]))
                    if val in fixed:
                        return None
                    fixed[val] = v
            for v in self.scope:
                if len(dom[v]) > 1 and fixed.keys() & dom[v]:
                    new = dom[v] - fixed.keys()
                    if not new:
                        return None
                    dom[v] = new
                    changed.add(v)
                    progress = True
            union = set().union(*(dom[v] for v in self.scope))
            if len(union) < len(self.scope):
                return None
            if len(union) == len(self.scope):
                where = defaultdict(list)
                for v in self.scope:
                    for x in dom[v]:
                        where[x].append(v)
                for x, vs in where.items():
                    if len(vs) == 1 and len(dom[vs[0]]) > 1:
                        dom[vs[0]] = {x}
                        changed.add(vs[0])
                        progress = True
            if not progress:
                return changed

    def satisfied(self, a):
        vals = [a[v] for v in self.scope]
        return len(set(vals)) == len(vals)


class Linear(Constraint):
    """sum(coef * var) op rhs with op in '<=', '>=', '==', '!=' and bounds propagation."""

    def __init__(self, coefs, scope, op, rhs):
        if op not in ("<=", ">=", "==", "!="):
            raise ValueError("bad operator %r" % op)
        self.coefs, self.scope, self.op, self.rhs = list(coefs), list(scope), op, rhs

    def _bounds(self, dom, i):
        a = self.coefs[i]
        d = dom[self.scope[i]]
        return (a * min(d), a * max(d)) if a >= 0 else (a * max(d), a * min(d))

    def propagate(self, dom):
        changed = set()
        if self.op == "!=":
            unfixed = [i for i, v in enumerate(self.scope) if len(dom[v]) > 1]
            if len(unfixed) == 0:
                return changed if self.satisfied({v: next(iter(dom[v])) for v in self.scope}) else None
            if len(unfixed) == 1:
                i = unfixed[0]
                rest = sum(a * next(iter(dom[v])) for k, (a, v) in enumerate(zip(self.coefs, self.scope)) if k != i)
                a = self.coefs[i]
                if a != 0 and (self.rhs - rest) % a == 0:
                    bad = (self.rhs - rest) // a
                    if not _restrict(dom, self.scope[i], lambda x: x != bad, changed):
                        return None
            return changed
        again = True
        while again:
            again = False
            bounds = [self._bounds(dom, i) for i in range(len(self.scope))]
            lo_sum = sum(b[0] for b in bounds)
            hi_sum = sum(b[1] for b in bounds)
            if self.op in ("<=", "==") and lo_sum > self.rhs:
                return None
            if self.op in (">=", "==") and hi_sum < self.rhs:
                return None
            for i, v in enumerate(self.scope):
                a = self.coefs[i]
                if a == 0:
                    continue
                lo_o, hi_o = lo_sum - bounds[i][0], hi_sum - bounds[i][1]
                keep_lo, keep_hi = -math.inf, math.inf      # bounds on a*x
                if self.op in ("<=", "=="):
                    keep_hi = self.rhs - lo_o
                if self.op in (">=", "=="):
                    keep_lo = self.rhs - hi_o
                before = len(dom[v])
                if not _restrict(dom, v, lambda x, a=a, lo=keep_lo, hi=keep_hi: lo <= a * x <= hi, changed):
                    return None
                if len(dom[v]) != before:
                    again = True
        return changed

    def satisfied(self, a):
        s = sum(c * a[v] for c, v in zip(self.coefs, self.scope))
        return {"<=": s <= self.rhs, ">=": s >= self.rhs, "==": s == self.rhs, "!=": s != self.rhs}[self.op]


class Predicate(Constraint):
    """Any relation given as a Python function; generalised arc consistency by enumeration, so keep the
    arity small (2-3 variables)."""

    def __init__(self, scope, fn, max_product=200000):
        self.scope, self.fn, self.max_product = list(scope), fn, max_product

    def propagate(self, dom):
        doms = [sorted(dom[v]) for v in self.scope]
        if math.prod(len(d) for d in doms) > self.max_product:
            return set()                             # too big to enumerate: checked once assigned
        supported = [set() for _ in self.scope]
        for combo in itertools.product(*doms):
            if self.fn(*combo):
                for k, x in enumerate(combo):
                    supported[k].add(x)
        changed = set()
        for k, v in enumerate(self.scope):
            if not supported[k]:
                return None
            if len(supported[k]) != len(dom[v]):
                dom[v] = supported[k]
                changed.add(v)
        return changed

    def satisfied(self, a):
        return bool(self.fn(*[a[v] for v in self.scope]))


class Table(Constraint):
    def __init__(self, scope, tuples):
        self.scope, self.tuples = list(scope), [tuple(t) for t in tuples]

    def propagate(self, dom):
        live = [t for t in self.tuples if all(x in dom[v] for x, v in zip(t, self.scope))]
        if not live:
            return None
        changed = set()
        for k, v in enumerate(self.scope):
            vals = {t[k] for t in live}
            if len(vals) != len(dom[v]):
                dom[v] = vals
                changed.add(v)
        return changed

    def satisfied(self, a):
        return tuple(a[v] for v in self.scope) in set(self.tuples)


class Disjunctive(Constraint):
    """Two tasks on one resource: s1 + d1 <= s2 or s2 + d2 <= s1 (bounds reasoning)."""

    def __init__(self, s1, d1, s2, d2):
        self.scope, self.d1, self.d2 = [s1, s2], d1, d2

    def propagate(self, dom):
        s1, s2 = self.scope
        changed = set()
        can_12 = min(dom[s1]) + self.d1 <= max(dom[s2])          # 1 before 2 still possible
        can_21 = min(dom[s2]) + self.d2 <= max(dom[s1])
        if not can_12 and not can_21:
            return None
        if can_12 and not can_21:
            lo2 = min(dom[s1]) + self.d1
            hi1 = max(dom[s2]) - self.d1
            if not _restrict(dom, s2, lambda x: x >= lo2, changed) or \
                    not _restrict(dom, s1, lambda x: x <= hi1, changed):
                return None
        elif can_21 and not can_12:
            lo1 = min(dom[s2]) + self.d2
            hi2 = max(dom[s1]) - self.d2
            if not _restrict(dom, s1, lambda x: x >= lo1, changed) or \
                    not _restrict(dom, s2, lambda x: x <= hi2, changed):
                return None
        return changed

    def satisfied(self, a):
        s1, s2 = self.scope
        return a[s1] + self.d1 <= a[s2] or a[s2] + self.d2 <= a[s1]


class CSP:
    def __init__(self):
        self.domains = {}
        self.constraints = []
        self.watch = defaultdict(list)
        self.nodes = 0

    def var(self, name, values):
        values = set(values)
        if not values:
            raise ValueError("empty domain for %r" % (name,))
        self.domains[name] = values
        return name

    def int_var(self, name, lo, hi):
        return self.var(name, range(lo, hi + 1))

    def add(self, c):
        for v in c.scope:
            if v not in self.domains:
                raise KeyError("unknown variable %r" % (v,))
        idx = len(self.constraints)
        self.constraints.append(c)
        for v in set(c.scope):
            self.watch[v].append(idx)
        return c

    def all_different(self, scope):
        return self.add(AllDifferent(scope))

    def linear(self, coefs, scope, op, rhs):
        return self.add(Linear(coefs, scope, op, rhs))

    def predicate(self, scope, fn):
        return self.add(Predicate(scope, fn))

    def table(self, scope, tuples):
        return self.add(Table(scope, tuples))

    # ---- search ----
    def _propagate(self, dom, queue):
        queue = list(queue)
        inq = set(queue)
        while queue:
            ci = queue.pop()
            inq.discard(ci)
            changed = self.constraints[ci].propagate(dom)
            if changed is None:
                return False
            for v in changed:
                for cj in self.watch[v]:
                    if cj != ci and cj not in inq:
                        inq.add(cj)
                        queue.append(cj)
        return True

    def _choose(self, dom):
        best, key = None, None
        for v, d in dom.items():
            if len(d) > 1:
                k = (len(d), -len(self.watch[v]))
                if key is None or k < key:
                    best, key = v, k
        return best

    def solutions(self, limit=None, value_order=sorted):
        dom = {v: set(d) for v, d in self.domains.items()}
        if not self._propagate(dom, range(len(self.constraints))):
            return
        found = 0
        stack = [dom]
        while stack:
            dom = stack.pop()
            self.nodes += 1
            v = self._choose(dom)
            if v is None:
                sol = {x: next(iter(d)) for x, d in dom.items()}
                if all(c.satisfied(sol) for c in self.constraints):
                    yield sol
                    found += 1
                    if limit is not None and found >= limit:
                        return
                continue
            children = []
            for val in value_order(dom[v]):
                child = {x: set(d) for x, d in dom.items()}
                child[v] = {val}
                if self._propagate(child, self.watch[v]):
                    children.append(child)
            stack.extend(reversed(children))

    def solve(self):
        return next(self.solutions(1), None)

    def count(self, limit=None):
        return sum(1 for _ in self.solutions(limit))

    def minimize(self, objective):
        """Branch and bound on a variable: returns (best value, solution) or (None, None)."""
        best_val, best_sol = None, None
        original = set(self.domains[objective])
        try:
            while True:
                sol = self.solve()
                if sol is None:
                    break
                best_val, best_sol = sol[objective], sol
                tighter = {x for x in self.domains[objective] if x < best_val}
                if not tighter:
                    break
                self.domains[objective] = tighter
        finally:
            self.domains[objective] = original
        return best_val, best_sol
