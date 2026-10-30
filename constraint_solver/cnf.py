"""CNF modelling helpers: fresh variables, cardinality encodings (pairwise, sequential counter),
Tseitin gates, and a bridge to the CDCL solver."""
from .sat import Solver, to_dimacs


class CNF:
    def __init__(self):
        self.n = 0
        self.clauses = []
        self.names = {}

    def var(self, name=None):
        self.n += 1
        if name is not None:
            self.names[name] = self.n
        return self.n

    def vars(self, k):
        return [self.var() for _ in range(k)]

    def add(self, *lits):
        self.clauses.append(list(lits))

    def add_clause(self, lits):
        self.clauses.append(list(lits))

    def implies(self, a, b):
        self.add(-a, b)

    def at_least_one(self, lits):
        self.add_clause(lits)

    def at_most_one(self, lits, method="auto"):
        lits = list(lits)
        if method == "auto":
            method = "pairwise" if len(lits) <= 6 else "sequential"
        if method == "pairwise":
            for i in range(len(lits)):
                for j in range(i + 1, len(lits)):
                    self.add(-lits[i], -lits[j])
        else:
            self.at_most_k(lits, 1)

    def exactly_one(self, lits, method="auto"):
        self.at_least_one(lits)
        self.at_most_one(lits, method)

    def at_most_k(self, lits, k):
        """Sinz's sequential counter: O(n*k) auxiliary variables and clauses."""
        lits = list(lits)
        n = len(lits)
        if k >= n:
            return
        if k == 0:
            for x in lits:
                self.add(-x)
            return
        s = [[self.var() for _ in range(k)] for _ in range(n - 1)]
        self.add(-lits[0], s[0][0])
        for j in range(1, k):
            self.add(-s[0][j])
        for i in range(1, n - 1):
            self.add(-lits[i], s[i][0])
            self.add(-s[i - 1][0], s[i][0])
            for j in range(1, k):
                self.add(-lits[i], -s[i - 1][j - 1], s[i][j])
                self.add(-s[i - 1][j], s[i][j])
            self.add(-lits[i], -s[i - 1][k - 1])
        self.add(-lits[n - 1], -s[n - 2][k - 1])

    def at_least_k(self, lits, k):
        lits = list(lits)
        if k <= 0:
            return
        if k > len(lits):
            self.add_clause([])                 # impossible
            return
        self.at_most_k([-x for x in lits], len(lits) - k)

    def exactly_k(self, lits, k):
        self.at_most_k(lits, k)
        self.at_least_k(lits, k)

    def and_gate(self, ins):
        """Fresh y with y <-> AND(ins)."""
        y = self.var()
        for x in ins:
            self.add(-y, x)
        self.add_clause([y] + [-x for x in ins])
        return y

    def or_gate(self, ins):
        y = self.var()
        for x in ins:
            self.add(y, -x)
        self.add_clause([-y] + list(ins))
        return y

    def xor_gate(self, a, b):
        y = self.var()
        self.add(-y, a, b)
        self.add(-y, -a, -b)
        self.add(y, -a, b)
        self.add(y, a, -b)
        return y

    def solver(self):
        s = Solver(self.n)
        for c in self.clauses:
            s.add_clause(c)
        return s

    def solve(self, assumptions=()):
        """Model as a set of true variables, or None when UNSAT."""
        s = self.solver()
        if not s.ok or not s.solve(assumptions):
            return None
        return {v for v in range(1, self.n + 1) if s.value(v)}

    def to_dimacs(self, comment=None):
        return to_dimacs(self.n, self.clauses, comment)
