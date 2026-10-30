"""A CDCL SAT solver: two watched literals, 1-UIP clause learning with minimisation, VSIDS decisions on a
lazy heap, phase saving, Luby restarts and solving under assumptions.

Literals are DIMACS integers (+v / -v, v >= 1) at the interface; internally literal 2*(v-1) is v and
2*(v-1)+1 is not-v, so negation is `lit ^ 1`."""
import heapq


def luby(i):
    """i-th element (1-based) of the Luby sequence 1 1 2 1 1 2 4 1 1 2 ..."""
    k = 1
    while (1 << k) - 1 < i:
        k += 1
    while (1 << k) - 1 != i:
        i -= (1 << (k - 1)) - 1
        k = 1
        while (1 << k) - 1 < i:
            k += 1
    return 1 << (k - 1)


class Solver:
    def __init__(self, n_vars=0):
        self.n = 0
        self.clauses = []
        self.watches = []
        self.assign = []          # per var: 0 unassigned, 1 true, -1 false
        self.level = []
        self.reason = []
        self.activity = []
        self.phase = []
        self.trail, self.trail_lim = [], []
        self.qhead = 0
        self.heap = []
        self.var_inc = 1.0
        self.ok = True
        self.conflicts = self.decisions = self.propagations = 0
        self.model = None
        for _ in range(n_vars):
            self.new_var()

    # ---- construction ----
    def new_var(self):
        self.n += 1
        self.watches += [[], []]
        self.assign.append(0)
        self.level.append(0)
        self.reason.append(None)
        self.activity.append(0.0)
        self.phase.append(False)
        heapq.heappush(self.heap, (0.0, self.n - 1))
        return self.n

    @staticmethod
    def _internal(lit):
        return 2 * (lit - 1) if lit > 0 else 2 * (-lit - 1) + 1

    @staticmethod
    def _external(l):
        return (l >> 1) + 1 if not l & 1 else -((l >> 1) + 1)

    def _value(self, l):
        a = self.assign[l >> 1]
        return a if not l & 1 else -a

    def add_clause(self, lits):
        """Add a clause (iterable of DIMACS literals). Returns False if the formula became UNSAT."""
        if not self.ok:
            return False
        if self.trail_lim:
            self._backtrack(0)
        seen, clause = set(), []
        for lit in lits:
            if lit == 0:
                raise ValueError("0 is not a literal")
            while abs(lit) > self.n:
                self.new_var()
            l = self._internal(lit)
            if l ^ 1 in seen:
                return True                       # tautology
            if l in seen:
                continue
            v = self._value(l)
            if v == 1:
                return True                       # already satisfied at level 0
            if v == -1:
                continue                          # false at level 0
            seen.add(l)
            clause.append(l)
        if not clause:
            self.ok = False
            return False
        if len(clause) == 1:
            self._enqueue(clause[0], None)
            if self._propagate() is not None:
                self.ok = False
            return self.ok
        self._attach(clause)
        return True

    def _attach(self, clause):
        ci = len(self.clauses)
        self.clauses.append(clause)
        self.watches[clause[0]].append(ci)
        self.watches[clause[1]].append(ci)
        return ci

    # ---- core ----
    def _enqueue(self, l, reason):
        v = l >> 1
        self.assign[v] = -1 if l & 1 else 1
        self.level[v] = len(self.trail_lim)
        self.reason[v] = reason
        self.trail.append(l)

    def _propagate(self):
        """Unit propagation; returns a conflicting clause index or None."""
        clauses, watches = self.clauses, self.watches
        while self.qhead < len(self.trail):
            p = self.trail[self.qhead]
            self.qhead += 1
            self.propagations += 1
            false_lit = p ^ 1
            ws = watches[false_lit]
            keep = []
            i, n = 0, len(ws)
            while i < n:
                ci = ws[i]
                i += 1
                c = clauses[ci]
                if c[0] == false_lit:
                    c[0], c[1] = c[1], c[0]
                first = c[0]
                if self._value(first) == 1:
                    keep.append(ci)
                    continue
                for k in range(2, len(c)):
                    if self._value(c[k]) != -1:
                        c[1], c[k] = c[k], c[1]
                        watches[c[1]].append(ci)
                        break
                else:
                    keep.append(ci)
                    if self._value(first) == -1:
                        keep.extend(ws[i:])
                        watches[false_lit] = keep
                        self.qhead = len(self.trail)
                        return ci
                    self._enqueue(first, ci)
            watches[false_lit] = keep
        return None

    def _bump(self, v):
        self.activity[v] += self.var_inc
        if self.activity[v] > 1e100:
            self.activity = [a * 1e-100 for a in self.activity]
            self.var_inc *= 1e-100
            self.heap = [(-self.activity[u], u) for u in range(self.n) if self.assign[u] == 0]
            heapq.heapify(self.heap)
        if self.assign[v] == 0:
            heapq.heappush(self.heap, (-self.activity[v], v))

    def _analyze(self, ci):
        """1-UIP learning. Returns (learnt clause with the asserting literal first, backtrack level)."""
        seen = [False] * self.n
        learnt = [None]
        counter = 0
        p = None
        idx = len(self.trail) - 1
        cur = len(self.trail_lim)
        while True:
            c = self.clauses[ci]
            for q in (c if p is None else c[1:]):
                v = q >> 1
                if not seen[v] and self.level[v] > 0:
                    seen[v] = True
                    self._bump(v)
                    if self.level[v] >= cur:
                        counter += 1
                    else:
                        learnt.append(q)
            while not seen[self.trail[idx] >> 1]:
                idx -= 1
            p = self.trail[idx]
            idx -= 1
            seen[p >> 1] = False
            counter -= 1
            if counter == 0:
                break
            ci = self.reason[p >> 1]
        learnt[0] = p ^ 1
        # local minimisation: drop literals implied by other literals of the clause
        kept = [learnt[0]]
        for q in learnt[1:]:
            r = self.reason[q >> 1]
            if r is None or not all(seen[x >> 1] or self.level[x >> 1] == 0 for x in self.clauses[r][1:]):
                kept.append(q)
        learnt = kept
        if len(learnt) == 1:
            return learnt, 0
        best = max(range(1, len(learnt)), key=lambda k: self.level[learnt[k] >> 1])
        learnt[1], learnt[best] = learnt[best], learnt[1]
        return learnt, self.level[learnt[1] >> 1]

    def _backtrack(self, level):
        if len(self.trail_lim) <= level:
            return
        start = self.trail_lim[level]
        for l in self.trail[start:]:
            v = l >> 1
            self.phase[v] = not (l & 1)
            self.assign[v] = 0
            self.reason[v] = None
            heapq.heappush(self.heap, (-self.activity[v], v))
        del self.trail[start:]
        del self.trail_lim[level:]
        self.qhead = len(self.trail)

    def _pick(self):
        while self.heap:
            _, v = heapq.heappop(self.heap)
            if self.assign[v] == 0:
                return v
        return None

    def solve(self, assumptions=(), max_conflicts=None):
        """True (model in self.model / value()), False (UNSAT under the assumptions), or None (limit hit)."""
        self.model = None
        if not self.ok:
            return False
        self._backtrack(0)
        if self._propagate() is not None:
            self.ok = False
            return False
        assume = [self._internal(a) for a in assumptions]
        for a in assumptions:
            while abs(a) > self.n:
                self.new_var()
        restart_no, budget = 1, 100 * luby(1)
        since_restart = 0
        start_conflicts = self.conflicts
        while True:
            confl = self._propagate()
            if confl is not None:
                self.conflicts += 1
                since_restart += 1
                if not self.trail_lim:
                    self.ok = False
                    return False
                learnt, back = self._analyze(confl)
                self._backtrack(back)
                if len(learnt) == 1:
                    self._enqueue(learnt[0], None)
                else:
                    ci = self._attach(learnt)
                    self._enqueue(learnt[0], ci)
                self.var_inc /= 0.95
                if max_conflicts is not None and self.conflicts - start_conflicts >= max_conflicts:
                    self._backtrack(0)
                    return None
                continue
            if since_restart >= budget:
                restart_no += 1
                budget = 100 * luby(restart_no)
                since_restart = 0
                self._backtrack(0)
                continue
            level = len(self.trail_lim)
            if level < len(assume):
                a = assume[level]
                val = self._value(a)
                if val == -1:
                    self._backtrack(0)
                    return False
                self.trail_lim.append(len(self.trail))
                if val == 0:
                    self._enqueue(a, None)
                continue
            v = self._pick()
            if v is None:
                self.model = [False] + [a == 1 for a in self.assign]
                self._backtrack(0)
                return True
            self.decisions += 1
            self.trail_lim.append(len(self.trail))
            self._enqueue(2 * v + (0 if self.phase[v] else 1), None)

    def value(self, var):
        if self.model is None:
            raise ValueError("no model: call solve() first and check it returned True")
        return self.model[var]

    def model_literals(self):
        return [v if self.model[v] else -v for v in range(1, self.n + 1)]

    def stats(self):
        return {"vars": self.n, "clauses": len(self.clauses), "conflicts": self.conflicts,
                "decisions": self.decisions, "propagations": self.propagations}


def parse_dimacs(text):
    """Returns (n_vars, clauses). Comment lines start with 'c'; clauses may span lines."""
    n, clauses, cur = 0, [], []
    for line in text.splitlines():
        line = line.strip()
        if not line or line[0] in "c%":
            continue
        if line.startswith("p"):
            parts = line.split()
            if len(parts) < 4 or parts[1] != "cnf":
                raise ValueError("bad problem line: %r" % line)
            n = int(parts[2])
            continue
        for tok in line.split():
            x = int(tok)
            if x == 0:
                clauses.append(cur)
                cur = []
            else:
                cur.append(x)
                n = max(n, abs(x))
    if cur:
        clauses.append(cur)
    return n, clauses


def to_dimacs(n, clauses, comment=None):
    head = ["c %s" % comment] if comment else []
    return "\n".join(head + ["p cnf %d %d" % (n, len(clauses))] + [" ".join(map(str, c)) + " 0" for c in clauses]) + "\n"


def solve_clauses(clauses, n=0, assumptions=()):
    s = Solver(n)
    for c in clauses:
        if not s.add_clause(c):
            return None
    return s.model_literals() if s.solve(assumptions) else None


def check_model(clauses, literals):
    truth = set(literals)
    return all(any(l in truth for l in c) for c in clauses)
