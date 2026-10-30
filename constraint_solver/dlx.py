"""Knuth's Algorithm X with dancing links (array based), including secondary (at most once) columns."""


class DLX:
    def __init__(self, n_primary, n_secondary=0):
        self.np, self.ns = n_primary, n_secondary
        cols = n_primary + n_secondary
        # node 0 is the root; nodes 1..cols are column headers
        self.R = [0] * (cols + 1)
        self.L = [0] * (cols + 1)
        for c in range(cols + 1):
            self.L[c], self.R[c] = c, c
        prev = 0
        for c in range(1, n_primary + 1):          # only primary columns are linked to the root
            self.R[prev], self.L[c] = c, prev
            prev = c
        self.R[prev], self.L[0] = 0, prev
        self.U = list(range(cols + 1))
        self.D = list(range(cols + 1))
        self.C = list(range(cols + 1))
        self.S = [0] * (cols + 1)
        self.row_of = [None] * (cols + 1)
        self.rows = []
        self.updates = 0

    def add_row(self, columns, row_id=None):
        """columns: 0-based column indices (primary first, then secondary)."""
        rid = len(self.rows) if row_id is None else row_id
        self.rows.append(rid)
        first = None
        for col in sorted(set(columns)):
            if not 0 <= col < self.np + self.ns:
                raise ValueError("column %d out of range" % col)
            c = col + 1
            x = len(self.C)
            self.C.append(c)
            self.row_of.append(rid)
            self.U.append(self.U[c])
            self.D.append(c)
            self.D[self.U[c]] = x
            self.U[c] = x
            self.S[c] += 1
            if first is None:
                self.L.append(x)
                self.R.append(x)
                first = x
            else:
                self.L.append(self.L[first])
                self.R.append(first)
                self.R[self.L[first]] = x
                self.L[first] = x
        return rid

    def _cover(self, c):
        L, R, U, D, C, S = self.L, self.R, self.U, self.D, self.C, self.S
        R[L[c]], L[R[c]] = R[c], L[c]
        i = D[c]
        while i != c:
            j = R[i]
            while j != i:
                D[U[j]], U[D[j]] = D[j], U[j]
                S[C[j]] -= 1
                self.updates += 1
                j = R[j]
            i = D[i]

    def _uncover(self, c):
        L, R, U, D, C, S = self.L, self.R, self.U, self.D, self.C, self.S
        i = U[c]
        while i != c:
            j = L[i]
            while j != i:
                S[C[j]] += 1
                D[U[j]] = j
                U[D[j]] = j
                j = L[j]
            i = U[i]
        R[L[c]] = c
        L[R[c]] = c

    def solutions(self, limit=None):
        """Yield solutions as lists of row ids (iterative search, so deep covers are fine)."""
        R, D, C, S = self.R, self.D, self.C, self.S
        found = 0
        partial = []
        stack = []                     # (column, current row node)
        while True:
            if R[0] == 0:
                yield [self.row_of[x] for x in partial]
                found += 1
                if limit is not None and found >= limit:
                    return
                advance = True
            else:
                best, c = None, R[0]
                while c != 0:
                    if best is None or S[c] < S[best]:
                        best = c
                        if S[c] == 0:
                            break
                    c = R[c]
                self._cover(best)
                stack.append([best, best])
                advance = True
            # move to the next row of the top column (backtracking as needed)
            while advance:
                if not stack:
                    return
                col, r = stack[-1]
                if r != col:                       # undo the previously chosen row
                    j = self.L[r]
                    while j != r:
                        self._uncover(C[j])
                        j = self.L[j]
                    partial.pop()
                r = D[r]
                if r == col:
                    self._uncover(col)
                    stack.pop()
                    continue
                stack[-1][1] = r
                partial.append(r)
                j = R[r]
                while j != r:
                    self._cover(C[j])
                    j = R[j]
                advance = False

    def solve(self):
        return next(self.solutions(1), None)

    def count(self, limit=None):
        return sum(1 for _ in self.solutions(limit))


def exact_cover(n_columns, rows, secondary=0, limit=None):
    """rows: list of column-index lists (columns >= n_columns - secondary are secondary)."""
    d = DLX(n_columns - secondary, secondary)
    for i, r in enumerate(rows):
        d.add_row(r, i)
    return list(d.solutions(limit))
