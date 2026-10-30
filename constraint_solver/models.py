"""Modelling front-ends: Sudoku (SAT / CSP / DLX), N-Queens (DLX / CSP), graph colouring (SAT, chromatic
number), scheduling with precedences and machines (CSP, minimum makespan), generic exact cover, magic
squares."""
import math

from .cnf import CNF
from .csp import CSP, Disjunctive
from .dlx import DLX

SYMBOLS = "123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"
EMPTY = ".0_*"


# ---------------- Sudoku ----------------
def parse_sudoku(text):
    """Any N x N sudoku with N = k*k (4, 9, 16, 25): digits/letters for givens, '.', '0', '_' for blanks.
    Whitespace and box-drawing characters | - + are ignored. Returns (N, grid as list of ints, 0 = empty)."""
    chars = [c for c in text if not c.isspace() and c not in "|-+"]
    n2 = len(chars)
    n = math.isqrt(n2)
    box = math.isqrt(n)
    if n * n != n2 or box * box != n or n == 0:
        raise ValueError("a sudoku needs N*N cells with N a square number (got %d cells)" % n2)
    grid = []
    for c in chars:
        if c in EMPTY:
            grid.append(0)
        else:
            v = SYMBOLS.find(c.upper()) + 1
            if not 1 <= v <= n:
                raise ValueError("bad symbol %r for a %dx%d sudoku" % (c, n, n))
            grid.append(v)
    return n, grid


def format_sudoku(n, grid, boxes=True):
    box = math.isqrt(n)
    lines = []
    for r in range(n):
        if boxes and r and r % box == 0:
            lines.append("-+-".join("-" * (2 * box - 1) for _ in range(box)))
        row = []
        for c in range(n):
            if boxes and c and c % box == 0:
                row.append("|")
            v = grid[r * n + c]
            row.append(SYMBOLS[v - 1] if v else ".")
        lines.append(" ".join(row))
    return "\n".join(lines)


def _box(n, r, c):
    b = math.isqrt(n)
    return (r // b) * b + c // b


def sudoku_dlx(n, grid, limit=1):
    d = DLX(4 * n * n)
    for r in range(n):
        for c in range(n):
            given = grid[r * n + c]
            for v in ([given - 1] if given else range(n)):
                d.add_row([r * n + c, n * n + r * n + v, 2 * n * n + c * n + v, 3 * n * n + _box(n, r, c) * n + v],
                          (r, c, v + 1))
    out = []
    for sol in d.solutions(limit):
        g = [0] * (n * n)
        for r, c, v in sol:
            g[r * n + c] = v
        out.append(g)
    return out


def sudoku_sat(n, grid):
    cnf = CNF()
    base = cnf.n

    def x(r, c, v):
        return base + (r * n + c) * n + v + 1
    cnf.n += n * n * n
    for r in range(n):
        for c in range(n):
            cnf.exactly_one([x(r, c, v) for v in range(n)])
            if grid[r * n + c]:
                cnf.add(x(r, c, grid[r * n + c] - 1))
    b = math.isqrt(n)
    for v in range(n):
        for i in range(n):
            cnf.exactly_one([x(i, c, v) for c in range(n)])
            cnf.exactly_one([x(r, i, v) for r in range(n)])
            br, bc = (i // b) * b, (i % b) * b
            cnf.exactly_one([x(br + dr, bc + dc, v) for dr in range(b) for dc in range(b)])
    model = cnf.solve()
    if model is None:
        return None
    g = [0] * (n * n)
    for r in range(n):
        for c in range(n):
            for v in range(n):
                if x(r, c, v) in model:
                    g[r * n + c] = v + 1
    return g


def sudoku_csp(n, grid):
    csp = CSP()
    for r in range(n):
        for c in range(n):
            v = grid[r * n + c]
            csp.var((r, c), [v] if v else range(1, n + 1))
    b = math.isqrt(n)
    for i in range(n):
        csp.all_different([(i, c) for c in range(n)])
        csp.all_different([(r, i) for r in range(n)])
        br, bc = (i // b) * b, (i % b) * b
        csp.all_different([(br + dr, bc + dc) for dr in range(b) for dc in range(b)])
    sol = csp.solve()
    if sol is None:
        return None
    return [sol[(r, c)] for r in range(n) for c in range(n)]


def check_sudoku(n, grid, puzzle=None):
    b = math.isqrt(n)
    full = set(range(1, n + 1))
    for i in range(n):
        if set(grid[i * n:(i + 1) * n]) != full or {grid[r * n + i] for r in range(n)} != full:
            return False
        br, bc = (i // b) * b, (i % b) * b
        if {grid[(br + dr) * n + bc + dc] for dr in range(b) for dc in range(b)} != full:
            return False
    return puzzle is None or all(p == 0 or p == g for p, g in zip(puzzle, grid))


def solve_sudoku(text, engine="dlx"):
    n, grid = parse_sudoku(text)
    if engine == "dlx":
        sols = sudoku_dlx(n, grid, 1)
        return n, (sols[0] if sols else None)
    if engine == "sat":
        return n, sudoku_sat(n, grid)
    if engine == "csp":
        return n, sudoku_csp(n, grid)
    raise ValueError("engine must be dlx, sat or csp")


# ---------------- N-Queens ----------------
def queens_dlx(n, limit=None):
    """Rows and columns are primary columns; both diagonal families are secondary (at most one queen)."""
    d = DLX(2 * n, 2 * (2 * n - 1))
    for r in range(n):
        for c in range(n):
            d.add_row([r, n + c, 2 * n + r + c, 2 * n + (2 * n - 1) + (r - c + n - 1)], (r, c))
    for sol in d.solutions(limit):
        cols = [0] * n
        for r, c in sol:
            cols[r] = c
        yield cols


def queens_csp(n):
    csp = CSP()
    qs = [csp.int_var("q%d" % i, 0, n - 1) for i in range(n)]
    csp.all_different(qs)
    for i in range(n):
        for j in range(i + 1, n):
            csp.linear([1, -1], [qs[j], qs[i]], "!=", j - i)
            csp.linear([1, -1], [qs[i], qs[j]], "!=", j - i)
    sol = csp.solve()
    return [sol[q] for q in qs] if sol else None


def format_queens(cols):
    n = len(cols)
    return "\n".join(" ".join("Q" if cols[r] == c else "." for c in range(n)) for r in range(n))


# ---------------- graph colouring ----------------
def greedy_clique(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        if u != v:
            adj[u].add(v)
            adj[v].add(u)
    best = []
    for start in sorted(range(n), key=lambda v: -len(adj[v]))[:max(1, min(n, 20))]:
        clique = [start]
        cand = set(adj[start])
        while cand:
            v = max(cand, key=lambda x: len(adj[x] & cand))
            clique.append(v)
            cand &= adj[v]
        if len(clique) > len(best):
            best = clique
    return best


def dsatur(n, edges):
    """DSatur greedy colouring: returns a list of colours (0-based)."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        if u != v:
            adj[u].add(v)
            adj[v].add(u)
    color = [-1] * n
    for _ in range(n):
        v = max((u for u in range(n) if color[u] < 0),
                key=lambda u: (len({color[w] for w in adj[u] if color[w] >= 0}), len(adj[u])))
        used = {color[w] for w in adj[v]}
        c = 0
        while c in used:
            c += 1
        color[v] = c
    return color


def color_sat(n, edges, k, clique=()):
    if any(u == v for u, v in edges):
        return None                                   # a self-loop cannot be coloured
    cnf = CNF()
    x = [[cnf.var() for _ in range(k)] for _ in range(n)]
    for v in range(n):
        cnf.exactly_one(x[v])
    for u, v in edges:
        for c in range(k):
            cnf.add(-x[u][c], -x[v][c])
    for i, v in enumerate(list(clique)[:k]):        # symmetry breaking
        cnf.add(x[v][i])
    model = cnf.solve()
    if model is None:
        return None
    return [next(c for c in range(k) if x[v][c] in model) for v in range(n)]


def chromatic_number(n, edges):
    """Exact chromatic number: clique lower bound, DSatur upper bound, SAT for the values in between."""
    if n == 0:
        return 0, []
    if any(u == v for u, v in edges):
        raise ValueError("graph has a self-loop")
    if not edges:
        return 1, [0] * n
    clique = greedy_clique(n, edges)
    greedy = dsatur(n, edges)
    upper = max(greedy) + 1
    for k in range(len(clique), upper):
        col = color_sat(n, edges, k, clique)
        if col is not None:
            return k, col
    return upper, greedy


def valid_coloring(edges, colors):
    return all(colors[u] != colors[v] for u, v in edges)


# ---------------- scheduling ----------------
def parse_tasks(text):
    """Lines: 'name duration [on machine] [after a,b]'. Returns list of dicts."""
    tasks = []
    for raw in text.splitlines():
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        parts = line.split()
        if len(parts) < 2:
            raise ValueError("task line needs a name and a duration: %r" % raw)
        t = {"name": parts[0], "duration": int(parts[1]), "machine": None, "after": []}
        i = 2
        while i < len(parts):
            if parts[i] == "on" and i + 1 < len(parts):
                t["machine"] = parts[i + 1]
                i += 2
            elif parts[i] == "after" and i + 1 < len(parts):
                t["after"] += [p for p in ",".join(parts[i + 1:]).split(",") if p]
                break
            else:
                raise ValueError("cannot read %r in %r" % (parts[i], raw))
        tasks.append(t)
    names = {t["name"] for t in tasks}
    for t in tasks:
        for a in t["after"]:
            if a not in names:
                raise ValueError("task %s depends on unknown task %s" % (t["name"], a))
    return tasks


def schedule(tasks):
    """Minimum makespan with precedence and one-task-at-a-time machines. Returns (makespan, {name: start})."""
    horizon = sum(t["duration"] for t in tasks)
    csp = CSP()
    for t in tasks:
        csp.int_var(t["name"], 0, horizon - t["duration"])
    csp.int_var("__makespan", 0, horizon)
    dur = {t["name"]: t["duration"] for t in tasks}
    for t in tasks:
        csp.linear([1, -1], ["__makespan", t["name"]], ">=", t["duration"])
        for a in t["after"]:
            csp.linear([1, -1], [t["name"], a], ">=", dur[a])
    by_machine = {}
    for t in tasks:
        if t["machine"]:
            by_machine.setdefault(t["machine"], []).append(t["name"])
    for names in by_machine.values():
        for i in range(len(names)):
            for j in range(i + 1, len(names)):
                csp.add(Disjunctive(names[i], dur[names[i]], names[j], dur[names[j]]))
    best, sol = csp.minimize("__makespan")
    if sol is None:
        return None, None
    return best, {t["name"]: sol[t["name"]] for t in tasks}


def gantt(tasks, starts, width=60):
    span = max(starts[t["name"]] + t["duration"] for t in tasks) or 1
    scale = min(1.0, width / span)
    lines = []
    for t in sorted(tasks, key=lambda t: (starts[t["name"]], t["name"])):
        s = starts[t["name"]]
        bar = " " * int(s * scale) + "#" * max(1, int(round(t["duration"] * scale)))
        lines.append("%-12s %-8s %4d-%-4d |%s" % (t["name"], t["machine"] or "", s, s + t["duration"], bar))
    return "\n".join(lines)


# ---------------- exact cover / magic squares ----------------
def parse_cover(text):
    """'columns: A B C', optional 'secondary: X Y', then 'rowname: A C' lines."""
    primary, secondary, rows = [], [], []
    for raw in text.splitlines():
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        head, _, rest = line.partition(":")
        key = head.strip().lower()
        if key == "columns":
            primary = rest.split()
        elif key == "secondary":
            secondary = rest.split()
        else:
            rows.append((head.strip(), rest.split()))
    if not primary:
        raise ValueError("missing 'columns:' line")
    return primary, secondary, rows


def exact_cover_named(primary, secondary, rows, limit=None):
    index = {c: i for i, c in enumerate(primary + secondary)}
    d = DLX(len(primary), len(secondary))
    for name, cols in rows:
        try:
            d.add_row([index[c] for c in cols], name)
        except KeyError as exc:
            raise ValueError("row %s uses unknown column %s" % (name, exc))
    return list(d.solutions(limit))


def magic_square(n, limit=1):
    """n x n magic squares with the numbers 1..n^2 (CSP with linear sums)."""
    csp = CSP()
    cells = [[csp.int_var((r, c), 1, n * n) for c in range(n)] for r in range(n)]
    flat = [v for row in cells for v in row]
    total = n * (n * n + 1) // 2
    csp.all_different(flat)
    for i in range(n):
        csp.linear([1] * n, cells[i], "==", total)
        csp.linear([1] * n, [cells[r][i] for r in range(n)], "==", total)
    csp.linear([1] * n, [cells[i][i] for i in range(n)], "==", total)
    csp.linear([1] * n, [cells[i][n - 1 - i] for i in range(n)], "==", total)
    return [[[s[(r, c)] for c in range(n)] for r in range(n)] for s in csp.solutions(limit)]
