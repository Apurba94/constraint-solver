"""Command-line interface for constraint-solver."""
import argparse
import sys
import time

from . import models
from .sat import Solver, parse_dimacs


def _read(path):
    if path == "-":
        return sys.stdin.read()
    with open(path, encoding="utf-8") as fh:
        return fh.read()


def _read_graph(text):
    lines = [l.split() for l in text.splitlines() if l.strip() and not l.startswith("#")]
    n, m = int(lines[0][0]), int(lines[0][1]) if len(lines[0]) > 1 else len(lines) - 1
    raw = [(int(a), int(b)) for a, b, *_ in lines[1:1 + m]]
    base = 0 if any(0 in e for e in raw) else 1
    return n, [(a - base, b - base) for a, b in raw], base


def main(argv=None):
    ap = argparse.ArgumentParser(prog="constraint-solver", description="SAT, CSP and exact-cover solving.")
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("sat", help="solve a DIMACS CNF file (competition-style output)")
    s.add_argument("cnf")
    s.add_argument("--stats", action="store_true")
    s.add_argument("--max-conflicts", type=int)
    su = sub.add_parser("sudoku", help="solve an N x N sudoku (N = 4, 9, 16, ...)")
    su.add_argument("puzzle", help="file with the grid ('-' for stdin)")
    su.add_argument("-e", "--engine", choices=["dlx", "sat", "csp"], default="dlx")
    su.add_argument("--count", action="store_true", help="count solutions (up to 1000) to check uniqueness")
    q = sub.add_parser("queens", help="N-Queens")
    q.add_argument("n", type=int)
    q.add_argument("--count", action="store_true")
    q.add_argument("--engine", choices=["dlx", "csp"], default="dlx")
    c = sub.add_parser("color", help="graph colouring: 'n m' then 'u v' lines")
    c.add_argument("graph")
    c.add_argument("-k", type=int, help="test k-colourability instead of computing the chromatic number")
    sc = sub.add_parser("schedule", help="minimum makespan: 'task duration [on machine] [after a,b]' lines")
    sc.add_argument("tasks")
    cv = sub.add_parser("cover", help="exact cover: 'columns: ...', optional 'secondary: ...', 'row: cols'")
    cv.add_argument("file")
    cv.add_argument("--all", action="store_true")
    mg = sub.add_parser("magic", help="magic squares")
    mg.add_argument("n", type=int)
    args = ap.parse_args(argv)

    try:
        if args.cmd == "sat":
            n, clauses = parse_dimacs(_read(args.cnf))
            solver = Solver(n)
            t0 = time.perf_counter()
            ok = all(solver.add_clause(cl) for cl in clauses)
            res = solver.solve(max_conflicts=args.max_conflicts) if ok else False
            if res is None:
                print("s UNKNOWN")
                code = 0
            elif res:
                print("s SATISFIABLE")
                lits = solver.model_literals()[:n]
                for i in range(0, len(lits), 15):
                    print("v " + " ".join(map(str, lits[i:i + 15])))
                print("v 0")
                code = 10
            else:
                print("s UNSATISFIABLE")
                code = 20
            if args.stats:
                st = solver.stats()
                st["seconds"] = round(time.perf_counter() - t0, 3)
                print("c " + " ".join("%s=%s" % kv for kv in st.items()))
            return code
        if args.cmd == "sudoku":
            text = _read(args.puzzle)
            if args.count:
                n, grid = models.parse_sudoku(text)
                k = len(models.sudoku_dlx(n, grid, 1000))
                print("%s%d solution(s)" % ("at least " if k == 1000 else "", k))
                return 0
            n, sol = models.solve_sudoku(text, args.engine)
            if sol is None:
                print("no solution")
                return 1
            print(models.format_sudoku(n, sol))
            return 0
        if args.cmd == "queens":
            if args.count:
                print(sum(1 for _ in models.queens_dlx(args.n)))
                return 0
            cols = models.queens_csp(args.n) if args.engine == "csp" else next(models.queens_dlx(args.n, 1), None)
            if cols is None:
                print("no solution")
                return 1
            print(models.format_queens(cols))
            return 0
        if args.cmd == "color":
            n, edges, base = _read_graph(_read(args.graph))
            if args.k:
                col = models.color_sat(n, edges, args.k, models.greedy_clique(n, edges))
                if col is None:
                    print("not %d-colourable" % args.k)
                    return 1
                k = args.k
            else:
                k, col = models.chromatic_number(n, edges)
            print("colours: %d" % k)
            for v in range(n):
                print("%d %d" % (v + base, col[v] + 1))
            return 0
        if args.cmd == "schedule":
            tasks = models.parse_tasks(_read(args.tasks))
            span, starts = models.schedule(tasks)
            if span is None:
                print("infeasible (cyclic dependencies?)")
                return 1
            print("makespan %d" % span)
            print(models.gantt(tasks, starts))
            return 0
        if args.cmd == "cover":
            primary, secondary, rows = models.parse_cover(_read(args.file))
            sols = models.exact_cover_named(primary, secondary, rows, None if args.all else 1)
            if not sols:
                print("no exact cover")
                return 1
            for s in sols:
                print(" ".join(map(str, s)))
            if args.all:
                print("%d solution(s)" % len(sols))
            return 0
        if args.cmd == "magic":
            sols = models.magic_square(args.n)
            if not sols:
                print("no solution")
                return 1
            w = len(str(args.n * args.n))
            for row in sols[0]:
                print(" ".join(str(x).rjust(w) for x in row))
            return 0
    except (ValueError, OSError) as exc:
        print("error: %s" % exc, file=sys.stderr)
        return 1
    return 0
