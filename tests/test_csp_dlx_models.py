import contextlib
import io
import itertools
import os
import shutil
import tempfile
import unittest

from constraint_solver import models
from constraint_solver.cli import main
from constraint_solver.csp import CSP, Disjunctive
from constraint_solver.dlx import DLX, exact_cover

PUZZLE = """
53..7....
6..195...
.98....6.
8...6...3
4..8.3..1
7...2...6
.6....28.
...419..5
....8..79
"""
HARD = "8..........36......7..9.2...5...7.......457.....1...3...1....68..85...1..9....4.."


def run_cli(*argv):
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        rc = main(list(argv))
    return rc, out.getvalue(), err.getvalue()


class TestCsp(unittest.TestCase):
    def test_all_different_and_linear(self):
        csp = CSP()
        xs = [csp.int_var(i, 1, 3) for i in range(3)]
        csp.all_different(xs)
        self.assertEqual(csp.count(), 6)
        csp.linear([1, 1], [0, 1], "==", 3)
        sols = list(csp.solutions())
        self.assertEqual(sorted((s[0], s[1], s[2]) for s in sols), [(1, 2, 3), (2, 1, 3)])

    def test_pigeonhole_detected_by_propagation(self):
        csp = CSP()
        xs = [csp.int_var(i, 1, 3) for i in range(4)]
        csp.all_different(xs)
        self.assertIsNone(csp.solve())
        self.assertLessEqual(csp.nodes, 1)

    def test_send_more_money(self):
        csp = CSP()
        letters = "SENDMORY"
        for ch in letters:
            csp.int_var(ch, 0, 9)
        csp.domains["S"] = set(range(1, 10))
        csp.domains["M"] = set(range(1, 10))
        csp.all_different(list(letters))
        coefs = {"S": 1000, "E": 91, "N": -90, "D": 1, "M": -9000, "O": -900, "R": 10, "Y": -1}
        csp.linear(list(coefs.values()), list(coefs), "==", 0)
        s = csp.solve()
        word = lambda w: int("".join(str(s[c]) for c in w))
        self.assertEqual(word("SEND") + word("MORE"), word("MONEY"))
        self.assertEqual(word("MONEY"), 10652)
        self.assertEqual(csp.count(), 1)

    def test_predicate_table_and_minimize(self):
        csp = CSP()
        csp.int_var("x", 0, 10)
        csp.int_var("y", 0, 10)
        csp.predicate(["x", "y"], lambda x, y: x * y == 12)
        csp.table(["x", "y"], [(2, 6), (3, 4), (6, 2), (12, 1)])
        csp.int_var("s", 0, 20)
        csp.linear([1, 1, -1], ["x", "y", "s"], "==", 0)
        best, sol = csp.minimize("s")
        self.assertEqual((best, sol["x"], sol["y"]), (7, 3, 4))
        self.assertEqual(csp.domains["s"], set(range(21)))      # domain restored
        with self.assertRaises(ValueError):
            csp.linear([1], ["x"], "<", 3)
        with self.assertRaises(KeyError):
            csp.all_different(["nope"])

    def test_disjunctive(self):
        csp = CSP()
        csp.int_var("a", 0, 5)
        csp.int_var("b", 0, 5)
        csp.add(Disjunctive("a", 3, "b", 3))
        for s in csp.solutions():
            self.assertTrue(s["a"] + 3 <= s["b"] or s["b"] + 3 <= s["a"])
        self.assertEqual(csp.count(), 12)


class TestDlx(unittest.TestCase):
    def test_knuth_example(self):
        rows = [[2, 4, 5], [0, 3, 6], [1, 2, 5], [0, 3], [1, 6], [3, 4, 6]]
        sols = exact_cover(7, rows)
        self.assertEqual([sorted(s) for s in sols], [[0, 3, 4]])

    def test_secondary_columns_and_counts(self):
        d = DLX(2, 1)
        d.add_row([0, 2], "a")
        d.add_row([1, 2], "b")
        d.add_row([0], "c")
        d.add_row([1], "d")
        self.assertEqual(sorted(map(sorted, d.solutions())), [["a", "d"], ["b", "c"], ["c", "d"]])
        self.assertEqual(DLX(0).count(), 1)                     # empty cover
        self.assertEqual(exact_cover(2, [[0]]), [])
        with self.assertRaises(ValueError):
            DLX(2).add_row([5])

    def test_queens_counts(self):
        self.assertEqual([sum(1 for _ in models.queens_dlx(n)) for n in range(1, 9)], [1, 0, 0, 2, 10, 4, 40, 92])
        cols = models.queens_csp(10)
        for i, j in itertools.combinations(range(10), 2):
            self.assertNotEqual(cols[i], cols[j])
            self.assertNotEqual(abs(cols[i] - cols[j]), j - i)


class TestModels(unittest.TestCase):
    def test_sudoku_three_engines_agree(self):
        n, grid = models.parse_sudoku(PUZZLE)
        results = [models.solve_sudoku(PUZZLE, e)[1] for e in ("dlx", "sat", "csp")]
        for sol in results:
            self.assertTrue(models.check_sudoku(n, sol, grid))
        self.assertEqual(results[0], results[1])
        self.assertEqual(results[1], results[2])
        self.assertEqual(len(models.sudoku_dlx(n, grid, 10)), 1)
        self.assertIn("|", models.format_sudoku(n, results[0]))

    def test_hard_sudoku_and_sizes(self):
        n, sol = models.solve_sudoku(HARD, "dlx")
        self.assertTrue(models.check_sudoku(n, sol, models.parse_sudoku(HARD)[1]))
        n4, sol4 = models.solve_sudoku("1...\n..2.\n.3..\n...4", "sat")
        self.assertEqual(n4, 4)
        self.assertTrue(models.check_sudoku(4, sol4))
        n16, grid16 = models.parse_sudoku("." * 256)
        self.assertTrue(models.check_sudoku(16, models.sudoku_dlx(n16, grid16, 1)[0]))
        with self.assertRaises(ValueError):
            models.parse_sudoku("123")
        self.assertIsNone(models.solve_sudoku("11" + "." * 79, "csp")[1])

    def test_chromatic_numbers(self):
        petersen = [(i, (i + 1) % 5) for i in range(5)] + [(i, i + 5) for i in range(5)] + \
                   [(5 + i, 5 + (i + 2) % 5) for i in range(5)]
        k, col = models.chromatic_number(10, petersen)
        self.assertEqual(k, 3)
        self.assertTrue(models.valid_coloring(petersen, col))
        k4 = [(a, b) for a, b in itertools.combinations(range(4), 2)]
        self.assertEqual(models.chromatic_number(4, k4)[0], 4)
        self.assertIsNone(models.color_sat(4, k4, 3))
        self.assertEqual(models.chromatic_number(3, [])[0], 1)
        odd_wheel = [(0, i) for i in range(1, 6)] + [(i, i % 5 + 1) for i in range(1, 6)]
        self.assertEqual(models.chromatic_number(6, odd_wheel)[0], 4)

    def test_schedule_matches_brute_force(self):
        text = "a 3 on m1\nb 2 on m1\nc 2 on m2 after a\nd 1 on m2 after b\ne 2 after c,d\n"
        tasks = models.parse_tasks(text)
        span, starts = models.schedule(tasks)
        dur = {t["name"]: t["duration"] for t in tasks}
        for t in tasks:
            for a in t["after"]:
                self.assertGreaterEqual(starts[t["name"]], starts[a] + dur[a])
        best = None
        names = [t["name"] for t in tasks]
        for combo in itertools.product(range(8), repeat=5):
            st = dict(zip(names, combo))
            ok = all(st[t["name"]] >= st[a] + dur[a] for t in tasks for a in t["after"])
            ok = ok and all(st[x] + dur[x] <= st[y] or st[y] + dur[y] <= st[x]
                            for x, y in (("a", "b"), ("c", "d")))
            if ok:
                ms = max(st[x] + dur[x] for x in names)
                best = ms if best is None else min(best, ms)
        self.assertEqual(span, best)
        self.assertIn("#", models.gantt(tasks, starts))
        with self.assertRaises(ValueError):
            models.parse_tasks("x 1 after y\n")

    def test_cover_and_magic(self):
        primary, secondary, rows = models.parse_cover("columns: 1 2 3\nsecondary: x\nA: 1 x\nB: 2 3\nC: 1\nD: 3 x\n"
                                                      "E: 2\n")
        sols = models.exact_cover_named(primary, secondary, rows, 1)
        self.assertEqual(len(sols), 1)
        self.assertEqual(len(models.exact_cover_named(primary, secondary, rows, None)), 3)
        squares = models.magic_square(3, limit=None)
        self.assertEqual(len(squares), 8)
        for sq in squares:
            self.assertTrue(all(sum(r) == 15 for r in sq))


class TestCli(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.mkdtemp()

    def tearDown(self):
        shutil.rmtree(self.dir, ignore_errors=True)

    def _file(self, name, text):
        p = os.path.join(self.dir, name)
        with open(p, "w", encoding="utf-8") as fh:
            fh.write(text)
        return p

    def test_commands(self):
        rc, out, _ = run_cli("sat", self._file("a.cnf", "p cnf 2 2\n1 2 0\n-1 0\n"), "--stats")
        self.assertEqual(rc, 10)
        self.assertIn("v -1 2", out)
        rc, out, _ = run_cli("sat", self._file("b.cnf", "p cnf 1 2\n1 0\n-1 0\n"))
        self.assertEqual((rc, out.strip()), (20, "s UNSATISFIABLE"))
        rc, out, _ = run_cli("sudoku", self._file("s.txt", PUZZLE), "-e", "sat")
        self.assertIn("5 3 4", out)
        rc, out, _ = run_cli("sudoku", self._file("e.txt", "." * 16), "--count")
        self.assertIn("288 solution", out)
        rc, out, _ = run_cli("queens", "8", "--count")
        self.assertEqual(out.strip(), "92")
        rc, out, _ = run_cli("color", self._file("g.txt", "3 3\n1 2\n2 3\n3 1\n"))
        self.assertIn("colours: 3", out)
        rc, out, _ = run_cli("color", self._file("g2.txt", "3 3\n1 2\n2 3\n3 1\n"), "-k", "2")
        self.assertEqual(rc, 1)
        rc, out, _ = run_cli("schedule", self._file("t.txt", "x 2\ny 3 after x\n"))
        self.assertIn("makespan 5", out)
        rc, out, _ = run_cli("cover", self._file("c.txt", "columns: a b\nr1: a\nr2: b\nr3: a b\n"), "--all")
        self.assertIn("2 solution(s)", out)
        rc, out, _ = run_cli("magic", "3")
        self.assertEqual(len(out.split()), 9)
        rc, _, err = run_cli("sudoku", self._file("bad.txt", "12"))
        self.assertEqual(rc, 1)


if __name__ == "__main__":
    unittest.main()
