import itertools
import random
import unittest

from constraint_solver.cnf import CNF
from constraint_solver.sat import Solver, check_model, luby, parse_dimacs, solve_clauses, to_dimacs


def brute_force(n, clauses):
    for bits in itertools.product([False, True], repeat=n):
        if all(any((l > 0) == bits[abs(l) - 1] for l in c) for c in clauses):
            return True
    return False


def pigeonhole(holes):
    """holes+1 pigeons into `holes` holes: UNSAT."""
    cnf = CNF()
    x = [[cnf.var() for _ in range(holes)] for _ in range(holes + 1)]
    for p in range(holes + 1):
        cnf.add_clause(x[p])
    for h in range(holes):
        for p in range(holes + 1):
            for q in range(p + 1, holes + 1):
                cnf.add(-x[p][h], -x[q][h])
    return cnf


class TestSat(unittest.TestCase):
    def test_luby(self):
        self.assertEqual([luby(i) for i in range(1, 16)], [1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8])

    def test_random_3sat_against_brute_force(self):
        rng = random.Random(7)
        for trial in range(150):
            n = rng.randint(3, 11)
            m = rng.randint(1, int(4.6 * n))
            clauses = [[rng.choice([-1, 1]) * rng.randint(1, n) for _ in range(3)] for _ in range(m)]
            model = solve_clauses(clauses, n)
            self.assertEqual(model is not None, brute_force(n, clauses), clauses)
            if model is not None:
                self.assertTrue(check_model(clauses, model))

    def test_pigeonhole_unsat_and_stats(self):
        s = pigeonhole(5).solver()
        self.assertFalse(s.solve())
        self.assertGreater(s.stats()["conflicts"], 0)
        self.assertIsNone(pigeonhole(4).solve())

    def test_units_tautologies_and_empty(self):
        s = Solver()
        self.assertTrue(s.add_clause([1, -1]))             # tautology ignored
        self.assertTrue(s.add_clause([2]))
        self.assertTrue(s.add_clause([-2, 3]))
        self.assertTrue(s.solve())
        self.assertTrue(s.value(2) and s.value(3))
        self.assertFalse(s.add_clause([-3]))
        self.assertFalse(s.solve())
        with self.assertRaises(ValueError):
            Solver().add_clause([0])
        self.assertFalse(Solver().add_clause([]))

    def test_assumptions_and_incremental(self):
        s = Solver()
        s.add_clause([1, 2])
        s.add_clause([-1, 3])
        self.assertTrue(s.solve([-2]))
        self.assertTrue(s.value(1) and s.value(3))
        self.assertFalse(s.solve([-2, -3]))
        self.assertTrue(s.solve())                           # assumptions do not stick
        s.add_clause([-3])
        self.assertTrue(s.solve())
        self.assertTrue(s.value(2))

    def test_conflict_limit(self):
        s = pigeonhole(7).solver()
        self.assertIsNone(s.solve(max_conflicts=5))

    def test_dimacs_roundtrip(self):
        text = "c example\np cnf 3 2\n1 -3 0\n2 3\n-1 0\n"
        n, clauses = parse_dimacs(text)
        self.assertEqual((n, clauses), (3, [[1, -3], [2, 3, -1]]))
        self.assertEqual(parse_dimacs(to_dimacs(n, clauses)), (n, clauses))
        with self.assertRaises(ValueError):
            parse_dimacs("p dnf 1 1\n")

    def test_structured_sat_instance(self):
        # graph 3-colouring of a 30-cycle (even cycle, so even 2 colours suffice)
        cnf = CNF()
        n = 30
        x = [[cnf.var() for _ in range(2)] for _ in range(n)]
        for v in range(n):
            cnf.exactly_one(x[v])
            for c in range(2):
                cnf.add(-x[v][c], -x[(v + 1) % n][c])
        self.assertIsNotNone(cnf.solve())
        cnf2 = CNF()
        y = [[cnf2.var() for _ in range(2)] for _ in range(31)]
        for v in range(31):
            cnf2.exactly_one(y[v])
            for c in range(2):
                cnf2.add(-y[v][c], -y[(v + 1) % 31][c])
        self.assertIsNone(cnf2.solve())                      # odd cycle needs 3 colours


class TestCardinality(unittest.TestCase):
    def check(self, n, k, method):
        """The encoding is satisfiable exactly for assignments with the right number of true inputs."""
        for bits in itertools.product([0, 1], repeat=n):
            cnf = CNF()
            xs = cnf.vars(n)
            getattr(cnf, method)(xs, k) if method != "exactly_one" else cnf.exactly_one(xs, "sequential")
            assumptions = [x if b else -x for x, b in zip(xs, bits)]
            s = cnf.solver()
            ok = s.ok and s.solve(assumptions)
            t = sum(bits)
            expect = {"at_most_k": t <= k, "at_least_k": t >= k, "exactly_k": t == k, "exactly_one": t == 1}[method]
            self.assertEqual(bool(ok), expect, (n, k, method, bits))

    def test_encodings(self):
        for n in range(1, 6):
            for k in range(0, n + 1):
                for method in ("at_most_k", "at_least_k", "exactly_k"):
                    self.check(n, k, method)
        self.check(7, 1, "exactly_one")

    def test_gates(self):
        cnf = CNF()
        a, b = cnf.vars(2)
        y_and, y_or, y_xor = cnf.and_gate([a, b]), cnf.or_gate([a, b]), cnf.xor_gate(a, b)
        for va, vb in itertools.product([False, True], repeat=2):
            m = cnf.solve([a if va else -a, b if vb else -b])
            self.assertEqual(y_and in m, va and vb)
            self.assertEqual(y_or in m, va or vb)
            self.assertEqual(y_xor in m, va != vb)


if __name__ == "__main__":
    unittest.main()
