# constraint-solver

Three complete solving engines in pure Python, plus front-ends for the puzzles and modelling tasks
that keep appearing in contests (and in writing checkers and generators for them).

| Engine | What it is |
|---|---|
| **CDCL SAT** (`sat.py`) | two watched literals, 1-UIP learning with clause minimisation, VSIDS on a lazy heap, phase saving, Luby restarts, incremental solving under assumptions, conflict limits, DIMACS in/out |
| **CNF modelling** (`cnf.py`) | fresh variables, at-most/at-least/exactly-k (pairwise and Sinz sequential counter), Tseitin AND/OR/XOR gates |
| **Finite-domain CSP** (`csp.py`) | propagation queue to a fixpoint, `AllDifferent` (singletons, pigeonhole, hidden singles), `Linear` with bounds reasoning (`<= >= == !=`), arbitrary `Predicate` (GAC by enumeration), `Table`, `Disjunctive` resources; MRV + degree branching; enumerate, count, branch-and-bound `minimize` |
| **Dancing links** (`dlx.py`) | Knuth's Algorithm X, array based and iterative, with secondary (at most once) columns |

Front-ends (`models.py`):

* **Sudoku** of any size N = k² (4×4, 9×9, 16×16 …) with three interchangeable engines (DLX, SAT, CSP),
  solution counting for uniqueness checks.
* **N-Queens** – DLX with diagonals as secondary columns (counts 1, 0, 0, 2, 10, 4, 40, 92 …) or CSP.
* **Graph colouring** – exact chromatic number: greedy clique lower bound, DSatur upper bound, SAT with
  clique symmetry breaking in between.
* **Scheduling** – tasks with durations, precedences and machines that run one task at a time;
  minimum makespan by branch and bound, with an ASCII Gantt chart.
* **Exact cover** from a small text format, and **magic squares**.

## Usage

```bash
python -m constraint_solver sat problem.cnf --stats        # exit code 10 SAT / 20 UNSAT
python -m constraint_solver sudoku puzzle.txt --engine sat
python -m constraint_solver sudoku puzzle.txt --count
python -m constraint_solver queens 12 --count
python -m constraint_solver color graph.txt                # 'n m' then 'u v' lines
python -m constraint_solver color graph.txt -k 3
python -m constraint_solver schedule tasks.txt
python -m constraint_solver cover pentomino.txt --all
python -m constraint_solver magic 4
```

`tasks.txt`:

```
cut     3 on saw
drill   2 on drill after cut
sand    2 on saw  after cut
paint   1 after drill,sand
```

Exact cover file:

```
columns: 1 2 3 4
secondary: x
A: 1 2 x
B: 3 4
C: 1 x
```

## Library

```python
from constraint_solver import CNF, CSP, Solver, chromatic_number

cnf = CNF()
a, b, c = cnf.vars(3)
cnf.exactly_k([a, b, c], 2)
cnf.add(-a, -b)
print(cnf.solve())                     # {..} set of true variables, or None

csp = CSP()
x, y = csp.int_var("x", 0, 9), csp.int_var("y", 0, 9)
csp.linear([2, 3], [x, y], "==", 12)
csp.all_different([x, y])
print(list(csp.solutions()))
```

## Tests

```bash
python -m unittest discover -s tests -t .
```

The SAT solver is checked against brute force on 150 random 3-SAT instances around the phase
transition, on pigeonhole formulas, and through assumptions/incremental use. Every cardinality
encoding is verified on every input assignment for n ≤ 5. The three sudoku engines must agree, and
the scheduler is compared with exhaustive search.

## License

MIT
