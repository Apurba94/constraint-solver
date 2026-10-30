"""constraint-solver: CDCL SAT, finite-domain CSP and dancing-links exact cover, with puzzle front-ends."""
from .cnf import CNF
from .csp import CSP, AllDifferent, Disjunctive, Linear, Predicate, Table
from .dlx import DLX, exact_cover
from .models import (chromatic_number, color_sat, magic_square, queens_csp, queens_dlx, schedule, solve_sudoku,
                     sudoku_csp, sudoku_dlx, sudoku_sat)
from .sat import Solver, check_model, parse_dimacs, solve_clauses, to_dimacs

__version__ = "0.1.0"
