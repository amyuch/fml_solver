import z3
from pysat.solvers import Solver as SATSolver
from ...ir.transition_system import TransitionSystem


_blast = z3.Then('simplify', 'bit-blast', 'tseitin-cnf')


def _expr_to_dimacs(expr):
    """Convert a Z3 expression to DIMACS CNF.

    Returns (dimacs_str, num_vars, num_clauses) or (None, 0, 0) on failure.
    """
    if expr is None or z3.is_true(expr) or z3.is_false(expr):
        return None, 0, 0

    try:
        goal = z3.Goal()
        goal.add(expr)
        result = _blast(goal)
        if len(result) == 0:
            return None, 0, 0
        sg = result[0]
        if len(sg) == 0:
            return None, 0, 0
        dimacs = sg.dimacs()
        if not dimacs:
            return None, 0, 0
        lines = dimacs.strip().split('\n')
        header = lines[0]
        parts = header.split()
        n_vars = int(parts[2]) if len(parts) >= 3 else 0
        n_clauses = int(parts[3]) if len(parts) >= 4 else 0
        return dimacs, n_vars, n_clauses
    except Exception:
        return None, 0, 0


def _parse_dimacs_clauses(dimacs):
    """Parse a DIMACS string into a list of clauses (list of lists of ints)."""
    clauses = []
    for line in dimacs.strip().split('\n'):
        line = line.strip()
        if not line or line.startswith('p ') or line.startswith('c'):
            continue
        clause = [int(x) for x in line.split() if x != '0']
        if clause:
            clauses.append(clause)
    return clauses


class CNFContext:
    """Pre-bit-blats a transition system to CNF and provides fast SAT queries.

    The transition relation T, init constraint, comb constraints, and property
    negations are bit-blasted to CNF once. Per-query clauses (cube, frame
    clauses) can be added dynamically.
    """

    def __init__(self, ts, solver_name='glucose4'):
        self.ts = ts
        self.solver_name = solver_name

        # Pre-blast components
        self._trans_clauses = []
        self._init_clauses = []
        self._comb_clauses = []
        self._latch_map = {}  # state_var -> (cur_dv, next_dv) DIMACS var indices

        self._build()

    def _build(self):
        """Pre-bit-blast the transition relation components."""
        # Bit-blast trans_expr
        te = self.ts.trans_expr
        if te is not None and not z3.is_true(te):
            d, _, _ = _expr_to_dimacs(te)
            if d:
                self._trans_clauses = _parse_dimacs_clauses(d)

        # Bit-blast comb constraints
        ce = self.ts.comb_expr
        if ce is not None and not z3.is_true(ce):
            d, _, _ = _expr_to_dimacs(ce)
            if d:
                self._comb_clauses = _parse_dimacs_clauses(d)

        # Bit-blast init constraints (separately, for init-only queries)
        ie = self.ts.init_expr
        if ie is not None and not z3.is_true(ie):
            d, _, _ = _expr_to_dimacs(ie)
            if d:
                self._init_clauses = _parse_dimacs_clauses(d)

    def check_cube_inductive(self, cube_expr, timeout_ms=5000):
        """Check if a cube is inductive: cube ∧ T ∧ ¬P → next P.

        Returns 'sat' (cube is NOT inductive — counterexample found),
                'unsat' (cube IS inductive), or 'unknown'.
        """
        p_exprs = [e for _, e in self.ts.properties]
        if not p_exprs:
            return 'unknown'

        # Build: cube ∧ T ∧ ¬P_next
        p_not_exprs = [z3.Not(self.ts.substitute_cur_with_next(p)) for p in p_exprs]
        query = z3.And([cube_expr, self.ts.trans_expr] + p_not_exprs)
        return self._check(query, timeout_ms)

    def check_cube_in_frame(self, cube_expr, frame_clauses, timeout_ms=5000):
        """Check if cube can be reached from frame in 1 step: frame ∧ cube_next ∧ T.

        Returns 'sat' (cube is reachable), 'unsat' (cube is blocked), 'unknown'.
        """
        # Build: frame_clauses ∧ cube_next ∧ T
        frame_and = z3.And(frame_clauses) if frame_clauses else z3.BoolVal(True)

        # cube_next is the cube with cur->next substitution
        cube_next = z3.substitute(
            cube_expr,
            *[(self.ts.get_cur(name), self.ts.get_next(name))
              for name in self.ts.state_vars]
        ) if cube_expr is not None else z3.BoolVal(True)

        query = z3.And([frame_and, cube_next, self.ts.trans_expr])
        return self._check(query, timeout_ms)

    def _check(self, expr, timeout_ms):
        """Bit-blast expression and solve with PySAT."""
        # Bit-blast the per-query part
        d, n_vars, n_clauses = _expr_to_dimacs(expr)
        if d is None:
            return 'unknown'

        query_clauses = _parse_dimacs_clauses(d)

        # Merge with pre-blasted clauses
        all_clauses = self._trans_clauses + self._comb_clauses + query_clauses
        if not all_clauses:
            return 'sat'

        try:
            solver = SATSolver(name=self.solver_name)
            for clause in all_clauses:
                solver.add_clause(clause)
            result = solver.solve()
            solver.delete()
            return 'sat' if result else 'unsat'
        except Exception:
            return 'unknown'

    def check_sat(self, expr, timeout_ms=5000):
        """General SAT check with PySAT fallback to Z3."""
        d, _, _ = _expr_to_dimacs(expr)
        if d is not None:
            clauses = _parse_dimacs_clauses(d)
            if clauses:
                try:
                    solver = SATSolver(name=self.solver_name)
                    for c in clauses:
                        solver.add_clause(c)
                    result = solver.solve()
                    solver.delete()
                    return 'sat' if result else 'unsat'
                except Exception:
                    pass
        # Fallback
        s = z3.Solver()
        s.set("timeout", timeout_ms)
        s.add(expr)
        r = s.check()
        return 'sat' if r == z3.sat else 'unsat' if r == z3.unsat else 'unknown'
