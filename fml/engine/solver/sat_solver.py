import z3
from pysat.solvers import Solver as SATSolver
from pysat.card import CardEnc
from typing import Optional


# Z3 → CNF tactic pipeline
_blast_tactic = z3.Then('simplify', 'bit-blast', 'tseitin-cnf')


def z3_to_dimacs(expr):
    """Convert a Z3 Boolean expression to DIMACS CNF string using bit-blast + Tseitin.

    Returns (dimacs_str, var_map, num_vars, num_clauses) where
    var_map maps Z3 variable names to DIMACS variable indices.
    """
    goal = z3.Goal()
    goal.add(expr)
    result = _blast_tactic(goal)

    if len(result) == 0:
        return "", {}, 0, 0

    # Result is a list of subgoals; take the first
    sg = result[0]

    if len(sg) == 0:
        # Empty clause list — formula is trivially SAT
        return "", {}, 0, 0

    dimacs = sg.dimacs()
    if not dimacs:
        return "", {}, 0, 0

    # Parse the header to extract var count
    lines = dimacs.strip().split('\n')
    header = lines[0] if lines else ""
    parts = header.split()
    num_vars = int(parts[2]) if len(parts) >= 3 else 0
    num_clauses = int(parts[3]) if len(parts) >= 4 else 0

    return dimacs, num_vars, num_clauses


def check_sat_z3(expr, timeout_ms=5000):
    """Check satisfiability using Z3 directly (fallback)."""
    s = z3.Solver()
    s.set("timeout", timeout_ms)
    s.add(expr)
    return s.check()


def check_sat_pysat(expr, solver_name='glucose4', timeout_ms=5000):
    """Convert a Z3 expression to CNF and check with PySAT.

    Returns 'sat', 'unsat', or 'unknown'.
    On 'sat', also returns the model (variable assignments).
    """
    dimacs, num_vars, num_clauses = z3_to_dimacs(expr)

    if num_vars == 0 and num_clauses == 0:
        # No clauses means formula is trivially SAT
        return 'sat', {}

    try:
        solver = SATSolver(name=solver_name)
        # Parse DIMACS and add clauses
        for line in dimacs.strip().split('\n'):
            line = line.strip()
            if not line or line.startswith('p ') or line.startswith('c'):
                continue
            clause = [int(x) for x in line.split() if x != '0']
            if clause:
                solver.add_clause(clause)

        result = solver.solve()
        if result:
            model = solver.get_model()
            # Convert to dict
            assignments = {}
            for lit in model:
                if lit > 0:
                    assignments[lit] = True
                else:
                    assignments[-lit] = False
            solver.delete()
            return 'sat', assignments
        else:
            solver.delete()
            return 'unsat', None
    except Exception as e:
        # Fall back to Z3 on error
        return check_sat_z3(expr, timeout_ms)


class SATBridge:
    """Bridge between Z3 expressions and PySAT solvers.

    Provides fast SAT checking for bit-precise formulas by converting
    through Z3's bit-blast + Tseitin CNF pipeline and solving with Glucose.
    """

    def __init__(self, default_solver='glucose4'):
        self.default_solver = default_solver
        self._tactic = z3.Then('simplify', 'bit-blast', 'tseitin-cnf')

    def check(self, expr, timeout_ms=5000):
        """Check a Z3 Boolean formula for satisfiability.

        Returns 'sat', 'unsat', or 'unknown'.
        """
        return check_sat_pysat(expr, self.default_solver, timeout_ms)

    def check_with_model(self, expr, timeout_ms=5000):
        """Check SAT and return model if satisfiable.

        Returns (result, model_dict) where model_dict maps
        Z3 variable names to Python int values.
        """
        result, assignments = check_sat_pysat(expr, self.default_solver, timeout_ms)
        return result, assignments

    def check_bmc_frame(self, ts, k, p_expr, timeout_ms=5000):
        """Check if a property fails at depth k (BMC step).

        Returns True if property fails at k (CEX found).
        """
        from .solver import unfold_transition_system
        from ...ir.transition_system import TransitionSystem

        state_snaps, input_snaps, solver = unfold_transition_system(ts, k)

        # Build the property check at depth k
        si = state_snaps[k]
        inp = input_snaps[k - 1] if k > 0 else None

        subst_map = [(ts.get_cur(name), si[name]) for name in ts.state_vars]
        if inp:
            subst_map.extend([(ts.get_inp(name), inp[name]) for name in ts.inputs])

        p_at_k = z3.substitute(p_expr, *subst_map)
        # Check ¬P at k
        check_expr = z3.And(solver.assertions) if hasattr(solver, 'assertions') else z3.BoolVal(True)
        check_expr = z3.simplify(z3.And(check_expr, z3.Not(p_at_k)))

        result = self.check(check_expr, timeout_ms)
        return result == 'sat'

    def minimize_unsat_core(self, clauses, timeout_ms=5000):
        """Given a list of Z3 clauses, find a minimal unsatisfiable subset.

        Uses deletion-based minimization with PySAT.
        Returns the minimal subset of clauses.
        """
        # Build combined expression
        expr = z3.And(*clauses)
        result = self.check(expr, timeout_ms)
        if result != 'unsat':
            return clauses  # Not UNSAT, return all

        # Binary search minimization
        important = list(range(len(clauses)))
        # Try removing each clause
        for i in range(len(clauses)):
            if i not in important:
                continue
            test_clauses = [clauses[j] for j in important if j != i]
            if len(test_clauses) < 2:
                break
            test_expr = z3.And(*test_clauses)
            test_result = self.check(test_expr, timeout_ms)
            if test_result == 'unsat':
                important.remove(i)

        return [clauses[i] for i in important]


# Test
if __name__ == '__main__':
    # Quick test
    x, y = z3.BitVecs('x y', 8)
    f = z3.And(x + y > 250, x < 5, y < 5)
    result, model = check_sat_pysat(f)
    print(f'Result: {result}')
    if model:
        print(f'Model has {len(model)} assignments')
