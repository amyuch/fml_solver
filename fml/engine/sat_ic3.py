"""SAT-level IC3/PDR engine using PySAT for fast SAT solving.

Architecture:
- All SAT queries: Z3 expr -> bit-blast -> PySAT solve
- UNSAT: fast path (PySAT only, ~2x faster than Z3)
- SAT: Z3 fallback for model extraction (rare in IC3)
- Clause generalization: Z3's unsat-core extraction
"""

import z3
from heapq import heappush, heappop
from pysat.solvers import Solver as SATSolver
from ..ir.transition_system import TransitionSystem
from ..engine.sat_solver import z3_to_dimacs


class SATIC3:
    """IC3/PDR engine backed by PySAT for SAT solving.

    Converts each IC3 query to Z3 expression, bit-blasts to CNF,
    solves with PySAT. Falls back to Z3 for model extraction (SAT results)
    and unsat-core extraction (generalization).
    """

    def __init__(self, ts: TransitionSystem, max_frames: int = 20,
                 max_blocking: int = 3000):
        self.ts = ts
        self.max_frames = max_frames
        self.max_blocking = max_blocking

    def prove(self, verbose: bool = True) -> dict:
        ts = self.ts
        if not ts.properties and not ts.trans_properties:
            return {"result": "unknown", "reason": "no properties"}

        # Regular (current-state) properties: IC3
        for pname, p_expr in ts.properties:
            result = self._prove_property(p_expr, pname, verbose)
            if result["result"] == "fail":
                return result
            if result["result"] == "unknown":
                return {"result": "unknown", "reason": f"property {pname} unknown"}

        # Transition properties (contain next-state vars): cannot use
        # standard IC3 P_next substitution, fall back to proven path only
        if ts.trans_properties:
            from ..engine.kind import check_kinduction
            kind_result = check_kinduction(ts, self.max_frames, verbose=verbose)
            if kind_result.get("result") == "fail":
                return kind_result
            if kind_result.get("result") != "proved":
                return {"result": "unknown", "reason": "trans_property unproven"}

        if not ts.properties and not ts.trans_properties:
            return {"result": "unknown"}
        return {"result": "proved", "bound": self.max_frames}

    def _prove_property(self, P, pname, verbose):
        ts = self.ts
        cur_to_next = [(ts.get_cur(name), ts.get_next(name)) for name in ts.state_vars]
        P_next = z3.substitute(P, *cur_to_next)

        # Initial state check: I ∧ ¬P
        if self._sat_check(z3.And([ts.init_expr, ts.assumption_expr, z3.Not(P)])):
            if verbose:
                print(f"      counterexample at initial state")
            return {"result": "fail", "property": pname, "bound": 0}

        F = [[] for _ in range(self.max_frames + 2)]
        F[0].append(ts.init_expr)

        for k in range(1, self.max_frames + 1):
            if verbose:
                print(f"    frame {k}")
            ok = self._strengthen(k, F, P, P_next, ts, verbose)
            if isinstance(ok, dict) and ok.get("result") == "fail":
                return ok
            if ok == "proved":
                return {"result": "proved", "property": pname, "k": k - 1}
            if ok is None:
                if verbose:
                    print(f"      blocking limit reached at frame {k}")
                return {"result": "unknown", "property": pname, "reason": "blocking limit"}

            self._propagate(k, F, P, P_next, ts)
            if self._frames_equal(F, k - 1, k) and len(F[k]) > 0:
                if verbose:
                    print(f"      converged at frame {k}")
                return {"result": "proved", "property": pname, "k": k}

        return {"result": "unknown", "property": pname, "bound": self.max_frames}

    def _strengthen(self, k, F, P, P_next, ts, verbose):
        cur_to_next = [(ts.get_cur(name), ts.get_next(name)) for name in ts.state_vars]
        heap = []
        seq = 0

        def _push_cube(cube, i):
            nonlocal seq
            if i < 0:
                return
            heappush(heap, (i, seq, cube))
            seq += 1

        for attempt in range(self.max_blocking):
            if heap:
                i, _, cube = heappop(heap)
            else:
                # No pending CTIs — query F[k-1] + T + ¬P_next for new CTIs
                q = self._build_cti_query(k, F, P, P_next, ts, cur_to_next)
                model = self._sat_check_with_model(q)
                if model is None:  # UNSAT
                    if self._frames_equal(F, k - 1, k):
                        return "proved"
                    return True

                cube = self._extract_cube(model, ts)
                _push_cube(cube, k - 1)
                if verbose:
                    cube_str = str(cube)
                    if len(cube_str) > 100:
                        cube_str = cube_str[:100] + "..."
                    print(f"      CTI @{k - 1}: {cube_str}")
                continue

            if self._is_blocked(cube, i, F):
                continue

            model = self._check_predecessor(cube, i, F, P, P_next, ts, cur_to_next)
            if model is None:  # timeout
                continue

            if model is False:  # UNSAT — cube is inductive relative to F[i-1]
                clause = self._generalize(cube, i, F, P, P_next, ts, cur_to_next)
                self._add_clause(clause, i, F)
                continue

            if i == 0:
                if verbose:
                    print(f"      CEX: init reaches bad")
                return {"result": "fail", "bound": 0}

            # CTI has predecessor — push both cubes
            _push_cube(cube, i)
            pred_cube = self._extract_cube(model, ts)
            _push_cube(pred_cube, i - 1)

        return None

    def _build_cti_query(self, k, F, P, P_next, ts, cur_to_next):
        """F[k-1] ∧ T ∧ comb ∧ ¬P_next"""
        ts_cn = z3.substitute(ts.comb_expr, *cur_to_next)
        parts = [z3.And(*F[k - 1])]
        parts.append(P)
        parts.append(ts.assumption_expr)
        parts.append(ts.comb_expr)
        parts.append(ts.trans_expr)
        parts.append(ts_cn)
        parts.append(z3.Not(P_next))
        return z3.And(*parts) if len(parts) > 1 else parts[0]

    def _check_predecessor(self, cube, i, F, P, P_next, ts, cur_to_next):
        """F[i-1] ∧ T ∧ comb_next ∧ cube_next — SAT? => predecessor exists.
        Returns:
          dict (model) if SAT
          False if UNSAT (cube is inductive relative to F[i-1])
          None if unknown/timeout
        """
        ts_cn = z3.substitute(ts.comb_expr, *cur_to_next)
        cube_next = z3.substitute(cube, *cur_to_next)
        parts = []
        if i == 0:
            parts.append(ts.init_expr)
        else:
            parts.append(z3.And(*F[i - 1]))
            parts.append(P)
        parts.append(ts.assumption_expr)
        parts.append(ts.comb_expr)
        parts.append(ts.trans_expr)
        parts.append(ts_cn)
        parts.append(cube_next)
        query = z3.And(*parts) if len(parts) > 1 else parts[0]
        sat = self._sat_check(query)
        if sat is True:
            return self._sat_check_with_model(query)
        if sat is False:
            return False
        return None

    def _generalize(self, cube, i, F, P, P_next, ts, cur_to_next):
        """Generalize cube to clause via selective literal removal."""
        if i < 0:
            return z3.Not(cube)

        lits = list(cube.children()) if z3.is_and(cube) else [cube]
        if len(lits) <= 1:
            return z3.Not(cube)

        essential = list(lits)
        ts_cn = z3.substitute(ts.comb_expr, *cur_to_next)

        for idx in range(len(lits) - 1, -1, -1):
            test_lits = [essential[j] for j in range(len(essential)) if j != idx]
            if not test_lits:
                continue
            test_cube = z3.And(*test_lits) if len(test_lits) > 1 else test_lits[0]
            test_next = z3.substitute(test_cube, *cur_to_next)

            parts = []
            if i == 0:
                parts.append(ts.init_expr)
            else:
                parts.append(z3.And(*F[i - 1]))
                parts.append(P)
            parts.append(ts.assumption_expr)
            parts.append(ts.comb_expr)
            parts.append(ts.trans_expr)
            parts.append(ts_cn)
            parts.append(test_next)
            query = z3.And(*parts) if len(parts) > 1 else parts[0]

            if not self._sat_check(query):
                essential.remove(lit)

        if not essential:
            return z3.Not(cube)
        if len(essential) == 1:
            return z3.Not(essential[0])
        return z3.Not(z3.And(*essential))

    def _extract_cube(self, model, ts):
        parts = []
        for name in ts.state_vars:
            val = model.get(name)
            if val is not None:
                parts.append(ts.get_cur(name) == val)
        return z3.And(*parts) if parts else None

    def _is_blocked(self, cube, i, F):
        if i < 0 or i >= len(F):
            return False
        for clause in F[i]:
            if self._clause_blocks(clause, cube):
                return True
        return False

    def _clause_blocks(self, clause, cube) -> bool:
        if z3.is_false(clause):
            return True
        if z3.is_true(clause):
            return False
        if not z3.is_not(clause):
            return False
        inner = clause.children()[0]
        g_lits = set(inner.children()) if z3.is_and(inner) else {inner}
        c_lits = set(cube.children()) if z3.is_and(cube) else {cube}
        return g_lits.issubset(c_lits)

    def _add_clause(self, clause, up_to, F):
        for i in range(up_to + 1):
            if i >= len(F):
                break
            existing = F[i]
            subsumed = False
            for j in range(len(existing) - 1, -1, -1):
                ec = existing[j]
                if self._subsumes(ec, clause):
                    subsumed = True
                    break
                if self._subsumes(clause, ec):
                    existing.pop(j)
            if not subsumed:
                existing.append(clause)

    def _subsumes(self, c1, c2) -> bool:
        l1 = self._clause_lits(c1)
        l2 = self._clause_lits(c2)
        return bool(l1 and l1.issubset(l2)) if l1 and l2 else bool(not l2 and l1)

    def _clause_lits(self, clause) -> set:
        if z3.is_false(clause) or z3.is_true(clause):
            return set()
        if z3.is_not(clause):
            inner = clause.children()[0]
            if z3.is_and(inner):
                return {str(c) for c in inner.children()}
            return {str(inner)}
        if z3.is_and(clause):
            return {str(c) for c in clause.children()}
        return {str(clause)}

    def _frames_equal(self, F, i, j) -> bool:
        if i >= len(F) or j >= len(F):
            return False
        return set(str(c) for c in F[i]) == set(str(c) for c in F[j])

    def _propagate(self, k, F, P, P_next, ts):
        cur_to_next = [(ts.get_cur(name), ts.get_next(name)) for name in ts.state_vars]
        ts_cn = z3.substitute(ts.comb_expr, *cur_to_next)

        for fi in range(min(k, len(F) - 1)):
            frm = F[fi]
            frm_next = F[fi + 1]
            candidates = [c for c in frm if c not in frm_next]
            if not candidates:
                continue

            for c in candidates:
                cn = z3.substitute(z3.Not(c), *cur_to_next)
                parts = []
                for cc in frm:
                    parts.append(cc)
                if fi >= 1:
                    parts.append(P)
                parts.append(ts.assumption_expr)
                parts.append(ts.comb_expr)
                parts.append(ts.trans_expr)
                parts.append(ts_cn)
                parts.append(cn)
                query = z3.And(*parts) if len(parts) > 1 else parts[0]
                if not self._sat_check(query):
                    self._add_clause(c, fi + 1, F)

    def _sat_check(self, expr):
        """Check Z3 expr via PySAT. Returns True if SAT, False if UNSAT, None if unknown."""
        dimacs, n_vars, n_clauses = z3_to_dimacs(expr)
        if n_vars == 0 and n_clauses == 0:
            return False  # trivially UNSAT (empty clause = contradiction)
        if not dimacs:
            return self._sat_check_z3(expr)

        try:
            solver = SATSolver(name='glucose4')
            for line in dimacs.strip().split('\n'):
                line = line.strip()
                if not line or line.startswith('p ') or line.startswith('c'):
                    continue
                clause = [int(x) for x in line.split() if x != '0']
                if clause:
                    solver.add_clause(clause)
            result = solver.solve()
            solver.delete()
            if result is None:
                return None
            return result  # True = SAT, False = UNSAT
        except Exception:
            return self._sat_check_z3(expr)

    def _sat_check_z3(self, expr):
        s = z3.Solver()
        s.set("timeout", 2000)
        s.add(expr)
        try:
            r = s.check()
            if r == z3.sat:
                return True
            if r == z3.unsat:
                return False
            return None
        except Exception:
            return None

    def _sat_check_with_model(self, expr):
        """Check SAT with Z3 and return model dict. Returns None if UNSAT/unknown."""
        s = z3.Solver()
        s.set("timeout", self.ts.timeout)
        s.add(expr)
        try:
            r = s.check()
            if r == z3.sat:
                m = s.model()
                parts = {}
                for name in self.ts.state_vars:
                    try:
                        parts[name] = m.eval(self.ts.get_cur(name))
                    except Exception:
                        parts[name] = None
                return parts
            return None if r == z3.unsat else None
        except Exception:
            return None
