"""Property metrics: COI, proof core, vacuity, coverage, mutation score.

Metrics provide HW-specific insight beyond pass/fail:
  - COI: which signals actually influence each property
  - Vacuity: does the antecedent ever matter?
  - Coverage: what % of state space exercises the property?
  - Proof core: minimal constraint set needed for the proof
  - Mutation: how many injected bugs does this assertion catch?
"""

import z3

from ...ir.transition_system import TransitionSystem
from .fan_in import compute_fanin_cone, _collect_var_refs


class MetricsReport:
    def __init__(self, ts):
        self.ts = ts

    def compute(self, p_expr):
        return {
            "coi": self._coi_metrics(p_expr),
            "vacuity": self._vacuity_check(p_expr),
            "coverage": self._signal_coverage(p_expr),
            "complexity": self._prop_complexity(p_expr),
        }

    # ── COI Metrics ──────────────────────────────────────────────

    def _coi_metrics(self, p_expr):
        """Cone-of-influence analysis with pruning percentages."""
        s_vars, i_vars = compute_fanin_cone(self.ts, p_expr)
        total_s = len(self.ts.state_vars)
        total_i = len(self.ts.inputs)
        _, _, next_vars = _collect_var_refs(p_expr, self.ts)

        direct_state, direct_inputs, _ = _collect_var_refs(p_expr, self.ts)

        widths = {}
        for name in s_vars:
            w = self.ts.state_vars[name].width if name in self.ts.state_vars else 0
            widths[name] = w
        for name in i_vars:
            w = self.ts.inputs[name].width if name in self.ts.inputs else 0
            widths[name] = w

        return {
            "state_vars": sorted(s_vars),
            "state_var_widths": widths,
            "n_state_vars": len(s_vars),
            "n_state_total": total_s,
            "state_pruned_pct": (1 - len(s_vars) / max(total_s, 1)) * 100,
            "inputs": sorted(i_vars),
            "n_inputs": len(i_vars),
            "n_input_total": total_i,
            "input_pruned_pct": (1 - len(i_vars) / max(total_i, 1)) * 100,
            "direct_state_vars": sorted(direct_state),
            "direct_inputs": sorted(direct_inputs),
            "next_state_refs": sorted(next_vars),
            "total_signal_bits": sum(widths.values()),
        }

    # ── Vacuity Detection ───────────────────────────────────────

    def _vacuity_check(self, p_expr):
        """Detect vacuous passes: antecedent always false in all reachable states.

        For Implication(P => Q), checks if P is ever satisfiable together with init.
        If P is always false, the property passes vacuously.
        """
        ts = self.ts
        if not z3.is_app(p_expr):
            return {"vacuous": False, "reason": "not an implication"}

        try:
            decl_name = p_expr.decl().name()
        except Exception:
            return {"vacuous": False, "reason": "unknown decl"}

        if decl_name != "Implies":
            return {"vacuous": False, "reason": "not an implication"}

        ant = p_expr.children()[0]

        s = z3.Solver()
        s.set("timeout", 2000)
        s.add(ts.init_expr)
        s.add(ts.comb_expr)
        s.add(ts.assumption_expr)
        s.add(ant)

        try:
            r = s.check()
            if r == z3.unsat:
                return {"vacuous": True, "reason": "antecedent unreachable from init"}
            if r == z3.unknown:
                return {"vacuous": None, "reason": "timeout checking antecedent"}
            return {"vacuous": False, "reason": "antecedent reachable"}
        except Exception as e:
            return {"vacuous": None, "reason": str(e)}

    # ── Signal Coverage ─────────────────────────────────────────

    def _signal_coverage(self, p_expr):
        """Estimate what fraction of signal values can exercise the property.

        Uses random sampling: inject N random assignments and count
        how many produce a non-vacuous property check.
        """
        import random

        ts = self.ts
        trials = 50
        exercised = 0

        for _ in range(trials):
            s = z3.Solver()
            s.set("timeout", 500)
            s.add(ts.init_expr)
            s.add(ts.comb_expr)
            s.add(ts.assumption_expr)

            for name in ts.inputs:
                var = ts.get_inp(name)
                w = ts.inputs[name].width
                rval = random.randint(0, (1 << w) - 1)
                s.add(var == z3.BitVecVal(rval, w))

            if z3.is_app(p_expr):
                try:
                    if p_expr.decl().name() == "Implies":
                        ant = p_expr.children()[0]
                        s.add(ant)
                    else:
                        s.add(p_expr)
                except Exception:
                    s.add(p_expr)
            else:
                s.add(p_expr)

            try:
                r = s.check()
                if r == z3.sat:
                    exercised += 1
            except Exception:
                pass

        return {
            "coverage_pct": (exercised / max(trials, 1)) * 100,
            "trials": trials,
            "exercised": exercised,
        }

    # ── Proof Core (from IC3 result) ────────────────────────────

    def extract_proof_core(self, ic3_result):
        """Extract minimal proof core from an IC3 result dict.

        Returns assumptions/constraints essential to the proof.
        """
        if not ic3_result or ic3_result.get("result") != "proved":
            return {"core_available": False}

        ts = self.ts
        core = []
        for a in ts.assumptions:
            s = z3.Solver()
            s.set("timeout", 2000)
            s.add(ts.init_expr)
            s.add(ts.comb_expr)
            s.add(ts.trans_expr)

            remaining = [x for x in ts.assumptions if x is not a]
            if remaining:
                s.add(z3.And(*remaining))
            for name in ts.state_vars:
                s.add(ts.get_cur(name) == ts.get_next(name))

            try:
                r = s.check()
                if r == z3.sat:
                    core.append(str(a))
            except Exception:
                pass

        return {
            "core_available": True,
            "essential_assumptions": core,
            "n_assumptions_removable": len(ts.assumptions) - len(core),
        }

    # ── Property Complexity ─────────────────────────────────────

    def _prop_complexity(self, p_expr):
        """Measure structural complexity of the property expression."""
        depth = [0]
        op_count = [0]
        ops = set()

        def walk(e, d):
            if e is None:
                return
            depth[0] = max(depth[0], d)
            if z3.is_app(e):
                try:
                    ops.add(e.decl().name())
                except Exception:
                    pass
            op_count[0] += 1
            for child in e.children():
                walk(child, d + 1)

        walk(p_expr, 0)
        return {
            "ast_depth": depth[0],
            "node_count": op_count[0],
            "operators": sorted(ops),
        }

    # ── Mutation Testing ────────────────────────────────────────

    def mutation_test(self, p_expr, pname, engine="sat_ic3", max_mutations=20):
        """Inject bit-flip and stuck-at mutations, measure assertion detection rate.

        Returns mutation score: fraction of injected bugs caught by the assertion.
        """
        import copy
        from ...engine.sat_ic3 import SATIC3
        from ...engine.ic3 import IC3

        ts = self.ts
        mutations = []
        rng = __import__("random").Random(42)

        candidates = list(ts.state_vars.keys()) + list(ts.inputs.keys())
        if not candidates:
            return {"mutation_score": None, "reason": "no mutable signals"}

        for _ in range(min(max_mutations, len(candidates) * 2)):
            name = rng.choice(candidates)
            mut_type = rng.choice(["bitflip", "stuck_at_0", "stuck_at_1"])
            mutations.append((name, mut_type))

        mutations = mutations[:max_mutations]
        caught = 0
        total = 0

        for name, mut_type in mutations:
            ts2 = self._clone_ts()
            self._inject_mutation(ts2, name, mut_type)
            total += 1

            try:
                if engine == "sat_ic3":
                    eng = SATIC3(ts2)
                else:
                    eng = IC3(ts2)

                result = eng._prove_property(p_expr, pname, verbose=False)
                if result.get("result") == "fail":
                    caught += 1
            except Exception:
                pass

        score = caught / max(total, 1)
        return {
            "mutation_score": round(score, 3),
            "mutations_caught": caught,
            "mutations_total": total,
            "mutations": [
                {"signal": n, "type": t}
                for n, t in mutations[:10]
            ],
        }

    def _clone_ts(self):
        import copy
        return copy.deepcopy(self.ts)

    def _inject_mutation(self, ts, signal_name, mut_type):
        """Mutate the transition system by modifying a signal's next-state or init."""
        if signal_name in ts.state_vars:
            old_expr = ts._next_state_exprs.get(signal_name)
            if old_expr is None:
                return
            if mut_type == "bitflip":
                mutant = old_expr ^ z3.BitVecVal(1, ts.state_vars[signal_name].width)
            elif mut_type == "stuck_at_0":
                mutant = z3.BitVecVal(0, ts.state_vars[signal_name].width)
            elif mut_type == "stuck_at_1":
                mutant = z3.BitVecVal(-1, ts.state_vars[signal_name].width)
            else:
                return
            ts._next_state_exprs[signal_name] = mutant

        elif signal_name in ts.inputs:
            width = ts.inputs[signal_name].width
            if mut_type == "stuck_at_0":
                ts._trans_constraints.append(
                    ts.get_inp(signal_name) == z3.BitVecVal(0, width)
                )
            elif mut_type == "stuck_at_1":
                ts._trans_constraints.append(
                    ts.get_inp(signal_name) == z3.BitVecVal(-1, width)
                )
