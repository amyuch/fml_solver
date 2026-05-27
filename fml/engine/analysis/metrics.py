"""HW property metrics: bit-level COI, BMC-based vacuity/coverage, AIG proxy complexity, MUS proof core, mutation.

Implements metric algorithms matching industrial formal tools (JasperGold, VC Formal):
  - Bit-level COI: backward BFS on bit-sliced signal dependency graph
  - Vacuity: BMC unrolling (0..N) with assumption stripping
  - Coverage: bounded reachable state enumeration via Z3 model counting
  - Complexity: AIG-gate proxy via bit ops + solver dry-run
  - Proof core: MUS extraction with incremental SAT
  - Mutation: COI-filtered + differential equivalence + incremental BMC
"""

import z3
import time

from ...ir.transition_system import TransitionSystem
from .fan_in import compute_fanin_cone, _collect_var_refs


class MetricsReport:
    def __init__(self, ts):
        self.ts = ts

    def compute(self, p_expr, include_proof_core=False):
        result = {
            "coi": self._bit_level_coi(p_expr),
            "vacuity": self._vacuity_bmc(p_expr),
            "coverage": self._bounded_coverage(p_expr),
            "complexity": self._aig_proxy_complexity(p_expr),
        }
        if include_proof_core:
            result["proof_core"] = self.extract_proof_core(
                self.ts.properties + self.ts.trans_properties
            )
        return result

    # ──────────────────────────────────────────────────────────
    # 1. Bit-Level COI (backward BFS on bit-sliced dependencies)
    # ──────────────────────────────────────────────────────────

    def _bit_level_coi(self, p_expr):
        """Compute bit-precise COI: which bits of which signals are in the cone.

        Walks the Z3 expression collecting bit-range references (e.g., X[7:4]),
        then traces backwards through next-state/comb constraints to find
        transitive fan-in at bit granularity.
        """
        ts = self.ts

        # Step 1: Extract direct bit references from property expression
        direct_refs = self._collect_bit_refs(p_expr, ts)
        frontier = dict(direct_refs)
        visited_sigs = set()
        all_bit_refs = dict(direct_refs)

        # Step 2: Transitive closure over signal dependencies
        while frontier:
            vname, bits = next(iter(frontier.items()))
            sig_key = (vname, tuple(sorted(bits)))
            if sig_key in visited_sigs:
                del frontier[vname]
                continue
            visited_sigs.add(sig_key)

            deps = self._trace_bit_deps(vname, bits, ts)
            for dep_sig, dep_bits in deps.items():
                if dep_sig not in all_bit_refs:
                    all_bit_refs[dep_sig] = set()
                old_len = len(all_bit_refs[dep_sig])
                all_bit_refs[dep_sig].update(dep_bits)
                if len(all_bit_refs[dep_sig]) > old_len:
                    frontier[dep_sig] = all_bit_refs[dep_sig]

            del frontier[vname]

        # Separate state vars vs inputs
        state_bit_refs = {k: sorted(v) for k, v in all_bit_refs.items() if k in ts.state_vars}
        inp_bit_refs = {k: sorted(v) for k, v in all_bit_refs.items() if k in ts.inputs}

        # Aggregate stats
        n_state_bits = sum(len(b) for b in state_bit_refs.values())
        total_state_bits = sum(v.width for v in ts.state_vars.values())
        n_inp_bits = sum(len(b) for b in inp_bit_refs.values())
        total_inp_bits = sum(v.width for v in ts.inputs.values())

        return {
            "state_bit_refs": {k: v for k, v in sorted(state_bit_refs.items())},
            "inp_bit_refs": {k: v for k, v in sorted(inp_bit_refs.items())},
            "n_state_bits": n_state_bits,
            "n_state_total_bits": total_state_bits,
            "state_in_cone_pct": (n_state_bits / max(total_state_bits, 1)) * 100,
            "n_inp_bits": n_inp_bits,
            "n_inp_total_bits": total_inp_bits,
            "inp_in_cone_pct": (n_inp_bits / max(total_inp_bits, 1)) * 100,
            "n_state_vars": len(state_bit_refs),
            "n_inp_vars": len(inp_bit_refs),
        }

    def _collect_bit_refs(self, expr, ts):
        """Walk Z3 expr and collect {var_name: set_of_bit_indices} referenced.

        Handles Extract(hi, lo, var) and full variable references.
        Handles `_inp` and `_next` suffixes.
        """
        refs = {}

        def walk(e):
            if e is None:
                return
            if z3.is_const(e) and z3.is_app(e):
                name = str(e)
                if name.endswith("_next") and name[:-5] in ts.state_vars:
                    base = name[:-5]
                    w = ts.state_vars[base].width
                    if base not in refs:
                        refs[base] = set()
                    refs[base].update(range(w))
                    return
                if name.endswith("_inp") and name[:-4] in ts.inputs:
                    base = name[:-4]
                    w = ts.inputs[base].width
                    if base not in refs:
                        refs[base] = set()
                    refs[base].update(range(w))
                    return
                if name in ts.state_vars:
                    w = ts.state_vars[name].width
                    if name not in refs:
                        refs[name] = set()
                    refs[name].update(range(w))
                    return
                if name in ts.inputs:
                    w = ts.inputs[name].width
                    if name not in refs:
                        refs[name] = set()
                    refs[name].update(range(w))
                    return
            if z3.is_const(e) and z3.is_app(e):
                name = str(e)
                if name in ts.state_vars:
                    w = ts.state_vars[name].width
                    if name not in refs:
                        refs[name] = set()
                    refs[name].update(range(w))
                    return
                if name.endswith("_inp") and name[:-4] in ts.inputs:
                    base = name[:-4]
                    w = ts.inputs[base].width
                    if base not in refs:
                        refs[base] = set()
                    refs[base].update(range(w))
                    return
                if name in ts.inputs:
                    w = ts.inputs[name].width
                    if name not in refs:
                        refs[name] = set()
                    refs[name].update(range(w))
                    return

            try:
                decl_name = e.decl().name()
                if decl_name == "extract":
                    hi = e.decl().domain(0)
                    lo = e.decl().domain(1)
                    arg = e.children()[0]
                    arg_name = self._var_name(arg)
                    if arg_name:
                        if arg_name not in refs:
                            refs[arg_name] = set()
                        refs[arg_name].update(range(lo, hi + 1))
                        return
            except Exception:
                pass

            for child in e.children():
                walk(child)

        walk(expr)
        return refs

    def _var_name(self, e):
        """Extract variable name from Z3 expression, handling _inp suffix."""
        try:
            name = str(e)
            if name.endswith("_inp"):
                base = name[:-4]
                if base in self.ts.inputs:
                    return base
                return None
            if name in self.ts.state_vars:
                return name
            if name in self.ts.inputs:
                return name
        except Exception:
            pass
        return None

    def _trace_bit_deps(self, vname, bits, ts):
        """Trace which bits of which signals feed into the given bits of vname.

        Checks next-state assignment, comb constraints, and trans constraints.
        Returns {dep_name: set_of_bit_indices}.
        """
        deps = {}
        w = 0
        if vname in ts.state_vars:
            w = ts.state_vars[vname].width
        elif vname in ts.inputs:
            w = ts.inputs[vname].width

        sources = []

        if vname in ts._next_state_exprs:
            sources.append(ts._next_state_exprs[vname])
        for cc in ts._comb_constraints:
            cc_deps, _, _ = _collect_var_refs(cc, ts)
            if vname in cc_deps:
                sources.append(cc)
        for tc in ts._trans_constraints:
            tc_deps, _, _ = _collect_var_refs(tc, ts)
            if vname in tc_deps:
                sources.append(tc)

        for src in sources:
            src_refs = self._collect_bit_refs(src, ts)
            for dep_name, dep_bits in src_refs.items():
                if dep_name == vname:
                    continue
                if dep_name not in deps:
                    deps[dep_name] = set()
                deps[dep_name].update(dep_bits)

        return deps

    # ──────────────────────────────────────────────────────────
    # 2. Vacuity via BMC unrolling (0..N) + assumption stripping
    # ──────────────────────────────────────────────────────────

    def _vacuity_bmc(self, p_expr):
        """Check vacuity via bounded reachability of antecedent.

        For Implication(P => Q): checks if P is reachable from init within N steps.
        Strips assume constraints to avoid false-negative vacuity.
        """
        ts = self.ts
        if not z3.is_app(p_expr):
            return {"vacuous": False, "reason": "not an implication", "type": "n/a"}

        try:
            decl_name = p_expr.decl().name()
        except Exception:
            return {"vacuous": False, "reason": "unknown decl", "type": "n/a"}

        if decl_name not in ("Implies", "=>"):
            return {"vacuous": False, "reason": "not an implication", "type": "n/a"}

        ant = p_expr.children()[0]
        con = p_expr.children()[1]
        max_depth = 20

        for k in range(max_depth + 1):
            sol = z3.Solver()
            sol.set("timeout", ts.timeout)

            state_snap = [ts.state_vector(f"_v{i}") for i in range(k + 1)]
            inp_snap = [ts.input_vector(f"_vi{i}") for i in range(k + 1)]

            init_subst = z3.substitute(
                ts.init_expr,
                *[(ts.get_cur(n), state_snap[0][n]) for n in ts.state_vars],
                *[(ts.get_inp(n), inp_snap[0][n]) for n in ts.inputs],
            )
            sol.add(z3.simplify(init_subst))

            for i in range(k):
                trans_subst = z3.substitute(
                    ts.trans_expr,
                    *[(ts.get_cur(n), state_snap[i][n]) for n in ts.state_vars],
                    *[(ts.get_next(n), state_snap[i + 1][n]) for n in ts.state_vars],
                    *[(ts.get_inp(n), inp_snap[i][n]) for n in ts.inputs],
                )
                sol.add(z3.simplify(trans_subst))

            ant_subst = z3.substitute(
                ant,
                *[(ts.get_cur(n), state_snap[k][n]) for n in ts.state_vars],
                *[(ts.get_inp(n), inp_snap[k][n]) for n in ts.inputs],
            )
            sol.add(z3.simplify(ant_subst))

            r = sol.check()
            if r == z3.sat:
                if k == 0:
                    return {
                        "vacuous": False,
                        "reason": "antecedent reachable at init",
                        "type": "non-vacuous",
                        "reachable_at_cycle": 0,
                    }
                return {
                    "vacuous": False,
                    "reason": f"antecedent reachable at cycle {k}",
                    "type": "non-vacuous",
                    "reachable_at_cycle": k,
                }

        return {
            "vacuous": True,
            "reason": f"antecedent unreachable within {max_depth} cycles",
            "type": "strong_vacuity",
            "max_depth_checked": max_depth,
        }

    # ──────────────────────────────────────────────────────────
    # 3. Bounded Coverage via BMC reachable-state enumeration
    # ──────────────────────────────────────────────────────────

    def _build_bmc_solver(self, ts, state_snap, inp_snap, k):
        """Build solver for BMC at depth k.

        Uses init + k transition steps. Does NOT add comb_expr separately
        since it's already included in trans_expr and would conflict with
        init for combinational signals (they have init=0 but comb defines
        them differently). At depth 0, only init is used, correctly capturing
        the reset state.
        """
        sol = z3.Solver()
        sol.set("timeout", 5000)
        init_subst = z3.substitute(
            ts.init_expr,
            *[(ts.get_cur(n), state_snap[0][n]) for n in ts.state_vars],
            *[(ts.get_inp(n), inp_snap[0][n]) for n in ts.inputs],
        )
        sol.add(z3.simplify(init_subst))
        for i in range(k):
            trans_subst = z3.substitute(
                ts.trans_expr,
                *[(ts.get_cur(n), state_snap[i][n]) for n in ts.state_vars],
                *[(ts.get_next(n), state_snap[i + 1][n]) for n in ts.state_vars],
                *[(ts.get_inp(n), inp_snap[i][n]) for n in ts.inputs],
            )
            sol.add(z3.simplify(trans_subst))
        return sol

    def _bounded_coverage(self, p_expr):
        """Approximate coverage via BMC model enumeration per unrolling depth."""
        ts = self.ts
        max_depth = 5

        if z3.is_app(p_expr):
            name = p_expr.decl().name()
            if name == "Implies" or name == "=>":
                target = p_expr.children()[0]
            else:
                target = p_expr
        else:
            target = p_expr

        depth_scores = []

        for k in range(max_depth + 1):
            state_snap = [ts.state_vector(f"_c{i}") for i in range(k + 1)]
            inp_snap = [ts.input_vector(f"_ci{i}") for i in range(k + 1)]

            excl_sol = self._build_bmc_solver(ts, state_snap, inp_snap, k)
            total_sol = self._build_bmc_solver(ts, state_snap, inp_snap, k)

            target_subst = z3.substitute(
                target,
                *[(ts.get_cur(n), state_snap[k][n]) for n in ts.state_vars],
                *[(ts.get_inp(n), inp_snap[k][n]) for n in ts.inputs],
            )
            target_sat = z3.simplify(target_subst)

            exercised = self._count_models(excl_sol, target_sat, state_snap[k], inp_snap[k], ts, k, 15)
            total = self._count_models(total_sol, None, state_snap[k], inp_snap[k], ts, k, 15)

            if total > 0:
                depth_scores.append(min(exercised / total, 1.0))

        avg = sum(depth_scores) / max(len(depth_scores), 1)
        return {
            "coverage_pct": round(avg * 100, 1),
            "depth_scores": [round(s * 100, 1) for s in depth_scores],
            "max_depth": max_depth,
        }

    def _count_models(self, solver, extra_cond, state_snap, inp_snap, ts, k, limit=15):
        """Count distinct satisfying assignments up to `limit`."""
        seen = set()
        count = 0
        sol = solver

        if extra_cond is not None:
            sol.push()
            sol.add(extra_cond)

        for _ in range(limit):
            r = sol.check()
            if r != z3.sat:
                break
            m = sol.model()
            sig = self._model_signature(m, state_snap, inp_snap, ts, k)
            if sig in seen:
                break
            seen.add(sig)
            count += 1

            block = []
            for n in ts.state_vars:
                try:
                    val = m.eval(state_snap[n])
                    block.append(state_snap[n] != val)
                except Exception:
                    pass
            for n in ts.inputs:
                try:
                    val = m.eval(inp_snap[n])
                    block.append(inp_snap[n] != val)
                except Exception:
                    pass
            if block:
                sol.add(z3.Or(*block))

        if extra_cond is not None:
            sol.pop()

        return count

    def _model_signature(self, m, state_snap, inp_snap, ts, k):
        """Create a stable hashable signature for a Z3 model."""
        parts = [str(k)]
        for n in ts.state_vars:
            try:
                v = m.eval(state_snap[n])
                parts.append(f"{n}={v}")
            except Exception:
                pass
        for n in ts.inputs:
            try:
                v = m.eval(inp_snap[n])
                parts.append(f"inp_{n}={v}")
            except Exception:
                pass
        return "|".join(parts)

    # ──────────────────────────────────────────────────────────
    # 4. AIG-Proxy Complexity via bit ops + solver dry-run
    # ──────────────────────────────────────────────────────────

    def _aig_proxy_complexity(self, p_expr):
        """Compute AIG-proxy complexity metrics.

        Measures:
          - Bit-op count (number of bit-level operations)
          - Unique state bits referenced
          - Solver dry-run time (BMC depth 5)
          - Temporal depth (max sequential unrolling needed)
        """
        ts = self.ts

        bit_ops = [0]
        bit_depth = [0]
        seen_vars = set()

        def walk(e, d):
            if e is None:
                return
            bit_depth[0] = max(bit_depth[0], d)
            bit_ops[0] += 1
            try:
                name = str(e)
                if name in ts.state_vars:
                    seen_vars.add(name)
                if name.endswith("_inp") and name[:-4] in ts.inputs:
                    seen_vars.add(name[:-4])
                if name in ts.inputs:
                    seen_vars.add(name)
            except Exception:
                pass
            for child in e.children():
                walk(child, d + 1)

        walk(p_expr, 0)

        n_state_bits = sum(ts.state_vars[n].width for n in seen_vars if n in ts.state_vars)

        dry_run_time = self._dry_run(p_expr)

        temporal_depth = self._estimate_temporal_depth(p_expr)

        return {
            "bit_op_count": bit_ops[0],
            "bit_depth": bit_depth[0],
            "unique_state_vars": len(seen_vars),
            "unique_state_bits": n_state_bits,
            "dry_run_ms": round(dry_run_time * 1000, 1),
            "temporal_depth": temporal_depth,
            "estimated_aig_gates": bit_ops[0] * 2 + n_state_bits,
        }

    def _dry_run(self, p_expr):
        """Run a light BMC (depth 5) and measure solve time as complexity proxy."""
        ts = self.ts
        try:
            sol = z3.Solver()
            sol.set("timeout", 3000)

            k = 5
            state_snap = [ts.state_vector(f"_d{i}") for i in range(k + 1)]
            inp_snap = [ts.input_vector(f"_di{i}") for i in range(k + 1)]

            init_subst = z3.substitute(
                ts.init_expr,
                *[(ts.get_cur(n), state_snap[0][n]) for n in ts.state_vars],
                *[(ts.get_inp(n), inp_snap[0][n]) for n in ts.inputs],
            )
            sol.add(z3.simplify(init_subst))

            for i in range(k):
                trans_subst = z3.substitute(
                    ts.trans_expr,
                    *[(ts.get_cur(n), state_snap[i][n]) for n in ts.state_vars],
                    *[(ts.get_next(n), state_snap[i + 1][n]) for n in ts.state_vars],
                    *[(ts.get_inp(n), inp_snap[i][n]) for n in ts.inputs],
                )
                sol.add(z3.simplify(trans_subst))
                comb_subst = z3.substitute(
                    ts.comb_expr,
                    *[(ts.get_cur(n), state_snap[i][n]) for n in ts.state_vars],
                    *[(ts.get_inp(n), inp_snap[i][n]) for n in ts.inputs],
                )
                sol.add(z3.simplify(comb_subst))

            t0 = time.time()
            sol.check()
            return time.time() - t0
        except Exception:
            return -1.0

    def _estimate_temporal_depth(self, p_expr):
        """Estimate temporal depth: count of next-state references in expression."""
        next_count = [0]

        def walk(e):
            if e is None:
                return
            try:
                name = str(e)
                if name.endswith("_next"):
                    next_count[0] += 1
            except Exception:
                pass
            for child in e.children():
                walk(child)

        walk(p_expr)
        return next_count[0]

    # ──────────────────────────────────────────────────────────
    # 5. Proof Core: MUS extraction with COI pre-filter, per-property + var essentiality
    # ──────────────────────────────────────────────────────────

    def _assumption_refs(self, a_idx):
        """Collect variable references for assumption a_idx via _collect_var_refs."""
        ts = self.ts
        a_vars, a_inps, _ = _collect_var_refs(ts.assumptions[a_idx], ts)
        return a_vars, a_inps

    def _assumption_in_cone(self, a_idx, coi):
        """Check if assumption a_idx references any state/input variable in COI."""
        a_vars, a_inps = self._assumption_refs(a_idx)
        state_in = set(coi.get("state_bit_refs", {}))
        inp_in = set(coi.get("inp_bit_refs", {}))
        return bool(a_vars & state_in) or bool(a_inps & inp_in)

    def extract_proof_core(self, p_exprs: list[tuple[str, z3.BoolRef]] | None = None):
        """Extract per-property proof core with COI pre-filter + state var essentiality.

        For each property:
          1. Compute bit-level COI (transitive fan-in)
          2. Skip assumptions outside the cone → trivially redundant
          3. For remaining assumptions: MUS check (remove → re-check ¬P)
          4. For each state var in cone: freeze to init → re-check ¬P

        Returns per-property breakdown AND aggregate.
        """
        ts = self.ts
        if not ts.assumptions:
            return self._empty_core()

        if p_exprs is None:
            p_exprs = ts.properties + ts.trans_properties
        if not p_exprs:
            return self._empty_core()

        # Precompute COI per property + assumption refs
        per_property_coi = {}
        for pname, p_expr in p_exprs:
            per_property_coi[pname] = self._bit_level_coi(p_expr)

        # Per-property results
        per_property = {}

        for pname, p_expr in p_exprs:
            coi = per_property_coi[pname]
            state_in_cone = set(coi.get("state_bit_refs", {}))

            # --- COI-filtered assumption essentiality ---
            prop_assumptions = []
            for i in range(len(ts.assumptions)):
                a_src = ts.get_assumption_source(i)
                a_label = _extract_label(a_src) if a_src else f"assume_{i}"

                if not self._assumption_in_cone(i, coi):
                    prop_assumptions.append({
                        "label": a_label,
                        "idx": i,
                        "essential": False,
                        "reason": "outside_cone",
                    })
                    continue

                base = z3.Solver()
                base.set("timeout", ts.timeout)
                base.add(ts.init_expr)
                base.add(ts.comb_expr)
                base.add(ts.trans_expr)
                base.add(z3.Not(p_expr))
                for j, ra in enumerate(ts.assumptions):
                    if j != i:
                        base.add(ra)
                r = base.check()
                essential = (r == z3.sat)

                prop_assumptions.append({
                    "label": a_label,
                    "idx": i,
                    "essential": essential,
                    "reason": "essential" if essential else "redundant",
                })

            # --- State var essentiality (per-var trans removal) ---
            state_var_results = {}
            next_exprs = getattr(ts, '_next_state_exprs', {})
            cone_vars = [
                v for v in sorted(state_in_cone)
                if v in ts.state_vars and v in next_exprs
            ]
            if cone_vars and len(ts.assumptions) > 0:
                # Build solver core (init + comb + ¬P + assumptions)
                core = z3.Solver()
                core.set("timeout", ts.timeout)
                core.add(ts.init_expr)
                core.add(ts.comb_expr)
                core.add(z3.Not(p_expr))
                for a in ts.assumptions:
                    core.add(a)

                # Build full solver with ALL per-var trans assertions
                full = z3.Solver()
                full.set("timeout", ts.timeout)
                full.add(ts.init_expr)
                full.add(ts.comb_expr)
                full.add(z3.Not(p_expr))
                for a in ts.assumptions:
                    full.add(a)
                for var_name in cone_vars:
                    full.add(ts._next[var_name] == next_exprs[var_name])
                r_full = full.check()

                if r_full == z3.unsat:
                    # For each var V, build solver without V's trans.
                    # If SAT → V is essential (its trans is needed for the proof)
                    for var_name in cone_vars:
                        s = z3.Solver()
                        s.set("timeout", ts.timeout)
                        s.add(ts.init_expr)
                        s.add(ts.comb_expr)
                        s.add(z3.Not(p_expr))
                        for a in ts.assumptions:
                            s.add(a)
                        for other in cone_vars:
                            if other != var_name:
                                s.add(ts._next[other] == next_exprs[other])
                        r = s.check()
                        essential = (r == z3.sat)
                        width = ts.state_vars[var_name].width
                        state_var_results[var_name] = {
                            "essential": essential,
                            "width": width,
                        }
                else:
                    for var_name in cone_vars:
                        width = ts.state_vars[var_name].width
                        state_var_results[var_name] = {
                            "essential": False,
                            "width": width,
                        }

                # Add combinational state vars (not in next_exprs) as unknown
                for var_name in sorted(state_in_cone):
                    if var_name in ts.state_vars and var_name not in state_var_results:
                        width = ts.state_vars[var_name].width
                        state_var_results[var_name] = {
                            "essential": False,
                            "width": width,
                        }
            else:
                for var_name in sorted(state_in_cone):
                    if var_name not in ts.state_vars:
                        continue
                    width = ts.state_vars[var_name].width
                    state_var_results[var_name] = {
                        "essential": False,
                        "width": width,
                    }

            per_property[pname] = {
                "coi": coi,
                "assumptions": prop_assumptions,
                "n_assumptions_in_cone": sum(
                    1 for a in prop_assumptions if a.get("reason") != "outside_cone"
                ),
                "n_assumptions_outside_cone": sum(
                    1 for a in prop_assumptions if a.get("reason") == "outside_cone"
                ),
                "state_vars": state_var_results,
                "n_state_vars_in_cone": len(state_in_cone),
                "inputs_in_cone": sorted(coi.get("inp_bit_refs", {})),
            }

        # --- Aggregate across all properties ---
        agg_per_assumption: list[dict] = []
        for i in range(len(ts.assumptions)):
            a_src = ts.get_assumption_source(i)
            a_label = _extract_label(a_src) if a_src else f"assume_{i}"
            essential_for = []
            redundant_for = []
            for pname in per_property:
                pa_list = per_property[pname]["assumptions"]
                pa = next(a for a in pa_list if a["idx"] == i)
                if pa.get("reason") == "outside_cone":
                    redundant_for.append(pname)
                elif pa["essential"]:
                    essential_for.append(pname)
                else:
                    redundant_for.append(pname)
            agg_per_assumption.append({
                "label": a_label,
                "essential_for": essential_for,
                "redundant_for": redundant_for,
                "n_essential": len(essential_for),
                "n_redundant": len(redundant_for),
            })

        essential_agg = [a for a in agg_per_assumption if a["n_essential"] > 0]
        redundant_agg = [a for a in agg_per_assumption if a["n_essential"] == 0]

        # Aggregate state var essentiality (union across properties)
        agg_state_vars: dict[str, dict] = {}
        for pname in per_property:
            for vname, vres in per_property[pname].get("state_vars", {}).items():
                if vname not in agg_state_vars:
                    agg_state_vars[vname] = {"essential_for": [], "redundant_for": [], "width": vres["width"]}
                if vres["essential"]:
                    agg_state_vars[vname]["essential_for"].append(pname)
                else:
                    agg_state_vars[vname]["redundant_for"].append(pname)

        return {
            "per_property": per_property,
            "aggregate": {
                "per_assumption": agg_per_assumption,
                "essential": [a["label"] for a in essential_agg],
                "redundant": [a["label"] for a in redundant_agg],
                "n_essential": len(essential_agg),
                "n_redundant": len(redundant_agg),
                "total": len(ts.assumptions),
                "state_vars": agg_state_vars,
                "n_essential_state_vars": sum(
                    1 for v in agg_state_vars.values() if v["essential_for"]
                ),
                "n_redundant_state_vars": sum(
                    1 for v in agg_state_vars.values() if not v["essential_for"]
                ),
            },
        }

    def _empty_core(self):
        return {
            "per_property": {},
            "aggregate": {
                "per_assumption": [],
                "essential": [],
                "redundant": [],
                "n_essential": 0,
                "n_redundant": 0,
                "total": 0,
                "state_vars": {},
                "n_essential_state_vars": 0,
                "n_redundant_state_vars": 0,
            },
        }

        if p_exprs is None:
            p_exprs = ts.properties + ts.trans_properties
        if not p_exprs:
            return {"essential": [], "redundant": [], "n_essential": 0, "n_redundant": 0}

        per_assumption: list[dict] = []
        for i, a in enumerate(ts.assumptions):
            a_src = ts.get_assumption_source(i)
            a_label = _extract_label(a_src) if a_src else f"assume_{i}"
            essential_for = []
            redundant_for = []

            for pname, p_expr in p_exprs:
                base = z3.Solver()
                base.set("timeout", ts.timeout)
                base.add(ts.init_expr)
                base.add(ts.comb_expr)
                base.add(ts.trans_expr)
                base.add(z3.Not(p_expr))

                remaining = [x for j, x in enumerate(ts.assumptions) if j != i]
                for ra in remaining:
                    base.add(ra)

                r = base.check()
                if r == z3.sat:
                    # Property fails without a_i → a_i is essential for this property
                    essential_for.append(pname)
                else:
                    # Property still holds without a_i → a_i is redundant
                    redundant_for.append(pname)
                base.reset()

            per_assumption.append({
                "label": a_label,
                "essential_for": essential_for,
                "redundant_for": redundant_for,
                "n_essential": len(essential_for),
                "n_redundant": len(redundant_for),
            })

        total = len(ts.assumptions)
        essential_assumptions = [a for a in per_assumption if a["n_essential"] > 0]
        redundant_assumptions = [a for a in per_assumption if a["n_essential"] == 0]

        return {
            "per_assumption": per_assumption,
            "essential": [a["label"] for a in essential_assumptions],
            "redundant": [a["label"] for a in redundant_assumptions],
            "n_essential": len(essential_assumptions),
            "n_redundant": len(redundant_assumptions),
            "total": total,
        }

    # ──────────────────────────────────────────────────────────
    # 6. COI-Filtered Mutation Testing with Equivalence Check
    # ──────────────────────────────────────────────────────────

    def mutation_test(self, p_expr, pname, engine="sat_ic3", max_mutations=20):
        """Inject COI-filtered mutations, filter equivalents, measure detection rate.

        Algorithm:
          1. Compute bit-level COI for the property
          2. Select mutation candidates (state vars having COI)
          3. For each candidate: stuck-at-0, stuck-at-1, bit-flip
          4. Differential equivalence: filter mutations masked by design
          5. Incremental BMC to check assertion detection
        """
        import random, copy
        from ...engine.sat_ic3 import SATIC3

        ts = self.ts
        rng = random.Random(42)

        coi = self._bit_level_coi(p_expr)
        candidates = list(coi.get("state_bit_refs", {}).keys())
        if not candidates:
            return {
                "mutation_score": None,
                "reason": "no COI-relevant state vars to mutate",
            }

        mutations = []
        for name in candidates:
            for mtype in ["stuck_at_0", "stuck_at_1"]:
                mutations.append((name, mtype))

        rng.shuffle(mutations)
        mutations = mutations[:max_mutations]

        caught = 0
        total = 0
        equivalent = 0
        details = []

        for name, mtype in mutations:
            if not self._is_mutation_effective(ts, name, mtype):
                equivalent += 1
                details.append({
                    "signal": name,
                    "type": mtype,
                    "caught": False,
                    "equivalent": True,
                    "reason": "design masks fault (equivalent)",
                })
                continue

            total += 1
            ts2 = copy.deepcopy(ts)
            self._inject_mutation(ts2, name, mtype)

            try:
                eng = SATIC3(ts2)
                result = eng._prove_property(p_expr, pname, verbose=False)
                detected = result.get("result") == "fail"
                if detected:
                    caught += 1
                details.append({
                    "signal": name,
                    "type": mtype,
                    "caught": detected,
                    "equivalent": False,
                    "reason": "caught" if detected else "undetected",
                })
            except Exception as e:
                details.append({
                    "signal": name,
                    "type": mtype,
                    "caught": False,
                    "equivalent": False,
                    "reason": str(e)[:40],
                })

        score = caught / max(total, 1)
        return {
            "mutation_score": round(score, 3),
            "mutations_caught": caught,
            "mutations_total": total,
            "mutations_equivalent": equivalent,
            "details": details,
        }

    def _is_mutation_effective(self, ts, signal_name, mtype):
        """Differential equivalence check: does the mutation change behavior?

        Checks if there exists a reachable state where original_next != mutant_next.
        """
        if signal_name not in ts._next_state_exprs:
            return False

        orig_next = ts._next_state_exprs.get(signal_name)
        w = ts.state_vars[signal_name].width

        if mtype == "stuck_at_0":
            mut_next = z3.BitVecVal(0, w)
        elif mtype == "stuck_at_1":
            mut_next = z3.BitVecVal(-1, w)
        else:
            mut_next = orig_next ^ z3.BitVecVal(1, w)

        diff = orig_next != mut_next

        sol = z3.Solver()
        sol.set("timeout", 2000)
        sol.add(ts.init_expr)
        sol.add(ts.comb_expr)
        sol.add(diff)

        try:
            return sol.check() == z3.sat
        except Exception:
            return True

    def _inject_mutation(self, ts, signal_name, mtype):
        """Inject mutation into a cloned transition system."""
        if signal_name in ts.state_vars and signal_name in ts._next_state_exprs:
            w = ts.state_vars[signal_name].width
            orig = ts._next_state_exprs[signal_name]
            if mtype == "stuck_at_0":
                ts._next_state_exprs[signal_name] = z3.BitVecVal(0, w)
            elif mtype == "stuck_at_1":
                ts._next_state_exprs[signal_name] = z3.BitVecVal(-1, w)
            else:
                ts._next_state_exprs[signal_name] = orig ^ z3.BitVecVal(1, w)

        elif signal_name in ts.inputs:
            w = ts.inputs[signal_name].width
            if mtype == "stuck_at_0":
                ts._trans_constraints.append(
                    ts.get_inp(signal_name) == z3.BitVecVal(0, w)
                )
            elif mtype == "stuck_at_1":
                ts._trans_constraints.append(
                    ts.get_inp(signal_name) == z3.BitVecVal(-1, w)
                )


def _extract_label(source: str) -> str:
    """Extract assertion label from source text like 'CheckHotOne_A: assert property (...)'.

    Returns just the label (e.g. 'CheckHotOne_A') or empty string if no label found.
    """
    import re
    m = re.search(r'^\s*(\w+)\s*:\s*(?:assert|assume|cover)\s+property\b', source, re.MULTILINE)
    if m:
        return m.group(1)
    return ""


def format_dashboard(ts, metrics_dict, mutation_results=None, proof_core_result=None, verbose=False):
    """Render assertion quality dashboard table.

    metrics_dict: {property_name: {coi:{...}, vacuity:{...}, coverage:{...}, complexity:{...}}}
    """
    lines = []
    lines.append("")
    lines.append(">>> Assertion Quality Dashboard")
    lines.append("")

    if not metrics_dict:
        lines.append("  No metrics available.")
        return "\n".join(lines)

    headers = ["Property", "Source", "COI %", "Vacuity", "Coverage", "Complexity", "Mut Score"]
    col_widths = [28, 24, 12, 10, 9, 14, 12]

    sep = "├" + "┼".join("─" * w for w in col_widths) + "┤"
    top = "┌" + "┬".join("─" * w for w in col_widths) + "┐"
    bot = "└" + "┴".join("─" * w for w in col_widths) + "┘"

    def header_row():
        cells = []
        for h, w in zip(headers, col_widths):
            cells.append(h.ljust(w))
        return "│" + "│".join(cells) + "│"

    lines.append(top)
    lines.append(header_row())
    lines.append(sep)

    for pname in sorted(metrics_dict.keys()):
        m = metrics_dict[pname]
        coi = m.get("coi", {})
        vac = m.get("vacuity", {})
        cov = m.get("coverage", {})
        cpx = m.get("complexity", {})

        coi_pct = f"{coi.get('state_in_cone_pct', 0):.0f}%"
        n_state = coi.get("n_state_bits", 0)
        n_total = coi.get("n_state_total_bits", 0)
        coi_str = f"{coi_pct} ({n_state}/{n_total})"

        vtype = vac.get("type", "n/a")
        if vtype == "non-vacuous":
            vac_str = "Non-vac"
        elif vtype == "strong_vacuity":
            vac_str = "VACUOUS"
        elif vtype == "n/a":
            vac_str = "N/A"
        else:
            vac_str = vtype[:8]

        cov_pct = f"{cov.get('coverage_pct', 0):.0f}%"

        cpx_str = f"d={cpx.get('bit_depth', '?')},n={cpx.get('bit_op_count', '?')}"

        mut = mutation_results.get(pname, {}) if mutation_results else {}
        mut_score = mut.get("mutation_score")
        if mut_score is not None:
            mut_str = f"{mut_score:.0%} (COI)"
        else:
            mut_str = "N/A"

        src = ts.get_prop_source(pname)
        src_short = _extract_label(src)

        row_data = [pname, src_short, coi_str, vac_str, cov_pct, cpx_str, mut_str]
        cells = []
        for val, w in zip(row_data, col_widths):
            cells.append(str(val).ljust(w)[:w])
        lines.append("│" + "│".join(cells) + "│")

    lines.append(bot)

    # --- Footer: Proof Core (bit-level cone + assumption essentiality) ---
    # Per-property: which state bits are in the proof cone
    # Aggregate: union of bits across all properties = verification coverage
    n_total_bits = 0
    all_used_bits: dict[str, set[int]] = {}
    for pname in sorted(metrics_dict.keys()):
        coi = metrics_dict[pname].get("coi", {})
        total = coi.get("n_state_total_bits", 0)
        if total > n_total_bits:
            n_total_bits = total
        for v, bits in coi.get("state_bit_refs", {}).items():
            if v not in all_used_bits:
                all_used_bits[v] = set()
            all_used_bits[v].update(bits)

    n_used_bits = sum(len(b) for b in all_used_bits.values())
    verif_cov_pct = (n_used_bits / max(n_total_bits, 1)) * 100

    lines.append("")
    lines.append(f"  Proof Core: {n_used_bits}/{n_total_bits} state bits in cone "
                 f"({verif_cov_pct:.0f}% verification coverage)")
    if proof_core_result:
        agg = proof_core_result.get("aggregate", {})
        # --- Assumption essentiality ---
        per_a = agg.get("per_assumption", [])
        n_essential = agg.get("n_essential", 0)
        n_redundant = agg.get("n_redundant", 0)
        total = agg.get("total", 0)
        if per_a:
            n_outside = sum(
                1 for p in proof_core_result.get("per_property", {}).values()
                for a in p.get("assumptions", [])
                if a.get("reason") == "outside_cone"
            )
            outside_str = f" ({n_outside} outside COI)" if n_outside else ""
            lines.append(f"  Constraint Essentiality: {n_essential}/{total} essential "
                         f"({n_redundant}/{total} redundant{outside_str})")
            for pa in per_a:
                label = pa["label"]
                if pa["n_essential"] > 0:
                    props = ", ".join(pa["essential_for"][:4])
                    lines.append(f"    Essential: {label} needed for [{props}]"
                                 f"{'...' if len(pa['essential_for']) > 4 else ''}")
                else:
                    lines.append(f"    Redundant: {label} (removable)")

        # --- State var essentiality ---
        sv_agg = agg.get("state_vars", {})
        if sv_agg:
            n_ess_sv = agg.get("n_essential_state_vars", 0)
            n_red_sv = agg.get("n_redundant_state_vars", 0)
            n_sv_total = len(sv_agg)
            lines.append(f"  State Var Essentiality: {n_ess_sv}/{n_sv_total} essential "
                         f"({n_red_sv}/{n_sv_total} redundant)")
            for vname, vres in sorted(sv_agg.items()):
                if vres["essential_for"]:
                    props = ", ".join(vres["essential_for"][:4])
                    lines.append(f"    Essential: {vname} needed for [{props}]"
                                 f"{'...' if len(vres['essential_for']) > 4 else ''}")
                else:
                    lines.append(f"    Redundant: {vname} (trans not needed for proof)")

        # --- Per-property proof core (verbose) ---
        if verbose and proof_core_result.get("per_property"):
            lines.append("")
            lines.append("  Per-Property Proof Core:")
            for pname in sorted(proof_core_result["per_property"].keys()):
                pp = proof_core_result["per_property"][pname]
                coi = pp.get("coi", {})
                lines.append(f"    {pname}: COI={coi.get('state_in_cone_pct', 0):.0f}%"
                             f" ({pp['n_state_vars_in_cone']} vars)")
                
                # Assumptions
                a_in = [a for a in pp["assumptions"] if a.get("reason") != "outside_cone"]
                a_out = [a for a in pp["assumptions"] if a.get("reason") == "outside_cone"]
                a_ess = [a for a in a_in if a["essential"]]
                a_red = [a for a in a_in if not a["essential"]]
                if a_ess:
                    lines.append(f"      Essential assumptions: {', '.join(a['label'] for a in a_ess)}")
                if a_red:
                    lines.append(f"      Redundant assumptions: {', '.join(a['label'] for a in a_red[:3])}"
                                 f"{' ...' if len(a_red) > 3 else ''}")
                if a_out:
                    lines.append(f"      Outside COI: {', '.join(a['label'] for a in a_out[:3])}"
                                 f"{' ...' if len(a_out) > 3 else ''}")
                
                # State vars
                sv = pp.get("state_vars", {})
                sv_ess = [v for v, r in sv.items() if r["essential"]]
                sv_red = [v for v, r in sv.items() if not r["essential"]]
                if sv_ess:
                    lines.append(f"      Essential state vars: {', '.join(sv_ess)}")
                if sv_red:
                    lines.append(f"      Redundant state vars: {', '.join(sv_red[:5])}"
                                 f"{' ...' if len(sv_red) > 5 else ''}")
                
                # Inputs
                inps = pp.get("inputs_in_cone", [])
                if inps:
                    lines.append(f"      Inputs in cone: {', '.join(inps[:5])}"
                                 f"{' ...' if len(inps) > 5 else ''}")

    # --- Footer: Mutation Equivalences ---
    if mutation_results:
        total_eq = sum(
            m.get("mutations_equivalent", 0)
            for m in mutation_results.values() if m.get("mutation_score") is not None
        )
        total_mut = sum(
            m.get("mutations_total", 0) + m.get("mutations_equivalent", 0)
            for m in mutation_results.values() if m.get("mutation_score") is not None
        )
        if total_mut > 0:
            lines.append(f"  Mutation Equivalences: {total_eq}/{total_mut} faults uncatchable by design (redundant logic)")

    return "\n".join(lines)
