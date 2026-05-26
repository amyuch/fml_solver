import z3
from heapq import heappush, heappop
from ..ir.transition_system import TransitionSystem
from .kind import check_kinduction
from .bmc import bmc_incremental
from .solver.sat_solver import z3_to_dimacs


try:
    from pysat.solvers import Solver as SATSolver
    _HAVE_PYSAT = True
except ImportError:
    _HAVE_PYSAT = False


class IC3:
    def __init__(self, ts: TransitionSystem, max_frames: int = 20,
                 max_blocking: int = 3000, bmc_fallback_depth: int = 0):
        self.ts = ts
        self.max_frames = max_frames
        self.max_blocking = max_blocking
        self.bmc_fallback_depth = bmc_fallback_depth or max_frames * 50

    def _sat_check(self, expr):
        """Z3 expr via PySAT. True/False/None."""
        if not _HAVE_PYSAT:
            return self._sat_check_z3(expr)
        dimacs, n_vars, n_clauses = z3_to_dimacs(expr)
        if n_vars == 0:
            return n_clauses != 0
        if not dimacs:
            return self._sat_check_z3(expr)
        try:
            sat_solver = SATSolver(name="glucose4", bootstrap_with=dimacs, use_timer=True)
            result = sat_solver.solve()
            sat_solver.delete()
            return result
        except Exception:
            return self._sat_check_z3(expr)

    def _sat_check_z3(self, expr):
        s = z3.Solver()
        s.set("timeout", self.ts.timeout)
        s.add(expr)
        r = s.check()
        if r == z3.sat: return True
        if r == z3.unsat: return False
        return None

    def _sat_check_with_model(self, expr):
        s = z3.Solver()
        s.set("timeout", self.ts.timeout)
        s.add(expr)
        r = s.check()
        if r == z3.sat:
            return s.model()
        return None

    def prove(self, verbose: bool = True) -> dict:
        ts = self.ts
        if not ts.properties and not ts.trans_properties:
            return {"result": "unknown", "reason": "no properties"}

        failures = []
        all_proved = True

        for pname, p_expr in ts.properties:
            result = self._prove_property(p_expr, pname, verbose)
            if result["result"] == "fail":
                failures.append(result)
                all_proved = False
            elif result["result"] == "proved":
                pass
            else:
                all_proved = False

        if ts.trans_properties:
            if verbose:
                print(f"  IC3 (k-ind fallback) for {len(ts.trans_properties)} trans properties...")
            kind_result = check_kinduction(ts, self.max_frames, verbose=verbose)
            if kind_result["result"] == "fail":
                kind_fails = kind_result.get("failures", [kind_result])
                failures.extend(kind_fails)
                all_proved = False
            elif kind_result["result"] != "proved":
                all_proved = False

        if failures:
            first = failures[0]
            first["failures"] = failures
            return first

        if all_proved and (ts.properties or ts.trans_properties):
            return {"result": "proved", "bound": self.max_frames}
        return {"result": "unknown", "bound": self.max_frames}

    def _prove_property(self, P: z3.BoolRef, pname: str, verbose: bool) -> dict:
        ts = self.ts
        cur_to_next = [(ts.get_cur(name), ts.get_next(name)) for name in ts.state_vars]
        inp_to_next = [(ts.get_inp(name), z3.BitVec(f"{name}_inp_next", ts.inputs[name].width))
                       for name in ts.inputs]
        P_next = z3.substitute(P, *(cur_to_next + inp_to_next))
        self._p_str = z3.simplify(P).sexpr() if not z3.is_true(P) and not z3.is_false(P) else str(P)

        # Base case: check if any initial state violates P
        s0 = z3.Solver()
        s0.set("timeout", self.ts.timeout)
        s0.add(ts.init_expr)
        s0.add(ts.comb_expr)
        s0.add(ts.assumption_expr)
        s0.add(z3.Not(P))
        if s0.check() == z3.sat:
            if verbose:
                print(f"      counterexample at initial state")
            m = s0.model()
            trace = []
            frame = {}
            for name in ts.state_vars:
                frame[name] = m.eval(ts.get_cur(name))
            trace.append(frame)
            return {"result": "fail", "property": pname, "bound": 0,
                    "counterexample": trace,
                    "trace": self._format_cex(trace)}

        frames: list[list[z3.BoolRef]] = [[] for _ in range(self.max_frames + 2)]
        frames[0].append(ts.init_expr)
        frames[0].append(ts.comb_expr)

        if verbose:
            print(f"  IC3 proving: {pname}")

        for k in range(1, self.max_frames + 1):
            if verbose:
                print(f"    frame {k}")
            ok = self._strengthen(k, frames, P, P_next, ts, verbose)
            if isinstance(ok, dict) and ok.get("result") == "fail":
                if verbose:
                    print(f"      counter-example found (depth {ok.get('bound', '?')})")
                trace = ok.get("trace", [])
                return {"result": "fail", "property": pname, "bound": ok.get("bound", 0),
                        "counterexample": trace,
                        "trace": self._format_cex(trace)}
            if ok == "proved":
                return {"result": "proved", "property": pname, "k": k - 1}
            if ok is None:
                bmc_depth = self.bmc_fallback_depth
                if verbose:
                    print(f"      max_blocking exhausted, running BMC fallback (depth={bmc_depth})...")
                bmc_result = bmc_incremental(ts, bmc_depth, verbose=False)
                if bmc_result["result"] == "fail":
                    return bmc_result
                return {"result": "unknown", "property": pname,
                        "bound": self.max_frames, "bmc_checked_up_to": bmc_depth}

            self._propagate_all(k, frames, P, ts)

            if self._frames_equal(frames, k - 1, k):
                if verbose:
                    print(f"      converged at frame {k}")
                return {"result": "proved", "property": pname, "k": k}

        return {"result": "unknown", "property": pname, "bound": self.max_frames}

    def _format_cex(self, trace):
        if not trace:
            return "Counterexample: (empty)"
        lines = ["=" * 60, "Counterexample Trace:", "=" * 60]
        for step, frame in enumerate(trace):
            lines.append(f"\n--- Cycle {step} ---")
            for name, val in frame.items():
                if val is None:
                    continue
                val_str = str(val)
                if val_str == name:
                    continue
                lines.append(f"  {name} = {val}")
        return "\n".join(lines)

    # ── Strengthening with CTI Priority Queue ──────────────────────────────

    _cube_objs: dict = {}

    def _strengthen(self, k: int, frames, P, P_next, ts, verbose) -> bool | str | dict:
        cur_to_next = [(ts.get_cur(name), ts.get_next(name)) for name in ts.state_vars]
        inp_to_next = [(ts.get_inp(name), z3.BitVec(f"{name}_inp_next", ts.inputs[name].width))
                       for name in ts.inputs]
        ts_cn = z3.substitute(ts.comb_expr, *(cur_to_next + inp_to_next))

        heap = []
        seq = 0

        p_var_strs = set()
        for name in ts.state_vars:
            cur_str = f"__{name}__cur"
            if cur_str in self._p_str:
                p_var_strs.add(cur_str)

        cex_next = {}
        cex_state = {}

        def _cti_signature(cube):
            if z3.is_and(cube):
                lits = cube.children()
            else:
                lits = [cube]
            sig_lits = frozenset(str(l) for l in lits)
            return sig_lits

        def _push_cube(cube, i):
            nonlocal seq
            if i < 0:
                return
            heappush(heap, (i, seq, cube))
            seq += 1

        def _extract_state_vals(model):
            vals = {}
            for name in ts.state_vars:
                try:
                    v = model.eval(ts.get_cur(name))
                    vals[name] = v if str(v) != str(ts.get_cur(name)) else None
                except Exception:
                    vals[name] = None
            for name in ts.inputs:
                try:
                    v = model.eval(ts.get_inp(name))
                    vals[f"{name}_inp"] = v if str(v) != str(ts.get_inp(name)) else None
                except Exception:
                    vals[f"{name}_inp"] = None
            return vals

        def _cube_to_state(cube):
            vals = {}
            if z3.is_and(cube):
                lits = cube.children()
            else:
                lits = [cube]
            cur_names = {str(ts.get_cur(name)): name for name in ts.state_vars}
            inp_names = {str(ts.get_inp(name)): name for name in ts.inputs}
            for lit in lits:
                if z3.is_eq(lit):
                    a, b = lit.children()
                    sa, sb = str(a), str(b)
                    if sa in cur_names:
                        vals[cur_names[sa]] = b
                    elif sb in cur_names:
                        vals[cur_names[sb]] = a
                    if sa in inp_names:
                        vals[f"{inp_names[sa]}_inp"] = b
                    elif sb in inp_names:
                        vals[f"{inp_names[sb]}_inp"] = a
            return vals

        def _build_cex_trace(init_model, first_cube):
            trace = [_extract_state_vals(init_model)]
            cur_key = str(first_cube)
            keys_seen = set()
            while cur_key in cex_next and cur_key not in keys_seen:
                keys_seen.add(cur_key)
                if cur_key in cex_state:
                    trace.append(cex_state[cur_key])
                else:
                    cube_obj = IC3._cube_objs.get(cur_key)
                    if cube_obj is not None:
                        trace.append(_cube_to_state(cube_obj))
                    else:
                        break
                cur_key = cex_next[cur_key]
            if cur_key in cex_state:
                trace.append(cex_state[cur_key])
            else:
                cube_obj = IC3._cube_objs.get(cur_key)
                if cube_obj is not None:
                    trace.append(_cube_to_state(cube_obj))
            # Compute the violating next state from the final CTI cube
            final_cube = IC3._cube_objs.get(cur_key)
            if final_cube is not None:
                ns = z3.Solver()
                ns.set("timeout", 2000)
                cur_to_next = [(ts.get_cur(name), ts.get_next(name)) for name in ts.state_vars]
                inp_to_next = [(ts.get_inp(name), z3.BitVec(f"{name}_inp_next", ts.inputs[name].width))
                               for name in ts.inputs]
                ns.add(final_cube)
                ns.add(ts.assumption_expr)
                ns.add(ts.comb_expr)
                ns.add(ts.trans_expr)
                ns.add(z3.substitute(ts.comb_expr, *(cur_to_next + inp_to_next)))
                ns.add(z3.Not(P_next))
                if ns.check() == z3.sat:
                    nm = ns.model()
                    nv = {}
                    for name in ts.state_vars:
                        try:
                            nv[name] = nm.eval(ts.get_next(name))
                        except Exception:
                            nv[name] = None
                    trace.append(nv)
            return trace

        seen_cti = set()

        for attempt in range(self.max_blocking):
            if heap:
                i, _, cube = heappop(heap)
            else:
                cti_parts = list(frames[k - 1]) + [P, ts.comb_expr, ts.trans_expr, ts_cn, z3.Not(P_next)]
                cti_query = z3.And(*cti_parts) if len(cti_parts) > 1 else cti_parts[0]
                sat = self._sat_check(cti_query)
                if sat is False:
                    if self._frames_equal(frames, k - 1, k):
                        return "proved"
                    return True
                if sat is None:
                    if self._frames_equal(frames, k - 1, k):
                        return "proved"
                    return True
                model = self._sat_check_with_model(cti_query)
                if model is None:
                    if self._frames_equal(frames, k - 1, k):
                        return "proved"
                    return True
                cube = self._extract_cube(model, ts)
                IC3._cube_objs[str(cube)] = cube
                sig = _cti_signature(cube)
                if sig in seen_cti:
                    if verbose:
                        print(f"      spinning on repeated CTI @{k - 1}, triggering BMC fallback")
                    return None
                seen_cti.add(sig)
                _push_cube(cube, k - 1)
                if verbose:
                    print(f"      CTI @{k - 1}: {cube}")
                continue

            if i >= 0 and self._is_blocked(cube, i, frames, ts):
                continue

            result = self._check_predecessor(cube, i, frames, P, ts)
            if result is None:
                if verbose:
                    print(f"      solver timeout @{i}")
                continue

            if result == "unsat":
                clause = self._generalize(cube, i, frames, P, ts)
                self._add_clause(clause, i, frames, ts)
                continue

            if i == 0:
                if verbose:
                    print(f"      CEX: predecessor reachable from init")
                trace = _build_cex_trace(result, cube)
                return {"result": "fail", "trace": trace, "bound": len(trace) - 1}

            pred_cube = self._extract_cube(result, ts)
            cex_state[str(pred_cube)] = _extract_state_vals(result)
            cex_next[str(pred_cube)] = str(cube)
            IC3._cube_objs[str(cube)] = cube
            IC3._cube_objs[str(pred_cube)] = pred_cube
            _push_cube(cube, i)
            _push_cube(pred_cube, i - 1)

        if verbose:
            print(f"      max_blocking ({self.max_blocking}) exhausted")
        return None

    # ── Cube / Predecessor helpers ─────────────────────────────────────────

    def _extract_cube(self, model, ts) -> z3.BoolRef:
        parts = []
        for name in ts.state_vars:
            val = model.eval(ts.get_cur(name))
            parts.append(ts.get_cur(name) == val)
        return z3.And(*parts)

    def _is_blocked(self, cube, i, frames, ts) -> bool:
        if i < 0 or i >= len(frames):
            return False
        for clause in frames[i]:
            if self._clause_blocks(clause, cube, ts):
                return True
        return False

    def _clause_blocks(self, clause, cube, ts) -> bool:
        if z3.is_false(clause):
            return True
        if z3.is_true(clause):
            return False
        if not z3.is_not(clause):
            return False
        inner = clause.children()[0]
        if z3.is_and(inner):
            g_lits = set(inner.children())
        else:
            g_lits = {inner}

        if z3.is_and(cube):
            c_lits = set(cube.children())
        else:
            c_lits = {cube}

        return g_lits.issubset(c_lits)

    def _check_predecessor(self, cube, i, frames, P, ts):
        cur_to_next = [(ts.get_cur(name), ts.get_next(name)) for name in ts.state_vars]
        inp_to_next = [(ts.get_inp(name), z3.BitVec(f"{name}_inp_next", ts.inputs[name].width))
                       for name in ts.inputs]
        all_to_next = cur_to_next + inp_to_next
        parts = []
        if i == 0:
            parts.append(ts.init_expr)
        else:
            parts.append(z3.And(*frames[i - 1]))
            parts.append(P)
        parts.append(ts.assumption_expr)
        parts.append(ts.comb_expr)
        parts.append(ts.trans_expr)
        parts.append(z3.substitute(ts.comb_expr, *all_to_next))
        parts.append(z3.substitute(cube, *all_to_next))
        query = z3.And(*parts) if len(parts) > 1 else parts[0]
        sat = self._sat_check(query)
        if sat is False:
            return "unsat"
        if sat is None:
            return None
        return self._sat_check_with_model(query)

    # ── Unsat-Core Generalization ─────────────────────────────────────────

    def _generalize(self, cube, i, frames, P, ts):
        if i < 0:
            return z3.Not(cube)

        if z3.is_and(cube):
            lits_cur = list(cube.children())
        else:
            lits_cur = [cube]

        if len(lits_cur) <= 1:
            return z3.Not(cube)

        cur_to_next = [(ts.get_cur(name), ts.get_next(name)) for name in ts.state_vars]
        inp_to_next = [(ts.get_inp(name), z3.BitVec(f"{name}_inp_next", ts.inputs[name].width))
                       for name in ts.inputs]
        all_to_next = cur_to_next + inp_to_next
        lits_next = []
        for lit in lits_cur:
            lits_next.append(z3.substitute(lit, *all_to_next))

        s = z3.Solver()
        s.set("timeout", 1000)

        if i == 0:
            s.add(ts.init_expr)
        else:
            for clause in frames[i - 1]:
                s.add(clause)
            s.add(P)

        s.add(ts.comb_expr)
        s.add(ts.trans_expr)
        s.add(z3.substitute(ts.comb_expr, *all_to_next))

        trackers = []
        for j, lit in enumerate(lits_next):
            t = z3.Bool(f"t{j}")
            s.assert_and_track(lit, t)
            trackers.append(t)

        r = s.check()
        if r != z3.unsat:
            return z3.Not(cube)

        core = s.unsat_core()
        core_set = set(str(t) for t in core)

        p_var_strs = set()

        for name in ts.state_vars:
            cur_str = f"__{name}__cur"
            if cur_str in self._p_str:
                p_var_strs.add(cur_str)

        essential = []
        has_prop_var = False
        for j, lit in enumerate(lits_cur):
            if f"t{j}" in core_set:
                essential.append(lit)
                if any(pv in str(lit) for pv in p_var_strs):
                    has_prop_var = True

        if not has_prop_var and p_var_strs:
            for lit in lits_cur:
                if any(pv in str(lit) for pv in p_var_strs):
                    essential.append(lit)
                    has_prop_var = True
                    break

        if len(essential) <= 1:
            if not essential:
                return z3.Not(cube)
            return z3.Not(essential[0])

        essential = self._minimize_core(essential, i, frames, P, ts)

        prop_essential = []
        for lit in essential:
            if any(pv in str(lit) for pv in p_var_strs):
                prop_essential.append(lit)
        if prop_essential:
            essential = prop_essential

        if len(essential) == 0:
            return z3.Not(cube)
        if len(essential) == 1:
            clause = z3.Not(essential[0])
        else:
            clause = z3.Not(z3.And(*essential))

        clause = self._ensure_prop_var(clause, cube, i, frames, P, ts)
        return clause

    def _ensure_prop_var(self, clause, cube, i, frames, P, ts):
        """If clause doesn't mention any property variable, try to find a
        single-literal clause that does, so it blocks cubes more broadly."""
        p_var_strs = set()

        for name in ts.state_vars:
            cur_str = f"__{name}__cur"
            if cur_str in self._p_str:
                p_var_strs.add(cur_str)

        if not p_var_strs:
            return clause

        clause_str = str(clause)
        if any(pv in clause_str for pv in p_var_strs):
            return clause

        if z3.is_and(cube):
            lits_cur = list(cube.children())
        else:
            lits_cur = [cube]

        cur_to_next = [(ts.get_cur(name), ts.get_next(name)) for name in ts.state_vars]

        for lit in lits_cur:
            lit_str = str(lit)
            if not any(pv in lit_str for pv in p_var_strs):
                continue
            s = z3.Solver()
            s.set("timeout", 200)
            if i == 0:
                s.add(ts.init_expr)
            else:
                for cf in frames[i - 1]:
                    s.add(cf)
                s.add(P)
            s.add(ts.assumption_expr)
            s.add(ts.comb_expr)
            s.add(ts.trans_expr)
            s.add(z3.substitute(ts.comb_expr, *cur_to_next))
            s.add(z3.substitute(lit, *cur_to_next))
            if s.check() == z3.unsat:
                return z3.Not(lit)

        return clause

    def _minimize_core(self, essential, i, frames, P, ts):
        p_var_strs = set()

        for name in ts.state_vars:
            cur_str = f"__{name}__cur"
            if cur_str in self._p_str:
                p_var_strs.add(cur_str)

        cur_to_next = [(ts.get_cur(name), ts.get_next(name)) for name in ts.state_vars]
        inp_to_next = [(ts.get_inp(name), z3.BitVec(f"{name}_inp_next", ts.inputs[name].width))
                       for name in ts.inputs]
        all_to_next = cur_to_next + inp_to_next
        changed = True
        while changed:
            changed = False
            for idx in range(len(essential) - 1, -1, -1):
                lit = essential[idx]
                lit_str = str(lit)
                is_prop_var = any(pv in lit_str for pv in p_var_strs)
                if is_prop_var:
                    continue
                candidate = [essential[j] for j in range(len(essential)) if j != idx]
                if not candidate:
                    continue
                cand_expr = z3.And(*candidate) if len(candidate) > 1 else candidate[0]

                parts = []
                if i == 0:
                    parts.append(ts.init_expr)
                else:
                    parts.append(z3.And(*frames[i - 1]))
                    parts.append(P)
                parts.append(ts.assumption_expr)
                parts.append(ts.comb_expr)
                parts.append(ts.trans_expr)
                parts.append(z3.substitute(ts.comb_expr, *all_to_next))
                parts.append(z3.substitute(cand_expr, *all_to_next))
                query = z3.And(*parts) if len(parts) > 1 else parts[0]
                if not self._sat_check(query):
                    essential.pop(idx)
                    changed = True
                    essential.pop(idx)
                    changed = True
        return essential

    # ── Clause Management (subsumption-aware) ────────────────────────────

    def _add_clause(self, clause, up_to, frames, ts):
        for i in range(up_to + 1):
            if i >= len(frames):
                break
            existing = frames[i]
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
        if not l1 and l2:
            return False
        if not l2:
            return True
        if not l1:
            return z3.is_false(c1)
        return l1.issubset(l2)

    def _clause_lits(self, clause) -> set:
        if z3.is_false(clause):
            return set()
        if z3.is_true(clause):
            return set()
        if z3.is_not(clause):
            inner = clause.children()[0]
            if z3.is_and(inner):
                return {str(c) for c in inner.children()}
            return {str(inner)}
        if z3.is_and(clause):
            return {str(c) for c in clause.children()}
        return {str(clause)}

    # ── Frame equality check ──────────────────────────────────────────────

    def _frames_equal(self, frames, i, j) -> bool:
        if i >= len(frames) or j >= len(frames):
            return False
        si = set(str(c) for c in frames[i])
        sj = set(str(c) for c in frames[j])
        return si == sj

    # ── Propagation ──────────────────────────────────────────────────────

    def _propagate_all(self, k, frames, P, ts):
        cur_to_next = [(ts.get_cur(name), ts.get_next(name)) for name in ts.state_vars]
        inp_to_next = [(ts.get_inp(name), z3.BitVec(f"{name}_inp_next", ts.inputs[name].width))
                       for name in ts.inputs]
        all_to_next = cur_to_next + inp_to_next
        ts_cn = z3.substitute(ts.comb_expr, *all_to_next)

        for _ in range(5):
            prog = False
            for fi in range(min(k, len(frames) - 1)):
                frm = frames[fi]
                frm_next = frames[fi + 1]
                candidates = [c for c in frm if c not in frm_next]
                if not candidates:
                    continue

                s = z3.Solver()
                s.set("timeout", 5000)
                for c in frm:
                    s.add(c)
                if fi >= 1:
                    s.add(P)
                s.add(ts.assumption_expr)
                s.add(ts.comb_expr)
                s.add(ts.trans_expr)
                s.add(ts_cn)

                to_propagate = []
                for c in candidates:
                    cn = z3.substitute(z3.Not(c), *all_to_next)
                    t = z3.Bool(f"p{fi}_{len(to_propagate)}")
                    s.assert_and_track(cn, t)
                    to_propagate.append((c, t))

                r = s.check()
                if r == z3.unsat:
                    core = set(str(t) for t in s.unsat_core())
                    for c, t in to_propagate:
                        if str(t) not in core:
                            continue
                        self._add_clause(c, fi + 1, frames, ts)
                        prog = True
                else:
                    for c, _ in to_propagate:
                        cs = z3.Solver()
                        cs.set("timeout", 2000)
                        for cc in frm:
                            cs.add(cc)
                        if fi >= 1:
                            cs.add(P)
                        cs.add(ts.assumption_expr)
                        cs.add(ts.comb_expr)
                        cs.add(ts.trans_expr)
                        cs.add(ts_cn)
                        cs.add(z3.substitute(z3.Not(c), *all_to_next))
                        if cs.check() == z3.unsat:
                            self._add_clause(c, fi + 1, frames, ts)
                            prog = True
            if not prog:
                break
