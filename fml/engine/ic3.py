import z3
from heapq import heappush, heappop
from ..ir.transition_system import TransitionSystem
from .kind import check_kinduction
from .bmc import bmc_incremental


class IC3:
    def __init__(self, ts: TransitionSystem, max_frames: int = 20,
                 max_blocking: int = 3000, bmc_fallback_depth: int = 0):
        self.ts = ts
        self.max_frames = max_frames
        self.max_blocking = max_blocking
        self.bmc_fallback_depth = bmc_fallback_depth or max_frames * 50

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
        P_next = z3.substitute(P, *cur_to_next)

        # Base case: check if any initial state violates P
        s0 = z3.Solver()
        s0.set("timeout", 60000)
        s0.add(ts.init_expr)
        s0.add(ts.assumption_expr)
        s0.add(z3.Not(P))
        if s0.check() == z3.sat:
            if verbose:
                print(f"      counterexample at initial state")
            return {"result": "fail", "property": pname, "bound": 0}

        frames: list[list[z3.BoolRef]] = [[] for _ in range(self.max_frames + 2)]
        frames[0].append(ts.init_expr)

        if verbose:
            print(f"  IC3 proving: {pname}")

        for k in range(1, self.max_frames + 1):
            if verbose:
                print(f"    frame {k}")
            ok = self._strengthen(k, frames, P, P_next, ts, verbose)
            if ok is False:
                if verbose:
                    print(f"      counter-example found")
                return {"result": "fail", "property": pname, "cube": "found"}
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

    # ── Strengthening with CTI Priority Queue ──────────────────────────────

    def _strengthen(self, k: int, frames, P, P_next, ts, verbose) -> bool | str:
        cur_to_next = [(ts.get_cur(name), ts.get_next(name)) for name in ts.state_vars]
        ts_cn = z3.substitute(ts.comb_expr, *cur_to_next)

        heap = []
        seq = 0

        p_var_strs = set()
        p_str = z3.simplify(P).sexpr() if not z3.is_true(P) and not z3.is_false(P) else str(P)
        for name in ts.state_vars:
            cur_str = f"__{name}__cur"
            if cur_str in p_str:
                p_var_strs.add(cur_str)

        def _cti_signature(cube):
            if z3.is_and(cube):
                lits = cube.children()
            else:
                lits = [cube]
            sig_lits = frozenset(
                str(l) for l in lits
                if any(pv in str(l) for pv in p_var_strs)
            )
            return sig_lits

        def _push_cube(cube, i):
            nonlocal seq
            if i < 0:
                return
            heappush(heap, (i, seq, cube))
            seq += 1

        seen_cti = set()

        for attempt in range(self.max_blocking):
            if heap:
                i, _, cube = heappop(heap)
            else:
                s = z3.Solver()
                s.set("timeout", 60000)
                for clause in frames[k - 1]:
                    s.add(clause)
                s.add(P)
                s.add(ts.comb_expr)
                s.add(ts.trans_expr)
                s.add(ts_cn)
                s.add(z3.Not(P_next))

                r = s.check()
                if r == z3.unsat:
                    if self._frames_equal(frames, k - 1, k):
                        return "proved"
                    return True
                model = s.model()
                cube = self._extract_cube(model, ts)
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

            if i == -1:
                if verbose:
                    print(f"      CEX at init")
                return False

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
                return False

            pred_cube = self._extract_cube(result, ts)
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
        s = z3.Solver()
        s.set("timeout", 60000)
        if i == 0:
            s.add(ts.init_expr)
        else:
            for clause in frames[i - 1]:
                s.add(clause)
            s.add(P)

        s.add(ts.assumption_expr)
        s.add(ts.comb_expr)
        s.add(ts.trans_expr)
        s.add(z3.substitute(ts.comb_expr, *cur_to_next))
        s.add(z3.substitute(cube, *cur_to_next))

        r = s.check()
        if r == z3.unsat:
            return "unsat"
        if r == z3.unknown:
            return None
        return s.model()

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
        lits_next = []
        for lit in lits_cur:
            lits_next.append(z3.substitute(lit, *cur_to_next))

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
        s.add(z3.substitute(ts.comb_expr, *cur_to_next))

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
        p_str = z3.simplify(P).sexpr() if not z3.is_true(P) and not z3.is_false(P) else str(P)
        for name in ts.state_vars:
            cur_str = f"__{name}__cur"
            if cur_str in p_str:
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
        p_str = z3.simplify(P).sexpr() if not z3.is_true(P) and not z3.is_false(P) else str(P)
        for name in ts.state_vars:
            cur_str = f"__{name}__cur"
            if cur_str in p_str:
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
        p_str = z3.simplify(P).sexpr() if not z3.is_true(P) and not z3.is_false(P) else str(P)
        for name in ts.state_vars:
            cur_str = f"__{name}__cur"
            if cur_str in p_str:
                p_var_strs.add(cur_str)

        cur_to_next = [(ts.get_cur(name), ts.get_next(name)) for name in ts.state_vars]
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

                s = z3.Solver()
                s.set("timeout", 200)
                if i == 0:
                    s.add(ts.init_expr)
                else:
                    for clause in frames[i - 1]:
                        s.add(clause)
                    s.add(P)
                s.add(ts.assumption_expr)
                s.add(ts.comb_expr)
                s.add(ts.trans_expr)
                s.add(z3.substitute(ts.comb_expr, *cur_to_next))
                s.add(z3.substitute(cand_expr, *cur_to_next))

                if s.check() == z3.unsat:
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
        ts_cn = z3.substitute(ts.comb_expr, *cur_to_next)

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
                    cn = z3.substitute(z3.Not(c), *cur_to_next)
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
                        cs.add(z3.substitute(z3.Not(c), *cur_to_next))
                        if cs.check() == z3.unsat:
                            self._add_clause(c, fi + 1, frames, ts)
                            prog = True
            if not prog:
                break
