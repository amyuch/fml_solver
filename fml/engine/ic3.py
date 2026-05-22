import z3
from ..ir.transition_system import TransitionSystem
from .kind import check_kinduction


class IC3:
    def __init__(self, ts: TransitionSystem, max_frames: int = 20, max_blocking: int = 100):
        self.ts = ts
        self.max_frames = max_frames
        self.max_blocking = max_blocking

    def prove(self, verbose: bool = True) -> dict:
        ts = self.ts
        if not ts.properties and not ts.trans_properties:
            return {"result": "unknown", "reason": "no properties"}

        for pname, p_expr in ts.properties:
            result = self._prove_property(p_expr, pname, verbose)
            if result["result"] in ("fail", "proved"):
                return result

        for tpname, _ in ts.trans_properties:
            if verbose:
                print(f"  IC3 (k-ind fallback) proving: {tpname}")
            result = check_kinduction(ts, self.max_frames, verbose=verbose)
            if result["result"] in ("fail", "proved"):
                return {"result": result["result"], "property": tpname,
                        "k": result.get("k"), "trace": result.get("trace")}

        return {"result": "unknown", "bound": self.max_frames}

    def _prove_property(self, P: z3.BoolRef, pname: str, verbose: bool) -> dict:
        ts = self.ts
        cur_to_next = [(ts.get_cur(name), ts.get_next(name)) for name in ts.state_vars]
        P_next = z3.substitute(P, *cur_to_next)

        # Base case: check if any initial state violates P
        s0 = z3.Solver()
        s0.set("timeout", 60000)
        s0.add(ts.init_expr)
        s0.add(z3.Not(P))
        if s0.check() == z3.sat:
            if verbose:
                print(f"      counterexample at initial state")
            return {"result": "fail", "property": pname, "bound": 0}

        # Add P to frame 1 (all frames ≥1 implicitly include P)
        frames: list[list[z3.BoolRef]] = [[] for _ in range(self.max_frames + 2)]

        if verbose:
            print(f"  IC3 proving: {pname}")

        for k in range(1, self.max_frames + 1):
            if verbose:
                print(f"    frame {k}")

            blocked = self._strengthen_frame(k, frames, P, P_next, ts, verbose)
            if blocked is False:
                if verbose:
                    print(f"      converged at frame {k}")
                return {"result": "proved", "property": pname, "k": k}
            if isinstance(blocked, dict):
                return blocked

        return {"result": "unknown", "property": pname, "bound": self.max_frames}

    def _strengthen_frame(self, k, frames, P, P_next, ts, verbose):
        for attempt in range(self.max_blocking):
            s = z3.Solver()
            s.set("timeout", 60000)

            for clause in frames[k - 1]:
                s.add(clause)
            s.add(P)
            s.add(ts.comb_expr)
            s.add(ts.trans_expr)
            s.add(z3.substitute(ts.comb_expr,
                  *[(ts.get_cur(name), ts.get_next(name)) for name in ts.state_vars]))
            s.add(z3.Not(P_next))

            result = s.check()
            if result == z3.unsat:
                # No bad states reachable via F[k-1]
                return self._try_convergence(k, frames)

            model = s.model()
            bad_cube_parts = []
            for name in ts.state_vars:
                val = model.eval(ts.get_cur(name))
                bad_cube_parts.append(ts.get_cur(name) == val)
            bad_cube = z3.And(*bad_cube_parts)

            if verbose:
                print(f"      CTI: {bad_cube}")

            # Try to block this cube. _block_cube adds ¬bad_cube to frames on success.
            ok = self._block_cube(bad_cube, k - 1, frames, P, ts)
            if not ok:
                return {"result": "fail", "cube": bad_cube}
            # cube blocked; continue finding more CTIs

        return None

    def _block_cube(self, cube, max_i, frames, P, ts):
        """Try to block cube. On success, adds ¬cube to frames[0..max_i]."""
        cur_to_next = [(ts.get_cur(name), ts.get_next(name)) for name in ts.state_vars]
        i = max_i
        while i >= 0:
            s = z3.Solver()
            s.set("timeout", 60000)

            if i == 0:
                s.add(ts.init_expr)
            else:
                for clause in frames[i - 1]:
                    s.add(clause)
                s.add(P)

            s.add(ts.comb_expr)
            s.add(ts.trans_expr)
            s.add(z3.substitute(ts.comb_expr, *cur_to_next))
            cube_next = z3.substitute(
                cube,
                *[(ts.get_cur(name), ts.get_next(name)) for name in ts.state_vars]
            )
            s.add(cube_next)

            check = s.check()
            if check == z3.sat:
                model = s.model()
                pred_parts = []
                for name in ts.state_vars:
                    val = model.eval(ts.get_cur(name))
                    pred_parts.append(ts.get_cur(name) == val)
                pred_cube = z3.And(*pred_parts)

                ok = self._block_cube(pred_cube, i - 1, frames, P, ts)
                if not ok:
                    return False

                # Predecessor blocked. Retry at same i — the new clause
                # in frames[0..max_i] may make cube unreachable at this level.
                self._add_to_frames(z3.Not(pred_cube), max_i, frames, P, ts)
                continue
            else:
                # Cube blocked at frame i.
                self._add_to_frames(z3.Not(cube), max_i, frames, P, ts)
                return True

        return False

    def _add_to_frames(self, clause, up_to, frames, P, ts):
        """Add clause to frames 0..up_to and propagate forward."""
        cur_to_next = [(ts.get_cur(name), ts.get_next(name)) for name in ts.state_vars]
        for i in range(up_to + 1):
            if clause not in frames[i]:
                frames[i].append(clause)

        # Propagate to higher frames
        for i in range(up_to + 1, len(frames) - 1):
            s = z3.Solver()
            s.set("timeout", 60000)
            for c in frames[i]:
                s.add(c)
            if i >= 1:
                s.add(P)
            s.add(ts.comb_expr)
            s.add(ts.trans_expr)
            s.add(z3.substitute(ts.comb_expr, *cur_to_next))
            clause_next = z3.substitute(
                clause,
                *[(ts.get_cur(name), ts.get_next(name)) for name in ts.state_vars]
            )
            s.add(z3.Not(clause_next))

            if s.check() == z3.unsat:
                if clause not in frames[i + 1]:
                    frames[i + 1].append(clause)
            else:
                break

    def _try_convergence(self, k, frames):
        if k < 2:
            return True
        f_prev = set(str(c) for c in frames[k - 1])
        f_curr = set(str(c) for c in frames[k])
        if f_prev == f_curr:
            return False  # converged
        return True  # continue
