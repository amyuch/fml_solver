import z3
from ..ir.transition_system import TransitionSystem


def cover_bmc(ts, max_cycles=200, verbose=False, timeout=10000):
    """BMC-based cover property reachability analysis.

    Incrementally unrolls the transition system up to max_cycles
    and checks if each cover target is reachable.

    Returns a list of result dicts (one per cover property).
    """
    if not ts.cover_properties:
        return None

    results = []
    base_solver = z3.Solver()
    base_solver.set("timeout", timeout)

    s0 = ts.state_vector("_cv0")
    init_expr = z3.substitute(
        ts.init_expr,
        *[(ts.get_cur(name), s0[name]) for name in ts.state_vars]
    )
    base_solver.add(z3.simplify(init_expr))

    state_vecs = [s0]
    input_vecs = []

    for pname, p_expr in ts.cover_properties:
        res = _check_one_cover(
            ts, pname, p_expr, base_solver, state_vecs, input_vecs,
            max_cycles, verbose, timeout
        )
        results.append(res)

    return results


def _check_one_cover(ts, pname, p_expr, base_solver, state_vecs, input_vecs,
                     max_cycles, verbose, timeout):
    solver = z3.Solver()
    solver.set("timeout", timeout)
    solver.add(base_solver.assertions())

    local_sv = list(state_vecs)
    local_iv = list(input_vecs)

    # Build the unrolling incrementally
    for step in range(max_cycles + 1):
        if step == 0:
            si = local_sv[0]
        else:
            si_idx = step
            while len(local_sv) <= si_idx:
                # Need to extend the unrolling
                prev_idx = len(local_sv) - 1
                sp = local_sv[prev_idx]
                sn = ts.state_vector(f"_cv{prev_idx + 1}")
                inp = ts.input_vector(f"_cv_inp{prev_idx}")

                trans_expr = z3.substitute(
                    ts.trans_expr,
                    *[(ts.get_cur(name), sp[name]) for name in ts.state_vars],
                    *[(ts.get_next(name), sn[name]) for name in ts.state_vars],
                    *[(ts.get_inp(name), inp[name]) for name in ts.inputs],
                )
                solver.add(z3.simplify(trans_expr))

                inp_map = [(ts.get_inp(name), inp[name]) for name in ts.inputs]
                comb_expr = z3.substitute(
                    ts.comb_expr,
                    *[(ts.get_cur(name), sn[name]) for name in ts.state_vars],
                    *inp_map,
                )
                solver.add(z3.simplify(comb_expr))

                for a in ts.assumptions:
                    a_expr = z3.substitute(
                        a,
                        *[(ts.get_cur(name), sn[name]) for name in ts.state_vars],
                        *inp_map,
                    )
                    solver.add(z3.simplify(a_expr))

                local_sv.append(sn)
                local_iv.append(inp)

            si = local_sv[si_idx]

        # Build the cover condition at this state
        inp_at_k = local_iv[step - 1] if step > 0 else None
        sub_map = [(ts.get_cur(name), si[name]) for name in ts.state_vars]
        if inp_at_k is not None:
            sub_map += [(ts.get_inp(name), inp_at_k[name]) for name in ts.inputs]

        c_at_k = z3.substitute(p_expr, *sub_map)

        solver.push()
        solver.add(z3.simplify(c_at_k))
        chk = solver.check()

        if chk == z3.sat:
            try:
                model = solver.model()
            except Exception:
                solver.pop()
                continue
            solver.pop()
            cex = _build_cex(model, ts, local_sv, local_iv, step)
            if verbose:
                print(f"  [cover-bmc] {pname} REACHABLE at depth {step}")
            return {
                "property": pname,
                "result": "reachable",
                "engine": "cover_bmc",
                "bound": step,
                "counterexample": cex,
                "trace": _format_cex(cex, ts),
            }

        solver.pop()

    if verbose:
        print(f"  [cover-bmc] {pname}: not reachable within {max_cycles}")
    return {
        "property": pname,
        "result": "unknown",
        "engine": "cover_bmc",
        "reason": f"not reachable within {max_cycles} cycles",
    }


def _build_cex(model, ts, state_vecs, input_vecs, k):
    cex = []
    for step in range(k + 1):
        frame = {}
        si = state_vecs[step]
        for name in ts.state_vars:
            val = model.eval(si[name])
            w = ts.state_vars[name].width
            try:
                ival = val.as_long()
            except Exception:
                ival = 0
            frame[name] = (ival, w)
        if step < len(input_vecs):
            inp = input_vecs[step]
            for name in ts.inputs:
                if name == "clk":
                    continue
                val = model.eval(inp[name])
                w = ts.inputs[name].width
                try:
                    ival = val.as_long()
                except Exception:
                    ival = 0
                frame[f"{name}_inp"] = (ival, w)
        cex.append(frame)
    return cex


def _format_cex(cex, ts):
    lines = [f"  Cover trace ({len(cex)} cycles):"]
    for step, frame in enumerate(cex):
        parts = [f"    Cycle {step}: "]
        svs = []
        for name in ts.state_vars:
            val, w = frame.get(name, (0, 1))
            if w <= 8:
                svs.append(f"{name}={val}")
            else:
                svs.append(f"{name}=0x{val:0{w//4}x}")
        parts.append(", ".join(svs))
        for name in ts.inputs:
            if name == "clk":
                continue
            key = f"{name}_inp"
            if key in frame:
                val, w = frame[key]
                if w == 1:
                    parts.append(f" {name}={val}")
        lines.append("".join(parts))
    return "\n".join(lines)
