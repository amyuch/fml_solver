import z3
import random
import math
from ..ir.transition_system import TransitionSystem


def _random_bitvec_val(rng, width):
    return z3.BitVecVal(rng.randint(0, (1 << width) - 1), width)


def simulation_falsify(ts, max_cycles=200, trials=5, seed=None, verbose=False):
    """Random simulation to find quick counterexamples.
    
    For each trial:
      1. Unfold TS for max_cycles
      2. Assign random concrete input values
      3. Check satisfiability with the solver
      4. If SAT, evaluate each property at each cycle
    
    Returns first CEX found, or None.
    """
    rng = random.Random(seed)
    timeout = min(ts.timeout, 10000)

    for trial in range(trials):
        solver = z3.Solver()
        solver.set("timeout", timeout)
        state_snaps = []
        input_snaps = []

        s0 = ts.state_vector("_sim0")
        state_snaps.append(s0)
        init_expr = z3.substitute(
            ts.init_expr,
            *[(ts.get_cur(name), s0[name]) for name in ts.state_vars]
        )
        solver.add(z3.simplify(init_expr))

        for step in range(max_cycles):
            si = state_snaps[step]
            si1 = ts.state_vector(f"_sim{step + 1}")
            inp = ts.input_vector(f"_sim_inp{step}")

            for name, iv in ts.inputs.items():
                val = rng.randint(0, (1 << iv.width) - 1)
                solver.add(inp[name] == z3.BitVecVal(val, iv.width))

            trans_expr = z3.substitute(
                ts.trans_expr,
                *[(ts.get_cur(name), si[name]) for name in ts.state_vars],
                *[(ts.get_next(name), si1[name]) for name in ts.state_vars],
                *[(ts.get_inp(name), inp[name]) for name in ts.inputs],
            )
            solver.add(z3.simplify(trans_expr))

            inp_map_comb = [(ts.get_inp(name), inp[name]) for name in ts.inputs]
            comb_expr = z3.substitute(
                ts.comb_expr,
                *[(ts.get_cur(name), si[name]) for name in ts.state_vars],
                *inp_map_comb,
            )
            solver.add(z3.simplify(comb_expr))

            for a in ts.assumptions:
                a_expr = z3.substitute(
                    a,
                    *[(ts.get_cur(name), si[name]) for name in ts.state_vars],
                    *inp_map_comb,
                )
                solver.add(z3.simplify(a_expr))

            state_snaps.append(si1)
            input_snaps.append(inp)

        result = solver.check()
        if result == z3.unsat:
            if verbose:
                print(f"  [sim] trial {trial}: unsat (random inputs violated constraints)")
            continue

        model = solver.model()

        for step in range(max_cycles):
            si = state_snaps[step]
            inp = input_snaps[step] if step < len(input_snaps) else None
            inp_map_here = [(ts.get_inp(name), inp[name]) for name in ts.inputs] if inp else []

            for pname, p_expr in ts.properties:
                p_at_k = z3.substitute(
                    p_expr,
                    *[(ts.get_cur(name), si[name]) for name in ts.state_vars],
                    *inp_map_here,
                )
                p_val = model.eval(p_at_k)
                if z3.is_false(p_val):
                    cex = _build_cex(model, ts, state_snaps, input_snaps, step)
                    if verbose:
                        print(f"  [sim] trial {trial}, cycle {step}: FAIL {pname}")
                    return {
                        "result": "fail",
                        "property": pname,
                        "engine": "simulation",
                        "bound": step,
                        "counterexample": cex,
                        "trace": _format_cex(cex, ts),
                    }

            for pname, p_expr in ts.trans_properties:
                if step < max_cycles - 1:
                    si1 = state_snaps[step + 1]
                    p_at_k = z3.substitute(
                        p_expr,
                        *[(ts.get_cur(name), si[name]) for name in ts.state_vars],
                        *[(ts.get_next(name), si1[name]) for name in ts.state_vars],
                        *inp_map_here,
                    )
                    p_val = model.eval(p_at_k)
                    if z3.is_false(p_val):
                        cex = _build_cex(model, ts, state_snaps, input_snaps, step + 1)
                        if verbose:
                            print(f"  [sim] trial {trial}, cycle {step}: FAIL {pname}")
                        return {
                            "result": "fail",
                            "property": pname,
                            "engine": "simulation",
                            "bound": step + 1,
                            "counterexample": cex,
                            "trace": _format_cex(cex, ts),
                        }

        if verbose:
            print(f"  [sim] trial {trial}: no failures in {max_cycles} cycles")

    return None


def simulation_cover(ts, max_cycles=200, trials=5, seed=None, verbose=False):
    """Random simulation to find cover property traces."""
    rng = random.Random(seed)
    timeout = min(ts.timeout, 10000)

    if not ts.cover_properties:
        return None

    results = []
    for pname, p_expr in ts.cover_properties:
        results.append({
            "property": pname,
            "result": "unknown",
            "engine": "simulation",
        })

    for trial in range(trials):
        solver = z3.Solver()
        solver.set("timeout", timeout)
        state_snaps = []
        input_snaps = []

        s0 = ts.state_vector("_sim0")
        state_snaps.append(s0)
        init_expr = z3.substitute(
            ts.init_expr,
            *[(ts.get_cur(name), s0[name]) for name in ts.state_vars]
        )
        solver.add(z3.simplify(init_expr))

        for step in range(max_cycles):
            si = state_snaps[step]
            si1 = ts.state_vector(f"_sim{step + 1}")
            inp = ts.input_vector(f"_sim_inp{step}")

            for name, iv in ts.inputs.items():
                val = rng.randint(0, (1 << iv.width) - 1)
                solver.add(inp[name] == z3.BitVecVal(val, iv.width))

            trans_expr = z3.substitute(
                ts.trans_expr,
                *[(ts.get_cur(name), si[name]) for name in ts.state_vars],
                *[(ts.get_next(name), si1[name]) for name in ts.state_vars],
                *[(ts.get_inp(name), inp[name]) for name in ts.inputs],
            )
            solver.add(z3.simplify(trans_expr))

            state_snaps.append(si1)
            input_snaps.append(inp)

        result = solver.check()
        if result == z3.unsat:
            continue

        model = solver.model()

        for step in range(max_cycles):
            si = state_snaps[step]
            inp = input_snaps[step] if step < len(input_snaps) else None
            inp_map_here = [(ts.get_inp(name), inp[name]) for name in ts.inputs] if inp else []

            for idx, (pname, p_expr) in enumerate(ts.cover_properties):
                if results[idx]["result"] == "reachable":
                    continue
                c_at_k = z3.substitute(
                    p_expr,
                    *[(ts.get_cur(name), si[name]) for name in ts.state_vars],
                    *inp_map_here,
                )
                c_val = model.eval(c_at_k)
                if z3.is_true(c_val):
                    cex = _build_cex(model, ts, state_snaps, input_snaps, step)
                    results[idx] = {
                        "property": pname,
                        "result": "reachable",
                        "engine": "simulation",
                        "bound": step,
                        "counterexample": cex,
                        "trace": _format_cex(cex, ts),
                    }
                    if verbose:
                        print(f"  [sim-cover] trial {trial}, cycle {step}: {pname} REACHABLE")

    return results


def _build_cex(model, ts, state_snaps, input_snaps, k_cycles):
    cex = []
    for step in range(k_cycles + 1):
        frame = {}
        si = state_snaps[step]
        for name in ts.state_vars:
            val = model.eval(si[name])
            frame[name] = val
        if step < len(input_snaps):
            inp = input_snaps[step]
            for name in ts.inputs:
                val = model.eval(inp[name])
                frame[f"{name}_inp"] = val
        cex.append(frame)
    return cex


def _format_cex(cex, ts):
    lines = ["=" * 60, "Random Simulation Counterexample:", "=" * 60]
    for step, frame in enumerate(cex):
        lines.append(f"\n--- Cycle {step} ---")
        for name in ts.state_vars:
            if name in frame:
                lines.append(f"  {name} = {frame[name]}")
        for key, val in frame.items():
            if key.endswith("_inp"):
                lines.append(f"  {key} = {val}")
    return "\n".join(lines)
