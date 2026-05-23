import z3
from .solver import (
    SolverContext, unfold_transition_system,
    extract_counterexample, format_counterexample
)
from ..ir.transition_system import TransitionSystem


def _bmc_check_one(ts, pname, p_expr, k, is_trans=False):
    state_snapshots, input_snapshots, solver = unfold_transition_system(ts, k)

    if not is_trans:
        p_at_k = z3.substitute(
            p_expr,
            *[(ts.get_cur(name), state_snapshots[k][name]) for name in ts.state_vars]
        )
        solver.add(z3.simplify(z3.Not(p_at_k)))
    else:
        if k < 1:
            return None
        tp_violations = []
        for i in range(k):
            tp_at_i = z3.substitute(
                p_expr,
                *[(ts.get_cur(name), state_snapshots[i][name]) for name in ts.state_vars],
                *[(ts.get_next(name), state_snapshots[i+1][name]) for name in ts.state_vars],
                *[(ts.get_inp(name), input_snapshots[i][name]) for name in ts.inputs],
            )
            tp_violations.append(z3.simplify(z3.Not(tp_at_i)))
        if not tp_violations:
            return None
        solver.add(z3.Or(*tp_violations))

    result = solver.check()
    if result == z3.sat:
        model = solver.model()
        cex = extract_counterexample(model, ts, state_snapshots, input_snapshots, k)
        return {
            "result": "fail",
            "property": pname,
            "bound": k,
            "counterexample": cex,
            "trace": format_counterexample(cex, ts),
        }
    return None


def check_bmc(ts: TransitionSystem, k: int) -> dict:
    if not ts.properties and not ts.trans_properties:
        return {"result": "unknown", "reason": "no properties"}

    for pname, p_expr in ts.properties:
        r = _bmc_check_one(ts, pname, p_expr, k)
        if r is not None:
            return r

    for tpname, tp_expr in ts.trans_properties:
        r = _bmc_check_one(ts, tpname, tp_expr, k, is_trans=True)
        if r is not None:
            return r

    return {"result": "pass", "bound": k}


def bmc_incremental(ts: TransitionSystem, max_k: int, verbose: bool = True) -> dict:
    if not ts.properties and not ts.trans_properties:
        return {"result": "unknown", "reason": "no properties"}

    failures = []

    for pname, p_expr in ts.properties:
        if verbose:
            print(f"  BMC binary search [0, {max_k}] for {pname}...")
        lo, hi = 0, max_k
        best = None
        while lo <= hi:
            mid = (lo + hi) // 2
            if verbose:
                print(f"    depth: {mid}...")
            r = _bmc_check_one(ts, pname, p_expr, mid)
            if r is not None:
                best = r
                hi = mid - 1
            else:
                lo = mid + 1
        if best is not None:
            failures.append(best)

    for tpname, tp_expr in ts.trans_properties:
        if verbose:
            print(f"  BMC binary search [0, {max_k}] for {tpname}...")
        lo, hi = 1, max_k
        best = None
        while lo <= hi:
            mid = (lo + hi) // 2
            if verbose:
                print(f"    depth: {mid}...")
            r = _bmc_check_one(ts, tpname, tp_expr, mid, is_trans=True)
            if r is not None:
                best = r
                hi = mid - 1
            else:
                lo = mid + 1
        if best is not None:
            failures.append(best)

    if failures:
        first = failures[0]
        if verbose:
            names = ", ".join(f.get("property", "?") for f in failures)
            print(f"  Failures: {names}")
        first["failures"] = failures
        return first

    return {"result": "pass", "bound": max_k}