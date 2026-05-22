import z3
from .solver import (
    SolverContext, unfold_transition_system,
    extract_counterexample, format_counterexample
)
from ..ir.transition_system import TransitionSystem


def check_bmc(ts: TransitionSystem, k: int, verbose: bool = True) -> dict:
    props = ts.properties
    trans_props = ts.trans_properties

    if not props and not trans_props:
        return {"result": "unknown", "reason": "no properties"}

    for pname, p_expr in props:
        state_snapshots, input_snapshots, solver = unfold_transition_system(ts, k)

        p_at_k = z3.substitute(
            p_expr,
            *[(ts.get_cur(name), state_snapshots[k][name]) for name in ts.state_vars]
        )

        solver.add(z3.simplify(z3.Not(p_at_k)))

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

    for tpname, tp_expr in trans_props:
        if k < 1:
            continue
        state_snapshots, input_snapshots, solver = unfold_transition_system(ts, k)

        tp_violations = []
        for i in range(k):
            tp_at_i = z3.substitute(
                tp_expr,
                *[(ts.get_cur(name), state_snapshots[i][name]) for name in ts.state_vars],
                *[(ts.get_next(name), state_snapshots[i+1][name]) for name in ts.state_vars],
                *[(ts.get_inp(name), input_snapshots[i][name]) for name in ts.inputs],
            )
            tp_violations.append(z3.simplify(z3.Not(tp_at_i)))

        solver.add(z3.Or(*tp_violations))

        result = solver.check()
        if result == z3.sat:
            model = solver.model()
            cex = extract_counterexample(model, ts, state_snapshots, input_snapshots, k)
            return {
                "result": "fail",
                "property": tpname,
                "bound": k,
                "counterexample": cex,
                "trace": format_counterexample(cex, ts),
            }

    return {"result": "pass", "bound": k}


def bmc_incremental(ts: TransitionSystem, max_k: int, verbose: bool = True) -> dict:
    for k in range(max_k + 1):
        if verbose:
            print(f"  BMC depth: {k}...")
        result = check_bmc(ts, k, verbose=False)
        if result["result"] == "fail":
            return result
    return {"result": "pass", "bound": max_k}
