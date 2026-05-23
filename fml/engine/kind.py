import z3
from ..ir.transition_system import TransitionSystem


def _subst_state(ts, expr, states, idx):
    return z3.substitute(
        expr,
        *[(ts.get_cur(name), states[idx][name]) for name in ts.state_vars]
    )


def _subst_state_inp(ts, expr, states, inp, idx):
    inp_map = [(ts.get_inp(name), inp[idx][name]) for name in ts.inputs] if idx < len(inp) else []
    return z3.substitute(
        expr,
        *[(ts.get_cur(name), states[idx][name]) for name in ts.state_vars],
        *inp_map,
    )


def _subst_trans(ts, expr, states, inp, i):
    return z3.substitute(
        expr,
        *[(ts.get_cur(name), states[i][name]) for name in ts.state_vars],
        *[(ts.get_next(name), states[i + 1][name]) for name in ts.state_vars],
        *[(ts.get_inp(name), inp[i][name]) for name in ts.inputs],
    )


def _add_comb_per_state(solver, ts, states, inp, count):
    for i in range(count):
        c = _subst_state_inp(ts, ts.comb_expr, states, inp, i)
        if c is not None:
            solver.add(z3.simplify(c))


def _add_acts_per_state(solver, ts, states, inp, count):
    for i in range(count):
        c = _subst_state_inp(ts, ts.assumption_expr, states, inp, i)
        if c is not None:
            solver.add(z3.simplify(c))


def check_kinduction(ts: TransitionSystem, k: int, verbose: bool = True) -> dict:
    props = ts.properties
    trans_props = ts.trans_properties

    if not props and not trans_props:
        return {"result": "unknown", "reason": "no properties"}

    failures = []
    proved_count = 0
    total_count = 0

    for pname, p_expr in props:
        total_count += 1
        state_v = [ts.state_vector(f"_{i}") for i in range(k + 2)]
        inp_v = [ts.input_vector(f"_inp{i}") for i in range(k + 2)]

        base_s = z3.Solver()
        base_s.set("timeout", 60000)
        init_expr = _subst_state_inp(ts, ts.init_expr, state_v, inp_v, 0)
        base_s.add(z3.simplify(init_expr))
        _add_acts_per_state(base_s, ts, state_v, inp_v, k + 1)
        for i in range(k):
            trans_expr = _subst_trans(ts, ts.trans_expr, state_v, inp_v, i)
            base_s.add(z3.simplify(trans_expr))
        _add_comb_per_state(base_s, ts, state_v, inp_v, k + 1)
        viol = []
        for i in range(k + 1):
            viol.append(z3.simplify(z3.Not(_subst_state_inp(ts, p_expr, state_v, inp_v, i))))
        base_s.add(z3.Or(*viol))

        result = base_s.check()
        if result == z3.sat:
            failures.append({
                "result": "fail",
                "property": pname,
                "stage": "base",
                "bound": k,
            })
            continue

        ind_s = z3.Solver()
        ind_s.set("timeout", 60000)
        for i in range(k + 1):
            ind_s.add(z3.simplify(_subst_state_inp(ts, p_expr, state_v, inp_v, i)))
        _add_acts_per_state(ind_s, ts, state_v, inp_v, k + 2)
        for i in range(k + 1):
            trans_expr = _subst_trans(ts, ts.trans_expr, state_v, inp_v, i)
            ind_s.add(z3.simplify(trans_expr))
        _add_comb_per_state(ind_s, ts, state_v, inp_v, k + 2)
        ind_s.add(z3.simplify(z3.Not(_subst_state_inp(ts, p_expr, state_v, inp_v, k + 1))))

        result = ind_s.check()
        if result == z3.unsat:
            if verbose:
                print(f"  k-induction proved {pname} with k={k}")
            proved_count += 1

    for tpname, tp_expr in trans_props:
        total_count += 1
        if k < 1:
            continue

        state_v = [ts.state_vector(f"_{i}") for i in range(k + 3)]
        inp_v = [ts.input_vector(f"_inp{i}") for i in range(k + 2)]

        base_s = z3.Solver()
        base_s.set("timeout", 60000)
        init_expr = _subst_state(ts, ts.init_expr, state_v, 0)
        base_s.add(z3.simplify(init_expr))
        _add_acts_per_state(base_s, ts, state_v, inp_v, k + 2)
        for i in range(k):
            trans_expr = _subst_trans(ts, ts.trans_expr, state_v, inp_v, i)
            base_s.add(z3.simplify(trans_expr))
        _add_comb_per_state(base_s, ts, state_v, inp_v, k + 1)
        viol = []
        for i in range(k):
            viol.append(z3.simplify(z3.Not(_subst_trans(ts, tp_expr, state_v, inp_v, i))))
        base_s.add(z3.Or(*viol))

        result = base_s.check()
        if result == z3.sat:
            failures.append({
                "result": "fail",
                "property": tpname,
                "stage": "base",
                "bound": k,
            })
            continue

        ind_s = z3.Solver()
        ind_s.set("timeout", 60000)
        for i in range(k + 1):
            ind_s.add(z3.simplify(_subst_trans(ts, tp_expr, state_v, inp_v, i)))
        _add_acts_per_state(ind_s, ts, state_v, inp_v, k + 3)
        for i in range(k + 2):
            trans_expr = _subst_trans(ts, ts.trans_expr, state_v, inp_v, i)
            ind_s.add(z3.simplify(trans_expr))
        _add_comb_per_state(ind_s, ts, state_v, inp_v, k + 3)
        ind_s.add(z3.simplify(z3.Not(_subst_trans(ts, tp_expr, state_v, inp_v, k + 1))))

        result = ind_s.check()
        if result == z3.unsat:
            if verbose:
                print(f"  k-induction proved {tpname} with k={k}")
            proved_count += 1

    if failures:
        first = failures[0]
        first["failures"] = failures
        return first

    if total_count > 0 and proved_count == total_count:
        return {"result": "proved", "bound": k}
    return {"result": "unknown", "bound": k}
