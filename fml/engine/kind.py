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
    max_k = k
    if not ts.properties and not ts.trans_properties:
        return {"result": "unknown", "reason": "no properties"}

    failures = []
    unproved = set()
    for pname, _ in ts.properties:
        unproved.add(("state", pname))
    for tpname, _ in ts.trans_properties:
        unproved.add(("trans", tpname))

    for kk in range(1, max_k + 1):
        if not unproved:
            break

        to_remove = []
        for ptype, pname in list(unproved):
            if ptype == "state":
                p_expr = dict(ts.properties).get(pname)
                if p_expr is None:
                    to_remove.append((ptype, pname))
                    continue

                state_v = [ts.state_vector(f"_{i}") for i in range(kk + 2)]
                inp_v = [ts.input_vector(f"_inp{i}") for i in range(kk + 2)]

                base_s = z3.Solver()
                base_s.set("timeout", ts.timeout)
                init_expr = _subst_state_inp(ts, ts.init_expr, state_v, inp_v, 0)
                base_s.add(z3.simplify(init_expr))
                _add_acts_per_state(base_s, ts, state_v, inp_v, kk + 1)
                for i in range(kk):
                    trans_expr = _subst_trans(ts, ts.trans_expr, state_v, inp_v, i)
                    base_s.add(z3.simplify(trans_expr))
                _add_comb_per_state(base_s, ts, state_v, inp_v, kk + 1)
                viol = []
                for i in range(kk + 1):
                    viol.append(z3.simplify(z3.Not(_subst_state_inp(ts, p_expr, state_v, inp_v, i))))
                base_s.add(z3.Or(*viol))

                result = base_s.check()
                if result == z3.sat:
                    failures.append({
                        "result": "fail", "property": pname, "stage": "base", "bound": kk,
                    })
                    to_remove.append((ptype, pname))
                    continue

                ind_s = z3.Solver()
                ind_s.set("timeout", ts.timeout)
                for i in range(kk + 1):
                    ind_s.add(z3.simplify(_subst_state_inp(ts, p_expr, state_v, inp_v, i)))
                _add_acts_per_state(ind_s, ts, state_v, inp_v, kk + 2)
                for i in range(kk + 1):
                    trans_expr = _subst_trans(ts, ts.trans_expr, state_v, inp_v, i)
                    ind_s.add(z3.simplify(trans_expr))
                _add_comb_per_state(ind_s, ts, state_v, inp_v, kk + 2)
                ind_s.add(z3.simplify(z3.Not(_subst_state_inp(ts, p_expr, state_v, inp_v, kk + 1))))

                ind_result = ind_s.check()
                if ind_result == z3.unsat:
                    if verbose:
                        print(f"  k-induction proved {pname} with k={kk}")
                    to_remove.append((ptype, pname))

            elif ptype == "trans":
                tp_expr = dict(ts.trans_properties).get(pname)
                if tp_expr is None:
                    to_remove.append((ptype, pname))
                    continue

                state_v = [ts.state_vector(f"_{i}") for i in range(kk + 3)]
                inp_v = [ts.input_vector(f"_inp{i}") for i in range(kk + 2)]

                base_s = z3.Solver()
                base_s.set("timeout", ts.timeout)
                init_expr = _subst_state(ts, ts.init_expr, state_v, 0)
                base_s.add(z3.simplify(init_expr))
                _add_acts_per_state(base_s, ts, state_v, inp_v, kk + 2)
                for i in range(kk):
                    trans_expr = _subst_trans(ts, ts.trans_expr, state_v, inp_v, i)
                    base_s.add(z3.simplify(trans_expr))
                _add_comb_per_state(base_s, ts, state_v, inp_v, kk + 1)
                viol = []
                for i in range(kk):
                    viol.append(z3.simplify(z3.Not(_subst_trans(ts, tp_expr, state_v, inp_v, i))))
                base_s.add(z3.Or(*viol))

                result = base_s.check()
                if result == z3.sat:
                    failures.append({
                        "result": "fail", "property": pname, "stage": "base", "bound": kk,
                    })
                    to_remove.append((ptype, pname))
                    continue

                ind_s = z3.Solver()
                ind_s.set("timeout", ts.timeout)
                for i in range(kk + 1):
                    ind_s.add(z3.simplify(_subst_trans(ts, tp_expr, state_v, inp_v, i)))
                _add_acts_per_state(ind_s, ts, state_v, inp_v, kk + 3)
                for i in range(kk + 2):
                    trans_expr = _subst_trans(ts, ts.trans_expr, state_v, inp_v, i)
                    ind_s.add(z3.simplify(trans_expr))
                _add_comb_per_state(ind_s, ts, state_v, inp_v, kk + 3)
                ind_s.add(z3.simplify(z3.Not(_subst_trans(ts, tp_expr, state_v, inp_v, kk + 1))))

                ind_result = ind_s.check()
                if ind_result == z3.unsat:
                    if verbose:
                        print(f"  k-induction proved {pname} with k={kk}")
                    to_remove.append((ptype, pname))

        for item in to_remove:
            unproved.discard(item)

    if failures:
        first = failures[0]
        first["failures"] = failures
        return first

    if not unproved:
        return {"result": "proved", "bound": max_k}
    return {"result": "unknown", "bound": max_k}
