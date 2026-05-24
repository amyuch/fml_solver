import z3
from ..ir.transition_system import TransitionSystem


def _collect_var_refs(expr, ts):
    """Walk a Z3 expression and collect referenced variable names.

    Returns:
        state_vars: set of state variable names referenced
        inputs: set of input names referenced
        next_vars: set of next-state variable names referenced
    """
    state_vars = set()
    inputs = set()
    next_vars = set()

    seen = set()

    def walk(e):
        if e is None:
            return
        e_id = z3.get_id(e) if hasattr(z3, 'get_id') else id(e)
        if e_id in seen:
            return
        seen.add(e_id)

        if z3.is_const(e) and z3.is_app(e):
            try:
                name = str(e)
            except Exception:
                name = ""
            if name in ts.state_vars:
                state_vars.add(name)
                return
            if name.endswith("_inp") and name[:-4] in ts.inputs:
                inputs.add(name[:-4])
                return
            if name.endswith("_next") and name[:-5] in ts.state_vars:
                next_vars.add(name[:-5])
                return
            if name in ts.inputs:
                inputs.add(name)
                return

        for child in e.children():
            walk(child)

    walk(expr)
    return state_vars, inputs, next_vars


def compute_fanin_cone(ts, property_expr):
    """Compute the transitive fan-in cone for a property expression.

    Traces backwards through next-state assignments and constraints
    to find all state variables and inputs that influence the property.
    """
    all_state = set(ts.state_vars.keys())
    all_inputs = set(ts.inputs.keys())

    # Directly referenced variables
    direct_state, direct_inputs, direct_next = _collect_var_refs(property_expr, ts)

    relevant_state = set(direct_state)
    relevant_inputs = set(direct_inputs)
    relevant_next = set(direct_next)

    # Transitive closure over dependency graph
    # If var A's next-state depends on var B, then B influences A
    # If var A's next-state depends on input I, then I influences A
    frontier = set(relevant_state) | set(relevant_next)
    if not frontier:
        frontier = set(all_state)

    visited = set()

    while frontier:
        vname = frontier.pop()
        if vname in visited:
            continue
        visited.add(vname)

        # Check next-state assignment for this variable
        if vname in ts._next_state_exprs:
            nxt_expr = ts._next_state_exprs[vname]
            deps_state, deps_inp, deps_next = _collect_var_refs(nxt_expr, ts)
            for d in deps_state:
                if d not in visited and d not in frontier:
                    frontier.add(d)
                relevant_state.add(d)
            for d in deps_inp:
                relevant_inputs.add(d)
            for d in deps_next:
                if d not in visited and d not in frontier:
                    frontier.add(d)
                relevant_next.add(d)
                relevant_state.add(d)

        # Check trans constraints for dependencies
        for tc in ts._trans_constraints:
            deps_state, deps_inp, deps_next = _collect_var_refs(tc, ts)
            if vname in deps_state or vname in deps_next:
                for d in deps_state:
                    if d not in visited and d not in frontier:
                        frontier.add(d)
                    relevant_state.add(d)
                for d in deps_inp:
                    relevant_inputs.add(d)
                for d in deps_next:
                    if d not in visited and d not in frontier:
                        frontier.add(d)
                    relevant_next.add(d)
                    relevant_state.add(d)

        # Check comb constraints for dependencies
        for cc in ts._comb_constraints:
            deps_state, deps_inp, deps_next = _collect_var_refs(cc, ts)
            if vname in deps_state:
                for d in deps_state:
                    if d not in visited and d not in frontier:
                        frontier.add(d)
                    relevant_state.add(d)
                for d in deps_inp:
                    relevant_inputs.add(d)

    return relevant_state, relevant_inputs


def summarize_cone(ts, property_expr):
    s_vars, i_vars = compute_fanin_cone(ts, property_expr)
    lines = [
        f"Fan-in cone: {len(s_vars)} state vars, {len(i_vars)} inputs",
        f"  State vars in cone: {sorted(s_vars)}",
        f"  Inputs in cone: {sorted(i_vars)}",
    ]
    total_state = len(ts.state_vars)
    total_inp = len(ts.inputs)
    if total_state > 0:
        pct = len(s_vars) / total_state * 100
        lines.append(f"  Reduction: {total_state - len(s_vars)}/{total_state} state vars pruned ({pct:.1f}% kept)")
    return "\n".join(lines)
