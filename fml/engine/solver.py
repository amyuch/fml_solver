import z3
from typing import Optional, Any
from ..ir.transition_system import TransitionSystem


class SolverContext:
    def __init__(self):
        self.solver = z3.Solver()
        self.solver.set("timeout", 60000)

    def push(self):
        self.solver.push()

    def pop(self):
        self.solver.pop()

    def add(self, expr: z3.BoolRef):
        self.solver.add(expr)

    def check(self) -> z3.CheckSatResult:
        return self.solver.check()

    def model(self) -> z3.ModelRef:
        return self.solver.model()

    def reset(self):
        self.solver.reset()


def unfold_transition_system(
    ts: TransitionSystem, k: int
) -> tuple[list[dict[str, z3.BitVecRef]], list[dict[str, z3.BitVecRef]], z3.Solver]:
    solver = z3.Solver()
    solver.set("timeout", 60000)

    state_snapshots = []
    input_snapshots = []

    s0 = ts.state_vector("_0")
    state_snapshots.append(s0)

    init_expr = z3.substitute(
        ts.init_expr,
        *[(ts.get_cur(name), s0[name]) for name in ts.state_vars]
    )
    solver.add(z3.simplify(init_expr))

    for step in range(k):
        si = state_snapshots[step]
        si1 = ts.state_vector(f"_{step+1}")
        inp = ts.input_vector(f"_inp{step}")

        trans_expr = z3.substitute(
            ts.trans_expr,
            *[(ts.get_cur(name), si[name]) for name in ts.state_vars],
            *[(ts.get_next(name), si1[name]) for name in ts.state_vars],
            *[(ts.get_inp(name), inp[name]) for name in ts.inputs],
        )

        solver.add(z3.simplify(trans_expr))
        state_snapshots.append(si1)
        input_snapshots.append(inp)

        for a in ts.assumptions:
            a_expr = z3.substitute(
                a,
                *[(ts.get_cur(name), si[name]) for name in ts.state_vars],
                *[(ts.get_inp(name), inp[name]) for name in ts.inputs],
            )
            solver.add(z3.simplify(a_expr))

    for step in range(k + 1):
        si = state_snapshots[step]
        inp_map = []
        if step < len(input_snapshots):
            inp = input_snapshots[step]
            inp_map = [(ts.get_inp(name), inp[name]) for name in ts.inputs]
        comb_expr = z3.substitute(
            ts.comb_expr,
            *[(ts.get_cur(name), si[name]) for name in ts.state_vars],
            *inp_map,
        )
        if comb_expr is not None:
            solver.add(z3.simplify(comb_expr))

    return state_snapshots, input_snapshots, solver


def extract_counterexample(
    model: z3.ModelRef,
    ts: TransitionSystem,
    state_snapshots: list[dict[str, z3.BitVecRef]],
    input_snapshots: list[dict[str, z3.BitVecRef]],
    k: int,
):
    cex = []
    for step in range(k + 1):
        frame = {}
        for name in ts.state_vars:
            val = model.eval(state_snapshots[step][name])
            frame[name] = val
        if step < k:
            for name in ts.inputs:
                val = model.eval(input_snapshots[step][name])
                frame[f"{name}_inp"] = val
        cex.append(frame)
    return cex


def format_counterexample(cex: list[dict], ts: TransitionSystem) -> str:
    lines = ["=" * 60, "Counterexample Trace:", "=" * 60]
    for step, frame in enumerate(cex):
        lines.append(f"\n--- Cycle {step} ---")
        for name in ts.state_vars:
            if name in frame:
                val = frame[name]
                if val is not None:
                    lines.append(f"  {name} = {val}")
        for key, val in frame.items():
            if key.endswith("_inp"):
                lines.append(f"  {key} = {val}")
    return "\n".join(lines)
