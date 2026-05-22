import z3
from ..ir.transition_system import TransitionSystem
from .solver import format_counterexample
from .kind import check_kinduction


class IC3:
    def __init__(self, ts: TransitionSystem, max_frames: int = 20):
        self.ts = ts
        self.max_frames = max_frames

    def prove(self, verbose: bool = True) -> dict:
        ts = self.ts
        if not ts.properties and not ts.trans_properties:
            return {"result": "unknown", "reason": "no properties"}

        for k in range(1, self.max_frames + 1):
            result = check_kinduction(ts, k, verbose=verbose)
            if result["result"] in ("fail", "proved"):
                return result
        return {"result": "unknown", "bound": self.max_frames}
