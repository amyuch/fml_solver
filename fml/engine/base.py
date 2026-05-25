import z3
from ..ir.transition_system import TransitionSystem


class EngineBase:
    def __init__(self, ts: TransitionSystem, max_frames: int = 20):
        self.ts = ts
        self.max_frames = max_frames
        self._time_elapsed = 0.0

    @property
    def time_elapsed(self) -> float:
        return self._time_elapsed

    def run(self) -> dict:
        raise NotImplementedError
