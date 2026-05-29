import z3
from typing import Optional


class StateVar:
    def __init__(self, name: str, width: int, init_val: int = 0):
        self.name = name
        self.width = width
        self.init_val = init_val

    def __repr__(self):
        return f"StateVar({self.name}, {self.width}, init={self.init_val})"


class TransitionSystem:
    def __init__(self, name: str = "design", timeout: int = 60000):
        self.name = name
        self.timeout = timeout
        self.state_vars: dict[str, StateVar] = {}
        self.inputs: dict[str, StateVar] = {}
        self.params: dict[str, tuple[int, int | None]] = {}
        self._param_dims: dict[str, list[int]] = {}
        self.signed_vars: set[str] = set()
        self._cur: dict[str, z3.BitVec] = {}
        self._next: dict[str, z3.BitVec] = {}
        self._inps: dict[str, z3.BitVec] = {}
        self._init_constraints: list[z3.BoolRef] = []
        self._trans_constraints: list[z3.BoolRef] = []
        self.properties: list[tuple[str, z3.BoolRef]] = []
        self.trans_properties: list[tuple[str, z3.BoolRef]] = []
        self.cover_properties: list[tuple[str, z3.BoolRef]] = []
        self.assumptions: list[z3.BoolRef] = []
        self._comb_constraints: list[z3.BoolRef] = []
        self._next_state_exprs: dict[str, z3.BitVec] = {}
        self._var_dims: dict[str, list[int]] = {}  # var_name -> [dim_size, ...]
        self._var_num_packed: dict[str, int] = {}  # var_name -> num_packed_dims
        self.prop_sources: dict[str, str] = {}  # property_name -> original assertion text
        self.trans_prop_sources: dict[str, str] = {}
        self.cover_prop_sources: dict[str, str] = {}
        self.assumption_sources: dict[int, str] = {}  # index -> source text
        self._comb_targets: set[str] = set()  # state var names defined by comb constraints

    def add_state_var(self, name: str, width: int, init_val: int = 0, signed: bool = False):
        sv = StateVar(name, width, init_val)
        self.state_vars[name] = sv
        self._cur[name] = z3.BitVec(f"{name}", width)
        self._next[name] = z3.BitVec(f"{name}_next", width)
        if signed:
            self.signed_vars.add(name)

    def widen_state_var(self, name: str, new_width: int):
        if name not in self.state_vars:
            return
        old_sv = self.state_vars[name]
        if new_width <= old_sv.width:
            return
        self.state_vars[name] = StateVar(name, new_width, old_sv.init_val)
        self._cur[name] = z3.BitVec(f"{name}", new_width)
        self._next[name] = z3.BitVec(f"{name}_next", new_width)

    def _remove_init_constraint(self, name: str):
        self._init_constraints = [
            c for c in self._init_constraints
            if not (isinstance(c, z3.BoolRef) and name in str(c))
        ]

    def add_input(self, name: str, width: int, signed: bool = False):
        iv = StateVar(name, width)
        self.inputs[name] = iv
        self._inps[name] = z3.BitVec(f"{name}_inp", width)
        if signed:
            self.signed_vars.add(name)

    def set_next_state(self, name: str, expr: z3.BitVecRef):
        if name in self.state_vars:
            tw = self.state_vars[name].width
            ew = expr.size()
            if tw != ew:
                if tw > ew:
                    expr = z3.ZeroExt(tw - ew, expr)
                else:
                    expr = z3.Extract(tw - 1, 0, expr)
        self._next_state_exprs[name] = expr

    def set_var_dims(self, name: str, dims: list[int], num_packed: int = 0):
        self._var_dims[name] = dims
        self._var_num_packed[name] = num_packed

    def get_var_dims(self, name: str) -> list[int]:
        return self._var_dims.get(name, [])

    def get_var_num_packed(self, name: str) -> int:
        return self._var_num_packed.get(name, 0)

    def get_elem_width(self, name: str) -> int:
        """Compute element width for array variables."""
        dims = self._var_dims.get(name, [])
        if not dims:
            return 0
        total = self.state_vars[name].width if name in self.state_vars else 1
        dim_product = 1
        for d in dims:
            dim_product *= d
        if dim_product > 0:
            return total // dim_product
        return 1

    def add_init(self, expr: z3.BoolRef):
        self._init_constraints.append(expr)

    def add_trans(self, expr: z3.BoolRef):
        self._trans_constraints.append(expr)

    def add_property(self, name: str, expr: z3.BoolRef, source: str = ""):
        self.properties.append((name, expr))
        if source:
            self.prop_sources[name] = source

    def add_trans_property(self, name: str, expr: z3.BoolRef, source: str = ""):
        self.trans_properties.append((name, expr))
        if source:
            self.trans_prop_sources[name] = source

    def add_cover_property(self, name: str, expr: z3.BoolRef, source: str = ""):
        self.cover_properties.append((name, expr))
        if source:
            self.cover_prop_sources[name] = source

    def get_prop_source(self, name: str) -> str:
        return (self.prop_sources.get(name) or
                self.trans_prop_sources.get(name) or
                self.cover_prop_sources.get(name) or "")

    def add_assumption(self, expr: z3.BoolRef, source: str = ""):
        self.assumptions.append(expr)
        if source:
            self.assumption_sources[len(self.assumptions) - 1] = source

    def get_assumption_source(self, idx: int) -> str:
        return self.assumption_sources.get(idx, "")

    @property
    def comb_assumption_expr(self) -> z3.BoolRef:
        """Return only non-temporal assumptions (no _next or step-chain vars)."""
        import re as _re
        safe = []
        for a in self.assumptions:
            s = str(a)
            if '_next' in s:
                continue
            if _re.search(r'_c\d+_s', s):
                continue
            safe.append(a)
        return z3.And(*safe) if safe else z3.BoolVal(True)

    def add_param(self, name: str, width: int, init_val: int | None = None):
        self.params[name] = (width, init_val)

    def set_param_dims(self, name: str, dims: list[int]):
        self._param_dims[name] = dims

    def get_param_dims(self, name: str) -> list[int]:
        return self._param_dims.get(name, [])

    @property
    def assumption_expr(self) -> z3.BoolRef:
        return z3.And(*self.assumptions) if self.assumptions else z3.BoolVal(True)

    def add_comb_constraint(self, expr: z3.BoolRef):
        """Add a combinational constraint (always_comb or assign target).

        Tracks which state vars are defined by comb logic so coverage/etc.
        can skip their (contradictory) init constraints.
        """
        import re as _re
        self._comb_constraints.append(expr)
        lhs_str = str(expr)
        for name in self.state_vars:
            cur_str = str(self.get_cur(name))
            # Match pattern: var ==  at top level (not nested inside Extract/If/etc)
            if _re.match(_re.escape(cur_str) + r'\s*==', lhs_str):
                self._comb_targets.add(name)

    @property
    def comb_expr(self) -> z3.BoolRef:
        return z3.And(*self._comb_constraints) if self._comb_constraints else z3.BoolVal(True)

    @property
    def comb_expr_next(self) -> z3.BoolRef:
        if not self._comb_constraints:
            return z3.BoolVal(True)
        cur_to_next = [(self._cur[name], self._next[name]) for name in self.state_vars]
        return z3.And(*[z3.substitute(c, *cur_to_next) for c in self._comb_constraints])

    @property
    def init_expr(self) -> z3.BoolRef:
        inits = []
        for name, sv in self.state_vars.items():
            if name not in self._comb_targets:
                inits.append(self._cur[name] == z3.BitVecVal(sv.init_val, sv.width))
        inits.extend(self._init_constraints)
        return z3.And(*inits) if inits else z3.BoolVal(True)

    @property
    def trans_expr(self) -> z3.BoolRef:
        guards = []
        for name, expr in self._next_state_exprs.items():
            guards.append(self._next[name] == expr)
        guards.extend(self._trans_constraints)
        return z3.And(*guards) if guards else z3.BoolVal(True)

    def get_cur(self, name: str) -> z3.BitVecRef:
        return self._cur[name]

    def get_next(self, name: str) -> z3.BitVecRef:
        return self._next[name]

    def get_inp(self, name: str) -> z3.BitVecRef:
        return self._inps[name]

    def cur_values(self) -> list[z3.BitVecRef]:
        return list(self._cur.values())

    def next_values(self) -> list[z3.BitVecRef]:
        return list(self._next.values())

    def inp_values(self) -> list[z3.BitVecRef]:
        return list(self._inps.values())

    def all_vars(self) -> list[z3.ExprRef]:
        return self.cur_values() + self.inp_values() + self.next_values()

    def substitute_cur_with_next(self, expr: z3.BoolRef) -> z3.BoolRef:
        sub_map = {}
        for name in self.state_vars:
            sub_map[self._cur[name]] = self._next[name]
        return z3.substitute(expr, *[(v, k) for k, v in sub_map.items()])

    def substitute_next_with_cur(self, expr: z3.ExprRef) -> z3.ExprRef:
        sub_map = {}
        for name in self.state_vars:
            sub_map[self._next[name]] = self._cur[name]
        return z3.substitute(expr, *[(v, k) for k, v in sub_map.items()])

    def rename_cur_to(self, expr: z3.BoolRef, suffix: str) -> z3.BoolRef:
        sub_map = {}
        for name in self.state_vars:
            fresh = z3.BitVec(f"{name}{suffix}", self.state_vars[name].width)
            sub_map[self._cur[name]] = fresh
        return z3.substitute(expr, *[(k, v) for k, v in sub_map.items()])

    def state_vector(self, suffix: str = "") -> dict[str, z3.BitVecRef]:
        if suffix:
            return {name: z3.BitVec(f"{name}{suffix}", sv.width)
                    for name, sv in self.state_vars.items()}
        return dict(self._cur)

    def input_vector(self, suffix: str = "") -> dict[str, z3.BitVecRef]:
        if suffix:
            return {name: z3.BitVec(f"{name}{suffix}", iv.width)
                    for name, iv in self.inputs.items()}
        return dict(self._inps)

    def summarize(self) -> str:
        lines = [f"=== Transition System: {self.name} ==="]
        lines.append(f"State vars ({len(self.state_vars)}):")
        for sv in self.state_vars.values():
            lines.append(f"  {sv}")
        lines.append(f"Inputs ({len(self.inputs)}):")
        for iv in self.inputs.values():
            lines.append(f"  {iv}")
        lines.append(f"Properties ({len(self.properties)}):")
        for n, _ in self.properties:
            lines.append(f"  {n}")
        lines.append(f"Init constraints: {len(self._init_constraints)}")
        lines.append(f"Trans constraints: {len(self._trans_constraints)}")
        lines.append(f"Comb constraints: {len(self._comb_constraints)}")
        lines.append(f"Next-state assignments: {len(self._next_state_exprs)}")
        return "\n".join(lines)
