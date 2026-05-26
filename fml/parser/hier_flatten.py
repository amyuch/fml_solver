"""Hierarchy flattening for module instantiations.

Finds sub-module definitions, parses them, and inlines their logic
into the parent TransitionSystem with signal name prefixing.
"""
import os
import warnings
import z3
from pyslang.syntax import SyntaxKind
from ..ir.transition_system import TransitionSystem


# Default search paths for OpenTitan IP
OT_SEARCH_PATHS = [
    "/home/AM/hack2dac/opentitan/hw/ip/prim/rtl",
    "/home/AM/hack2dac/opentitan/hw/ip",
]


def find_module_path(mod_name: str) -> str | None:
    """Search for a SystemVerilog file containing the given module."""
    for base in OT_SEARCH_PATHS:
        if not os.path.isdir(base):
            continue
        if os.path.isfile(os.path.join(base, f"{mod_name}.sv")):
            return os.path.join(base, f"{mod_name}.sv")
        for root, dirs, files in os.walk(base):
            for f in files:
                if not f.endswith(".sv"):
                    continue
                fpath = os.path.join(root, f)
                try:
                    with open(fpath) as fh:
                        if f"module {mod_name}" in fh.read(4096):
                            return fpath
                except OSError:
                    continue
    return None


def _token_text(node) -> str:
    return str(node).strip()


class HierarchyFlattener:
    """Flattens module instantiations by inlining sub-module logic."""

    def __init__(self):
        self._module_cache: dict[str, TransitionSystem] = {}
        self._parser = None

    def _get_parser(self):
        if self._parser is None:
            from .rtl_parser import RTLParser
            self._parser = RTLParser()
        return self._parser

    def parse_and_cache_module(self, mod_name: str) -> TransitionSystem | None:
        """Find, parse, and cache a module definition."""
        if mod_name in self._module_cache:
            return self._module_cache[mod_name]
        path = find_module_path(mod_name)
        if path is None:
            warnings.warn(f"Module '{mod_name}' not found in search paths")
            return None
        from .ot_preproc import preprocess_file
        try:
            text = preprocess_file(path)
            parser = self._get_parser()
            ts = parser.parse_text_to_ts(text)
            self._module_cache[mod_name] = ts
            return ts
        except Exception as e:
            warnings.warn(f"Failed to parse '{mod_name}' at {path}: {e}")
            return None

    def flatten_instantiation(self, node, ts: TransitionSystem):
        """Process a HierarchyInstantiation node, inlining sub-module logic."""
        mod_name = _token_text(node.type)
        sub_ts = self.parse_and_cache_module(mod_name)
        if sub_ts is None:
            warnings.warn(f"Skipping instantiation of unknown module '{mod_name}'")
            return

        for instance in node.instances:
            if hasattr(instance, 'name'):
                inst_name = _token_text(instance.name)
            elif hasattr(instance, 'decl'):
                inst_name = _token_text(instance.decl)
            else:
                inst_name = _token_text(instance)
            port_map = {}
            for conn in instance.connections if hasattr(instance, 'connections') else instance:
                if hasattr(conn, 'kind') and conn.kind == SyntaxKind.NamedPortConnection:
                    sub_port = _token_text(conn.name)
                    parent_expr = conn.expr if hasattr(conn, 'expr') else None
                    if parent_expr is not None:
                        port_map[sub_port] = parent_expr
            self._merge_ts(ts, sub_ts, inst_name, port_map)

    def _merge_ts(self, parent_ts: TransitionSystem, sub_ts: TransitionSystem,
                   inst_name: str, port_map: dict):
        """Merge sub-module TS into parent TS with signal prefixing."""
        prefix = f"{inst_name}."

        # Create sub-module signal instances in parent
        sub_cur_map = {}
        sub_next_map = {}
        for sv_name, sv in sub_ts.state_vars.items():
            pname = f"{prefix}{sv_name}"
            if pname not in parent_ts.state_vars:
                parent_ts.add_state_var(pname, sv.width, sv.init_val,
                                        signed=sv_name in sub_ts.signed_vars)
            sub_cur_map[sub_ts.get_cur(sv_name)] = parent_ts.get_cur(pname)
            sub_next_map[sub_ts.get_next(sv_name)] = parent_ts.get_next(pname)

        # Sub-module inputs become parent wires (state vars)
        for inp_name, inp in sub_ts.inputs.items():
            pname = f"{prefix}{inp_name}"
            if pname not in parent_ts.state_vars:
                parent_ts.add_state_var(pname, inp.width)
            sub_cur_map[sub_ts.get_inp(inp_name)] = parent_ts.get_cur(pname)

        # Port connections: equate parent signals to sub-module ports
        for sub_port, parent_node in port_map.items():
            sub_sig_name = f"{prefix}{sub_port}"
            pv = self._resolve_name(parent_node, parent_ts)
            if pv is None:
                continue
            if sub_sig_name not in parent_ts.state_vars:
                continue
            sub_var = parent_ts.get_cur(sub_sig_name)
            if sub_var.size() != pv.size():
                if sub_var.size() > pv.size():
                    pv = z3.ZeroExt(sub_var.size() - pv.size(), pv)
                else:
                    pv = z3.Extract(sub_var.size() - 1, 0, pv)
            parent_ts.add_comb_constraint(sub_var == pv)

        # Merge combinational constraints
        for c in sub_ts._comb_constraints:
            renamed = z3.substitute(c, *[(k, v) for k, v in sub_cur_map.items()])
            parent_ts.add_comb_constraint(renamed)

        # Merge transition constraints (next-state equations)
        for sv_name, expr in sub_ts._next_state_exprs.items():
            pname = f"{prefix}{sv_name}"
            renamed_expr = z3.substitute(expr, *[(k, v) for k, v in sub_cur_map.items()])
            parent_ts.set_next_state(pname, renamed_expr)

        # Merge init constraints
        for c in sub_ts._init_constraints:
            renamed = z3.substitute(c, *[(k, v) for k, v in sub_cur_map.items()])
            parent_ts.add_init(renamed)

        # Merge trans constraints
        for c in sub_ts._trans_constraints:
            renamed = z3.substitute(c,
                *[(k, v) for k, v in sub_cur_map.items()],
                *[(k, v) for k, v in sub_next_map.items()])
            parent_ts.add_trans(renamed)

    def _resolve_name(self, node, ts) -> z3.BitVecRef | None:
        """Resolve a port connection expression to a Z3 variable."""
        # Unwrap property/sequence wrappers
        while hasattr(node, 'kind') and str(node.kind).endswith('PropertyExpr') or \
              hasattr(node, 'kind') and str(node.kind).endswith('SequenceExpr'):
            node = node.expr if hasattr(node, 'expr') else node
        k = node.kind
        if k == SyntaxKind.IdentifierName:
            name = _token_text(node.identifier)
            if name in ts.state_vars:
                return ts.get_cur(name)
            if name in ts.inputs:
                return ts.get_inp(name)
        return None
