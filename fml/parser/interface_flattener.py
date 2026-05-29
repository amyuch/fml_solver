"""Interface and modport flattening for SystemVerilog.

Expands interface ports (e.g., `tl_if.host bus`) into individual signals
in the TransitionSystem, resolves dot-access expressions like `bus.a_req`.
"""

import z3
import os
import warnings
from pyslang.syntax import SyntaxKind
from typing import Optional


class ModportDef:
    def __init__(self, name: str):
        self.name = name
        self.signals: dict[str, str] = {}  # signal_name -> direction


class InterfaceDef:
    def __init__(self, name: str):
        self.name = name
        self.modports: dict[str, ModportDef] = {}
        self.signal_widths: dict[str, int] = {}  # signal_name -> width (cached)
        self.signal_dims: dict[str, object] = {}  # signal_name -> dimension_node for re-eval
        self.params: dict[str, tuple[int, int | None]] = {}
        self.struct_vars: dict[str, object] = {}  # var_name -> StructType


class InterfacePortInstance:
    def __init__(self, iface_name: str, modport: str, instance_name: str):
        self.iface_name = iface_name
        self.modport = modport
        self.instance_name = instance_name
        self.signal_map: dict[str, str] = {}  # signal_name -> ts_var_name


class InterfaceFlattener:
    def __init__(self):
        self._interfaces: dict[str, InterfaceDef] = {}
        self._port_instances: dict[str, InterfacePortInstance] = {}

    def _get_interface_header(self, node):
        if hasattr(node, 'header') and node.header is not None:
            return node.header
        for child in node:
            if hasattr(child, 'kind') and 'InterfaceHeader' in str(child.kind):
                return child
        return None

    def _extract_interface_imports(self, header, search_paths: list[str]) -> dict:
        """Extract package imports from interface header and resolve types."""
        imports = getattr(header, 'imports', None)
        if not imports:
            return {}
        pkg_names = []
        for imp in imports:
            if not hasattr(imp, 'kind') or imp.kind != SyntaxKind.PackageImportDeclaration:
                continue
            for ci in range(256):
                try:
                    child = imp[ci]
                except (IndexError, TypeError):
                    break
                if hasattr(child, 'kind') and 'PackageImportItem' in str(child.kind):
                    for ci2 in range(256):
                        try:
                            child2 = child[ci2]
                        except (IndexError, TypeError):
                            break
                        if hasattr(child2, 'kind') and 'Identifier' in str(child2.kind) and 'Keyword' not in str(child2.kind):
                            raw = str(child2).strip()
                            if raw not in ('::', '*'):
                                pkg_names.append(raw)
        if not pkg_names:
            return {}
        from .struct_flattener import _resolve_package_types
        return _resolve_package_types(pkg_names, search_paths)

    def parse_interface(self, node, parser=None, search_paths=None) -> None:
        header = self._get_interface_header(node)
        if header is None:
            return
        iface_name = None
        if hasattr(header, 'name') and header.name is not None:
            iface_name = str(header.name).strip()

        if not iface_name:
            return
        iface = InterfaceDef(iface_name)

        # Extract interface parameters for width computation
        iface_params = self._extract_interface_params(header)
        iface.params = dict(iface_params)

        # Resolve package imports for struct type information
        known_types = self._extract_interface_imports(header, search_paths or [])

        saved_ts = None
        if parser is not None:
            from ..ir.transition_system import TransitionSystem
            temp_ts = TransitionSystem(iface_name)
            for pname, (pw, pval) in iface_params.items():
                if pval is not None:
                    temp_ts.add_param(pname, pw, pval)
            saved_ts = getattr(parser, '_current_ts', None)
            parser._current_ts = temp_ts

        try:
            for member in node.members:
                if member.kind == SyntaxKind.DataDeclaration:
                    self._extract_data_decl_widths(member, iface, parser)
                    self._extract_struct_data_decl(member, iface, known_types)
                elif member.kind == SyntaxKind.ModportDeclaration:
                    self._parse_modport(member, iface)
        finally:
            if parser is not None and saved_ts is not None:
                parser._current_ts = saved_ts

        self._interfaces[iface_name] = iface

    def _extract_interface_params(self, header) -> dict[str, tuple[int, int | None]]:
        params = {}
        if not hasattr(header, 'parameters') or header.parameters is None:
            return params
        for p in header.parameters:
            if not hasattr(p, 'kind') or p.kind != SyntaxKind.ParameterDeclaration:
                continue
            if not hasattr(p, 'declarators') or not p.declarators:
                continue
            for dcl in p.declarators:
                if not hasattr(dcl, 'name'):
                    continue
                name = str(dcl.name).strip()
                init_val = None
                if hasattr(dcl, 'initializer') and dcl.initializer is not None:
                    if hasattr(dcl.initializer, 'expr') and dcl.initializer.expr is not None:
                        try:
                            init_val = int(str(dcl.initializer.expr), 0)
                        except (ValueError, TypeError):
                            pass
                w = 32
                if hasattr(p, 'type') and p.type is not None:
                    try:
                        w = self._extract_type_width(p.type)
                    except Exception:
                        pass
                params[name] = (w, init_val)
        return params

    def _extract_type_width(self, type_node) -> int:
        w = 1
        if hasattr(type_node, 'dimensions') and type_node.dimensions:
            for dim in type_node.dimensions:
                if hasattr(dim, 'specifier') and dim.specifier:
                    spec = dim.specifier
                    if hasattr(spec, 'selector') and spec.selector:
                        s = spec.selector
                        if hasattr(s, 'left') and hasattr(s, 'right'):
                            lo = self._eval_literal(s.left)
                            hi = self._eval_literal(s.right)
                            if lo is not None and hi is not None:
                                w *= abs(lo - hi) + 1
        return w

    def _eval_literal(self, node) -> int | None:
        try:
            return int(str(node), 0)
        except (ValueError, TypeError):
            pass
        if hasattr(node, 'kind') and 'IdentifierName' in str(node.kind):
            if hasattr(node, 'identifier'):
                return str(node.identifier).strip()
        return None

    def _extract_struct_data_decl(self, node, iface: InterfaceDef, known_types: dict) -> None:
        if not hasattr(node, 'type') or node.type is None:
            return
        if node.type.kind != SyntaxKind.NamedType:
            return
        type_name = None
        for child in node.type:
            if hasattr(child, 'kind') and child.kind == SyntaxKind.IdentifierName:
                type_name = str(child).strip()
                break
        if not type_name or type_name not in known_types:
            return
        st = known_types[type_name]
        from .package_resolver import StructType
        if not isinstance(st, StructType):
            return
        if not hasattr(node, 'declarators') or not node.declarators:
            return
        for dcl in node.declarators:
            if not hasattr(dcl, 'name'):
                continue
            var_name = str(dcl.name).strip()
            iface.struct_vars[var_name] = st
            for flat_name, width, offset in st.flat_fields:
                iface.signal_widths[flat_name] = width

    def _extract_data_decl_widths(self, node, iface: InterfaceDef, parser=None) -> None:
        if not hasattr(node, 'type') or node.type is None:
            return
        w = self._extract_type_width(node.type)
        if w <= 0:
            w = 1
        # Store the first dimension node for re-evaluation with parameter overrides
        dim_node = None
        if hasattr(node.type, 'dimensions') and node.type.dimensions:
            for dim in node.type.dimensions:
                if hasattr(dim, 'specifier') and dim.specifier:
                    spec = dim.specifier
                    if hasattr(spec, 'selector') and spec.selector:
                        s = spec.selector
                        if hasattr(s, 'left') and hasattr(s, 'right'):
                            dim_node = s
                            break
        if not hasattr(node, 'declarators') or not node.declarators:
            return
        for dcl in node.declarators:
            if not hasattr(dcl, 'name'):
                continue
            sig_name = str(dcl.name).strip()
            iface.signal_widths[sig_name] = w
            if dim_node is not None:
                iface.signal_dims[sig_name] = dim_node
            if parser is not None and w == 1 and dim_node is not None:
                if hasattr(dim_node, 'left') and hasattr(dim_node, 'right'):
                    left_expr = parser._eval_literal_expr(dim_node.left, parser._current_ts) if hasattr(parser, '_eval_literal_expr') else None
                    right_expr = parser._eval_literal_expr(dim_node.right, parser._current_ts) if hasattr(parser, '_eval_literal_expr') else None
                    if left_expr is not None and right_expr is not None:
                        if isinstance(left_expr, int) and isinstance(right_expr, int):
                            iface.signal_widths[sig_name] = abs(left_expr - right_expr) + 1

    def _parse_modport(self, node, iface: InterfaceDef) -> None:
        for item in node.items if hasattr(node, 'items') and node.items else []:
            if not hasattr(item, 'name') or item.name is None:
                continue
            mp_name = str(item.name).strip()
            mp = ModportDef(mp_name)

            ports = item.ports if hasattr(item, 'ports') else None
            if ports is None:
                continue

            current_dir = None
            for pi in range(256):
                try:
                    p = ports[pi]
                except (IndexError, TypeError):
                    break
                sk = str(p.kind)
                if 'ModportSimplePortList' in sk:
                    if hasattr(p, 'direction') and p.direction is not None:
                        dk = str(p.direction.kind)
                        if 'Input' in dk:
                            current_dir = 'input'
                        elif 'Output' in dk:
                            current_dir = 'output'
                        elif 'InOut' in dk:
                            current_dir = 'inout'
                    for ci in range(256):
                        try:
                            child = p[ci]
                        except (IndexError, TypeError):
                            break
                        if hasattr(child, 'kind') and 'ModportNamedPort' in str(child.kind):
                            sig_name = None
                            if hasattr(child, 'name') and child.name is not None:
                                sig_name = str(child.name).strip()
                            if sig_name and current_dir:
                                # Expand struct variable references into individual fields
                                if sig_name in iface.struct_vars:
                                    st = iface.struct_vars[sig_name]
                                    for flat_name, width, offset in st.flat_fields:
                                        mp.signals[flat_name] = current_dir
                                else:
                                    mp.signals[sig_name] = current_dir
            if mp.signals:
                iface.modports[mp_name] = mp

    def _extract_port_array_dims(self, port, parser) -> list[int]:
        dims = []
        if not hasattr(port, 'declarator') or port.declarator is None:
            return dims
        dcl = port.declarator
        if not hasattr(dcl, 'dimensions') or not dcl.dimensions:
            return dims
        for dim in dcl.dimensions:
            if hasattr(dim, 'specifier') and dim.specifier:
                spec = dim.specifier
                if hasattr(spec, 'selector') and spec.selector:
                    s = spec.selector
                    if hasattr(s, 'expr') and s.expr is not None:
                        try:
                            val = int(str(s.expr), 0)
                            if val > 0:
                                dims.append(val)
                        except (ValueError, TypeError):
                            pass
        return dims

    def expand_port(self, port, ts, parser) -> Optional[str]:
        header = port.header
        if not hasattr(header, 'kind'):
            return None
        if str(header.kind) != 'SyntaxKind.InterfacePortHeader':
            if not hasattr(header, 'modport'):
                return None

        iface_name = None
        if hasattr(header, 'nameOrKeyword') and header.nameOrKeyword is not None:
            iface_name = str(header.nameOrKeyword).strip()

        modport_name = None
        if hasattr(header, 'modport') and header.modport is not None:
            raw = str(header.modport).strip()
            modport_name = raw.lstrip('.')

        inst_name = None
        if hasattr(port, 'declarator') and port.declarator is not None:
            if hasattr(port.declarator, 'name') and port.declarator.name is not None:
                inst_name = parser._token_text(port.declarator.name)

        if not iface_name or not inst_name:
            return None
        if iface_name not in self._interfaces:
            return None

        iface = self._interfaces[iface_name]

        # No modport specified: use all signals (first modport or combined)
        if not modport_name:
            modport_signals = {}
            for mp_name, mp in iface.modports.items():
                for sig_name, direction in mp.signals.items():
                    modport_signals[sig_name] = direction
        else:
            if modport_name not in iface.modports:
                return None
            modport_signals = iface.modports[modport_name].signals

        arr_dims = self._extract_port_array_dims(port, parser)
        arr_size = arr_dims[0] if arr_dims else 1

        inst = InterfacePortInstance(iface_name, modport_name or '', inst_name)
        for sig_name, direction in modport_signals.items():
            w = iface.signal_widths.get(sig_name, 1)
            if w <= 0:
                w = 1
            if arr_size > 1:
                full_w = w * arr_size
                ts_var = f"{inst_name}_{sig_name}"
                var_dims = [arr_size, w] if w > 1 else [arr_size]
                if direction == 'input':
                    ts.add_input(ts_var, full_w)
                else:
                    ts.add_state_var(ts_var, full_w)
                if var_dims:
                    ts.set_var_dims(ts_var, var_dims, num_packed=1)
            else:
                ts_var = f"{inst_name}_{sig_name}"
                if direction == 'input':
                    ts.add_input(ts_var, w)
                else:
                    ts.add_state_var(ts_var, w)
            inst.signal_map[sig_name] = ts_var

        self._port_instances[inst_name] = inst
        return inst_name

    def _eval_width_with_params(self, dim_node, param_overrides, parser) -> int:
        """Re-evaluate width using parameter overrides."""
        if not hasattr(dim_node, 'left') or not hasattr(dim_node, 'right'):
            return 1
        if parser is None or not hasattr(parser, '_eval_literal_expr'):
            return 1
        if not hasattr(parser, '_current_ts') or parser._current_ts is None:
            return 1
        try:
            left_val = parser._eval_literal_expr(dim_node.left, parser._current_ts)
            right_val = parser._eval_literal_expr(dim_node.right, parser._current_ts)
            if left_val is not None and right_val is not None:
                if isinstance(left_val, int) and isinstance(right_val, int):
                    return abs(left_val - right_val) + 1
        except Exception:
            pass
        return 1

    def expand_port_with_params(self, iface_name, modport_name, inst_name,
                                 param_overrides, ts, parser,
                                 arr_dims: Optional[list[int]] = None) -> Optional[str]:
        if iface_name not in self._interfaces:
            return None
        iface = self._interfaces[iface_name]

        # No modport specified: use all signals
        if not modport_name:
            modport_signals = {}
            for mp_name, mp in iface.modports.items():
                for sig_name, direction in mp.signals.items():
                    modport_signals[sig_name] = direction
        else:
            if modport_name not in iface.modports:
                return None
            modport_signals = iface.modports[modport_name].signals

        arr_dims = arr_dims or []
        arr_size = arr_dims[0] if arr_dims else 1

        # Build temp TS with overridden parameter values for width re-evaluation
        saved_ts = None
        temp_ts = None
        if parser is not None and param_overrides:
            from ..ir.transition_system import TransitionSystem
            temp_ts = TransitionSystem("_iface_temp")
            for pname, (pw, pval) in iface.params.items():
                ov = param_overrides.get(pname)
                if ov is not None:
                    temp_ts.add_param(pname, pw, ov)
            saved_ts = getattr(parser, '_current_ts', None)
            parser._current_ts = temp_ts

        sig_widths = {}
        try:
            for sig_name in modport_signals:
                sw = iface.signal_widths.get(sig_name, 1)
                if param_overrides and sig_name in iface.signal_dims:
                    re = self._eval_width_with_params(iface.signal_dims[sig_name],
                                                       param_overrides, parser)
                    if re > 0:
                        sw = re
                sig_widths[sig_name] = sw
        finally:
            if parser is not None and saved_ts is not None:
                parser._current_ts = saved_ts

        inst = InterfacePortInstance(iface_name, modport_name or '', inst_name)
        for sig_name, direction in modport_signals.items():
            w = sig_widths.get(sig_name, 1)
            if w <= 0:
                w = 1
            if arr_size > 1:
                full_w = w * arr_size
                ts_var = f"{inst_name}_{sig_name}"
                var_dims = [arr_size, w] if w > 1 else [arr_size]
                if direction == 'input':
                    ts.add_input(ts_var, full_w)
                else:
                    ts.add_state_var(ts_var, full_w)
                if var_dims:
                    ts.set_var_dims(ts_var, var_dims, num_packed=1)
            else:
                ts_var = f"{inst_name}_{sig_name}"
                if direction == 'input':
                    ts.add_input(ts_var, w)
                else:
                    ts.add_state_var(ts_var, w)
            inst.signal_map[sig_name] = ts_var

        self._port_instances[inst_name] = inst
        return inst_name

    def resolve(self, instance_name: str, signal_name: str) -> Optional[str]:
        inst = self._port_instances.get(instance_name)
        if inst is None:
            return None
        return inst.signal_map.get(signal_name)

    def get_direction(self, instance_name: str, signal_name: str) -> Optional[str]:
        inst = self._port_instances.get(instance_name)
        if inst is None:
            return None
        iface = self._interfaces.get(inst.iface_name)
        if iface is None:
            return None
        mp = iface.modports.get(inst.modport)
        if mp is None:
            return None
        return mp.signals.get(signal_name)
