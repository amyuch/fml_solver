import z3
import os
import warnings
from pyslang.driver import Driver
from pyslang.syntax import SyntaxKind
from pyslang.parsing import TokenKind
from ..ir.transition_system import TransitionSystem

from .utils import _token_text, _eval_literal, _extract_name
from .eval_expr import (
    _is_signed_expr, _is_signed_type,
    _extract_width_from_node, _dimension_width,
    _signal_width, _eval_literal_expr, _expr_width,
)
from .node_to_z3 import (
    _node_to_z3, _z3_promote_pair, _z3_promote,
    _extract_call_args, _unwrap_property_wrapper, _process_system_func,
)
from .hier_flatten import HierarchyFlattener

def _z3_slt(a, b):
    ctx = a.ctx
    return z3.BoolRef(z3.Z3_mk_bvslt(ctx.ref(), a.as_ast(), b.as_ast()), ctx)

def _z3_sle(a, b):
    ctx = a.ctx
    return z3.BoolRef(z3.Z3_mk_bvsle(ctx.ref(), a.as_ast(), b.as_ast()), ctx)

def _z3_sgt(a, b):
    ctx = a.ctx
    return z3.BoolRef(z3.Z3_mk_bvsgt(ctx.ref(), a.as_ast(), b.as_ast()), ctx)

def _z3_sge(a, b):
    ctx = a.ctx
    return z3.BoolRef(z3.Z3_mk_bvsge(ctx.ref(), a.as_ast(), b.as_ast()), ctx)

class RTLParser:
    # Imported methods
    _token_text = staticmethod(_token_text)
    _eval_literal = staticmethod(_eval_literal)
    _extract_name = staticmethod(_extract_name)
    _is_signed_expr = _is_signed_expr
    _is_signed_type = _is_signed_type
    _extract_width_from_node = _extract_width_from_node
    _dimension_width = _dimension_width
    _signal_width = _signal_width
    _eval_literal_expr = _eval_literal_expr
    _expr_width = _expr_width
    _node_to_z3 = _node_to_z3
    _z3_promote_pair = _z3_promote_pair
    _z3_promote = _z3_promote
    _extract_call_args = _extract_call_args
    _unwrap_property_wrapper = _unwrap_property_wrapper
    _process_system_func = _process_system_func
    def __init__(self):
        self.driver = Driver()
        self.driver.addStandardArgs()
        self._past_counter = 0
        self._chain_counter = 0
        self._hier_flattener = HierarchyFlattener()
        self._delay_context: dict = {}  # "step_vars", "step_names", "max_step" from ##N
        self._disable_cond: z3.BoolRef | None = None

    def parse_file(self, filepath: str) -> list[TransitionSystem]:
        self._module_path = filepath
        self.driver.parseCommandLine(f"parse {filepath}")
        self.driver.processOptions()
        ok = self.driver.parseAllSources()
        if not ok:
            raise RuntimeError(f"Failed to parse {filepath}")

        systems = []
        for tree in self.driver.syntaxTrees:
            systems.extend(self._extract_modules(tree.root))
        return systems

    def parse_text(self, text: str, filename: str = "top.sv") -> list[TransitionSystem]:
        import tempfile, os
        with tempfile.NamedTemporaryFile(mode="w", suffix=".sv", delete=False, dir="/tmp") as f:
            f.write(text)
            f.flush()
            tmp_path = f.name
        try:
            return self.parse_file(tmp_path)
        finally:
            os.unlink(tmp_path)

    def _extract_modules(self, root) -> list[TransitionSystem]:
        systems = []
        for member in root.members:
            if member.kind == SyntaxKind.ModuleDeclaration:
                ts = self._process_module(member)
                if ts:
                    systems.append(ts)
        return systems

    def _process_module(self, mod_node) -> TransitionSystem | None:
        header = mod_node.header
        mod_name = self._token_text(header.name)
        ts = TransitionSystem(mod_name)
        self._current_ts = ts
        self._extract_header_params(header, ts)
        self._extract_body_params(mod_node, ts)
        self._extract_ports(header, ts)
        self._resolve_header_imports(header, ts)
        self._extract_body(mod_node, ts)
        return ts

    def _extract_header_params(self, header, ts: TransitionSystem):
        if hasattr(header, 'parameters') and header.parameters is not None:
            for p in header.parameters:
                if hasattr(p, 'kind') and p.kind == SyntaxKind.ParameterDeclaration:
                    self._process_param_decl(p, ts)

    def _extract_body_params(self, mod_node, ts):
        for member in mod_node.members:
            k = member.kind
            if k == SyntaxKind.ParameterDeclarationStatement:
                self._process_parameter_declaration(member, ts)
            elif k == SyntaxKind.GenerateRegion:
                self._extract_generate_params(member, ts)

    def _extract_generate_params(self, node, ts):
        for member in node.members:
            k = member.kind
            if k == SyntaxKind.ParameterDeclarationStatement:
                self._process_parameter_declaration(member, ts)

    def _process_param_decl(self, node, ts: TransitionSystem, width_override: int = None):
        w = width_override
        if w is None and hasattr(node, 'type') and node.type is not None:
            w = self._extract_width_from_node(node.type, ts)
            packed_dims = self._extract_packed_dims(node.type, ts)
            if packed_dims:
                total = 1
                for d in packed_dims:
                    total *= d
                w = total
        if w is None or w <= 0:
            w = 1
        genvar_ctx = getattr(self, '_genvar_subst', None) or {}
        ctx_suffix = self._genvar_suffix(genvar_ctx) if genvar_ctx else ''
        for decl in node.declarators:
            base_name = self._token_text(decl.name)
            name = base_name + ctx_suffix
            init_val = None
            if hasattr(decl, 'initializer') and decl.initializer is not None:
                init_val = self._eval_literal_expr(decl.initializer.expr, ts)
            param_w = w
            if init_val is not None:
                required = max(init_val.bit_length(), 1)
                if param_w < required:
                    param_w = required
            if name not in ts.params:
                ts.add_param(name, param_w, init_val)
                if packed_dims:
                    ts.set_param_dims(name, packed_dims)

    def _genvar_suffix(self, genvar_ctx: dict) -> str:
        if not genvar_ctx:
            return ''
        parts = []
        for k in sorted(genvar_ctx.keys()):
            parts.append(f'{genvar_ctx[k]}')
        return '__' + '_'.join(parts)

    def _genvar_suffix_prefixes(self, genvar_ctx: dict):
        sorted_ctx = sorted(genvar_ctx.items(), key=lambda x: x[0])
        for i in range(len(sorted_ctx), -1, -1):
            if i == 0:
                yield ''
            else:
                yield '__' + '_'.join(str(v) for _, v in sorted_ctx[:i])

    def _resolve_header_imports(self, header, ts: TransitionSystem):
        """Resolve package imports from the module header and inject params."""
        for child in header:
            if hasattr(child, 'kind') and child.kind == SyntaxKind.PackageImportDeclaration:
                self._resolve_package_import(child, ts)

    def _extract_ports(self, header, ts: TransitionSystem):
        last_direction = None
        for port in header.ports:
            if port.kind != SyntaxKind.ImplicitAnsiPort:
                continue
            name, direction, width = self._parse_port_direct(port)
            if name is None:
                continue
            if direction:
                last_direction = direction
            else:
                direction = last_direction or "input"
            if width is None or width <= 0:
                width = 1
            signed = False
            if hasattr(port.header, 'dataType') and port.header.dataType is not None:
                signed = self._is_signed_type(port.header.dataType)
            if direction == "input":
                ts.add_input(name, width, signed=signed)
            elif direction == "output":
                ts.add_state_var(name, width, signed=signed)
            elif direction == "inout":
                ts.add_state_var(name, width, signed=signed)

    def _parse_port_direct(self, port) -> tuple:
        ph = port.header
        direction = None
        width = None
        name = self._token_text(port.declarator.name)

        if hasattr(ph, 'direction') and ph.direction is not None:
            dk = ph.direction.kind
            if dk == TokenKind.InputKeyword:
                direction = "input"
            elif dk == TokenKind.OutputKeyword:
                direction = "output"
            elif dk == TokenKind.InOutKeyword:
                direction = "inout"

        if hasattr(ph, 'dataType') and ph.dataType is not None:
            w = self._extract_width_from_node(ph.dataType)
            if w is not None and w > 0:
                width = w

        if not direction and hasattr(ph, 'placeholder'):
            direction = "wire"

        return (name, direction, width)

    def _extract_body(self, mod_node, ts: TransitionSystem):
        self._current_ts = ts
        for member in mod_node.members:
            k = member.kind

            if k == SyntaxKind.AlwaysFFBlock:
                self._process_always_ff(member, ts)
            elif k == SyntaxKind.AlwaysCombBlock:
                self._process_always_comb(member, ts)
            elif k == SyntaxKind.AlwaysLatchBlock:
                self._process_always_comb(member, ts)
            elif k == SyntaxKind.AlwaysBlock:
                self._process_always_comb(member, ts)
            elif k == SyntaxKind.ContinuousAssign:
                self._process_cont_assign(member, ts)
            elif k == SyntaxKind.ConcurrentAssertionMember:
                self._process_assertion(member, ts)
            elif k == SyntaxKind.DataDeclaration:
                self._process_data_declaration(member, ts)
            elif k == SyntaxKind.GenerateRegion:
                self._process_generate_region(member, ts)
            elif k == SyntaxKind.LoopGenerate:
                self._process_loop_generate(member, ts)
            elif k == SyntaxKind.IfGenerate:
                self._process_if_generate(member, ts)
            elif k == SyntaxKind.CaseGenerate:
                self._process_case_generate(member, ts)
            elif k == SyntaxKind.GenvarDeclaration:
                pass
            elif k == SyntaxKind.ParameterDeclarationStatement:
                self._process_parameter_declaration(member, ts)
            elif k == SyntaxKind.HierarchyInstantiation:
                self._hier_flattener.flatten_instantiation(member, ts)

            elif k == SyntaxKind.TypedefDeclaration:
                self._process_typedef(member, ts)
            elif k == SyntaxKind.NetDeclaration:
                self._process_data_declaration(member, ts)
            elif k == SyntaxKind.PackageImportDeclaration:
                self._resolve_package_import(member, ts)
            elif k == SyntaxKind.DPIImport:
                pass
            elif k == SyntaxKind.DefaultNetTypeDirective:
                pass
            else:
                k_str = str(k)
                if 'Unused' not in k_str and 'Empty' not in k_str:
                    warnings.warn(f"Unhandled module member: {k}", stacklevel=2)

    def _process_parameter_declaration(self, node, ts: TransitionSystem):
        if hasattr(node, 'parameter') and node.parameter is not None:
            self._process_param_decl(node.parameter, ts)

    def _process_generate_region(self, node, ts: TransitionSystem):
        for member in node.members:
            k = member.kind
            if k == SyntaxKind.IfGenerate:
                self._process_if_generate(member, ts)
            elif k == SyntaxKind.LoopGenerate:
                self._process_loop_generate(member, ts)
            elif k == SyntaxKind.CaseGenerate:
                self._process_case_generate(member, ts)
            elif k == SyntaxKind.GenerateBlock:
                self._process_generate_body(member, ts)
            else:
                warnings.warn(f"Unhandled generate region member: {k}", stacklevel=2)

    def _process_if_generate(self, node, ts: TransitionSystem):
        cond_val = self._eval_literal_expr(node.condition, ts)
        taken = cond_val is not None and cond_val != 0
        if cond_val is not None and not taken:
            if node.elseClause is not None and node.elseClause.clause is not None:
                self._process_generate_item_body(node.elseClause.clause, ts)
        else:
            self._process_generate_item_body(node.block, ts)
            if cond_val is None:
                if node.elseClause is not None and node.elseClause.clause is not None:
                    self._process_generate_item_body(node.elseClause.clause, ts)

    def _process_loop_generate(self, node, ts: TransitionSystem):
        genvar_name = self._token_text(node.identifier)
        init_expr = node.initialExpr
        stop_expr = node.stopExpr
        it_expr = node.iterationExpr

        init_val = self._eval_literal_expr(init_expr, ts)
        if init_val is None:
            return

        bound_val = self._eval_stop_bound(stop_expr, ts)
        if bound_val is None:
            return

        step = 1
        if it_expr.kind == SyntaxKind.PostincrementExpression:
            step = 1
        elif it_expr.kind == SyntaxKind.PostdecrementExpression:
            step = -1
        elif it_expr.kind == SyntaxKind.AssignmentExpression:
            step_val = self._eval_literal_expr(it_expr.right, ts)
            if step_val is not None:
                step = step_val

        for i in range(init_val, bound_val, step):
            outer_subst = getattr(self, '_genvar_subst', None) or {}
            merged = {**outer_subst, genvar_name: i}
            self._process_generate_body(node.block, ts, genvar_subst=merged)

    def _eval_stop_bound(self, node, ts) -> int | None:
        k = node.kind
        if k == SyntaxKind.LessThanExpression or k == SyntaxKind.LessThanEqualExpression:
            right = self._eval_literal_expr(node.right, ts)
            if right is not None:
                if k == SyntaxKind.LessThanEqualExpression:
                    return right + 1
                return right
        if k == SyntaxKind.GreaterThanExpression or k == SyntaxKind.GreaterThanEqualExpression:
            right = self._eval_literal_expr(node.right, ts)
            if right is not None:
                if k == SyntaxKind.GreaterThanEqualExpression:
                    return right - 1
                return right
        return None

    def _process_case_generate(self, node, ts: TransitionSystem):
        cond_val = self._eval_literal_expr(node.condition, ts)
        if cond_val is None:
            return

        matched = False
        for item in node.items:
            if item.kind == SyntaxKind.StandardCaseItem:
                for expr in item.expressions:
                    ev = self._eval_literal_expr(expr, ts)
                    if ev is not None and ev == cond_val:
                        self._process_generate_item_body(item.clause, ts)
                        matched = True
                        break
            elif item.kind == SyntaxKind.DefaultCaseItem:
                if not matched:
                    self._process_generate_item_body(item.clause, ts)

    def _process_generate_body(self, node, ts: TransitionSystem, genvar_subst=None):
        if node.kind == SyntaxKind.GenerateBlock:
            for m in node.members:
                self._dispatch_generate_member(m, ts, genvar_subst)
        else:
            self._dispatch_generate_member(node, ts, genvar_subst)

    def _process_generate_item_body(self, node, ts: TransitionSystem, genvar_subst=None):
        if node.kind == SyntaxKind.GenerateBlock:
            for m in node.members:
                self._dispatch_generate_member(m, ts, genvar_subst)
        else:
            self._dispatch_generate_member(node, ts, genvar_subst)

    def _dispatch_generate_member(self, node, ts: TransitionSystem, genvar_subst=None):
        saved = getattr(self, '_genvar_subst', None)
        if genvar_subst:
            existing = saved or {}
            self._genvar_subst = {**existing, **genvar_subst}
        k = node.kind
        if k == SyntaxKind.AlwaysFFBlock:
            self._process_always_ff(node, ts)
        elif k == SyntaxKind.AlwaysCombBlock:
            self._process_always_comb(node, ts)
        elif k == SyntaxKind.AlwaysLatchBlock:
            self._process_always_comb(node, ts)
        elif k == SyntaxKind.AlwaysBlock:
            self._process_always_comb(node, ts)
        elif k == SyntaxKind.ContinuousAssign:
            self._process_cont_assign(node, ts)
        elif k == SyntaxKind.ConcurrentAssertionMember:
            self._process_assertion(node, ts)
        elif k == SyntaxKind.DataDeclaration:
            self._process_data_declaration(node, ts)
        elif k == SyntaxKind.GenerateRegion:
            self._process_generate_region(node, ts)
        elif k == SyntaxKind.IfGenerate:
            self._process_if_generate(node, ts)
        elif k == SyntaxKind.LoopGenerate:
            self._process_loop_generate(node, ts)
        elif k == SyntaxKind.CaseGenerate:
            self._process_case_generate(node, ts)
        elif k == SyntaxKind.GenvarDeclaration:
            pass
        elif k == SyntaxKind.ParameterDeclarationStatement:
            self._process_parameter_declaration(node, ts)
        elif k == SyntaxKind.HierarchyInstantiation:
            self._hier_flattener.flatten_instantiation(node, ts)
        elif k == SyntaxKind.ModuleInstantiation:
            pass
        else:
            warnings.warn(f"Unhandled generate member: {k}", stacklevel=2)
        self._genvar_subst = saved

    def _process_data_declaration(self, node, ts: TransitionSystem):
        signed = self._is_signed_type(node.type)
        array_dims = self._extract_array_dims(node.type, ts)
        packed_dims = self._extract_packed_dims(node.type, ts)
        all_dims = packed_dims + array_dims
        w = 1
        for d in all_dims:
            w *= d
        if w <= 0 or not all_dims:
            w_base = self._extract_width_from_node(node.type, ts)
            if w_base is not None and w_base > 0:
                w = w_base
            if w <= 0:
                w = 1
        for decl in node.declarators:
            if not hasattr(decl, 'name'):
                continue
            try:
                name = self._token_text(decl.name)
            except Exception:
                continue
            decl_dims = self._extract_declarator_dims(decl, ts)
            full_dims = all_dims + decl_dims
            dw = 1
            for d in full_dims:
                dw *= d
            if dw > w:
                w = dw
            is_new = name not in ts.state_vars and name not in ts.inputs
            if is_new:
                ts.add_state_var(name, w, signed=signed)
            if full_dims and is_new:
                ts.set_var_dims(name, full_dims)

    def _extract_declarator_dims(self, decl, ts) -> list[int]:
        dims = []
        if hasattr(decl, 'dimensions') and decl.dimensions:
            for dim in decl.dimensions:
                if hasattr(dim, 'specifier') and dim.specifier:
                    spec = dim.specifier
                    if hasattr(spec, 'selector') and spec.selector:
                        sel = spec.selector
                        if sel.kind == SyntaxKind.BitSelect:
                            dv = self._eval_literal_expr(sel.expr, ts)
                            if dv is not None and dv > 0:
                                dims.append(dv)
                        elif sel.kind == SyntaxKind.SimpleRangeSelect:
                            lv = self._eval_literal_expr(sel.left, ts)
                            rv = self._eval_literal_expr(sel.right, ts)
                            if lv is not None and rv is not None:
                                dims.append(abs(lv - rv) + 1)
        return dims

    def _extract_array_dims(self, type_node, ts) -> list[int]:
        dims = []
        for child in type_node:
            if hasattr(child, 'kind'):
                if child.kind == SyntaxKind.IdentifierSelectName:
                    for sel in child.selectors if hasattr(child, 'selectors') else []:
                        if sel.kind == SyntaxKind.ElementSelect:
                            s = sel.selector
                            if s.kind == SyntaxKind.SimpleRangeSelect:
                                lv = self._eval_literal_expr(s.left, ts)
                                rv = self._eval_literal_expr(s.right, ts)
                                if lv is not None and rv is not None:
                                    dims.append(abs(lv - rv) + 1)
        # Only extract from NamedType's IdentifierSelectName, not from base types
        return dims

    def _extract_packed_dims(self, type_node, ts) -> list[int]:
        if type_node.kind == SyntaxKind.NamedType:
            return []
        dims = []
        if hasattr(type_node, 'dimensions') and type_node.dimensions:
            for dim in type_node.dimensions:
                dw = self._dimension_width(dim, ts)
                if dw is not None and dw > 0:
                    dims.append(dw)
        return dims

    def _process_typedef(self, node, ts: TransitionSystem):
        """Track typedef widths for struct types."""
        type_name = None
        struct_node = None
        for child in node:
            if hasattr(child, 'kind'):
                k_str = str(child.kind)
                if 'Identifier' in k_str and 'Token' in k_str:
                    type_name = str(child).strip()
                if child.kind == SyntaxKind.StructType:
                    struct_node = child
        if type_name and struct_node:
            w = self._compute_struct_width(struct_node, ts)
            if w > 0:
                ts.params[type_name] = ('type_width', w)

    def _compute_struct_width(self, node, ts) -> int:
        total = 0
        for child in node:
            if child.kind == SyntaxKind.StructUnionMember:
                fw = 0
                for c2 in child:
                    if c2.kind == SyntaxKind.LogicType:
                        fw = self._extract_width_from_node(c2, ts) or 1
                    elif c2.kind == SyntaxKind.NamedType:
                        fw = self._signal_width(str(c2).strip(), ts) or 1
                    elif c2.kind == SyntaxKind.StructType:
                        fw = self._compute_struct_width(c2, ts) or 1
                total += fw
        return total
        """Extract array dimension sizes from a type node."""
        dims = []
        for child in type_node:
            if hasattr(child, 'kind'):
                if child.kind == SyntaxKind.IdentifierSelectName:
                    for sel in child.selectors if hasattr(child, 'selectors') else []:
                        if sel.kind == SyntaxKind.ElementSelect:
                            s = sel.selector
                            if s.kind == SyntaxKind.SimpleRangeSelect:
                                lv = self._eval_literal_expr(s.left, ts)
                                rv = self._eval_literal_expr(s.right, ts)
                                if lv is not None and rv is not None:
                                    dims.append(abs(lv - rv) + 1)
        # Also check for VariableDimension children on the type
        if hasattr(type_node, 'dimensions'):
            for dim in type_node.dimensions:
                if dim.kind == SyntaxKind.VariableDimension:
                    for child in dim:
                        if hasattr(child, 'kind') and child.kind == SyntaxKind.RangeDimensionSpecifier:
                            for c2 in child:
                                if c2.kind == SyntaxKind.SimpleRangeSelect:
                                    lv = self._eval_literal_expr(c2.left, ts)
                                    rv = self._eval_literal_expr(c2.right, ts)
                                    if lv is not None and rv is not None:
                                        dims.append(abs(lv - rv) + 1)
        return dims

    def _process_always_ff(self, block, ts: TransitionSystem):
        self._current_ts = ts
        stmt = block.statement
        if stmt.kind != SyntaxKind.TimingControlStatement:
            return

        timing = stmt.timingControl
        clk = self._extract_clock(timing)
        if clk is None:
            return

        body = stmt.statement
        if body.kind == SyntaxKind.SequentialBlockStatement:
            for item in body.items:
                self._process_statement(item, ts)
        else:
            self._process_statement(body, ts)

    def _resolve_package_import(self, node, ts: TransitionSystem):
        """Resolve a package import and inject parameters into ts."""
        try:
            import_name = None
            for child in node:
                if hasattr(child, 'kind'):
                    k_str = str(child.kind)
                    if 'PackageImportItem' in k_str:
                        for c2 in child:
                            if hasattr(c2, 'kind'):
                                ck = str(c2.kind)
                                if 'Identifier' in ck and 'Token' in ck:
                                    import_name = str(c2).strip()
                                    break
                    if 'Identifier' in k_str and 'Token' in k_str and 'Keyword' not in k_str:
                        import_name = str(child).strip()

            if not import_name:
                return

            search_paths = []
            if self._module_path:
                search_paths.append(os.path.dirname(self._module_path))
                # Try OpenTitan standard paths
                if '/opentitan/' in self._module_path:
                    idx = self._module_path.index('/opentitan/')
                    ot = self._module_path[:idx + len('/opentitan/')]
                    search_paths.append(os.path.join(ot, 'hw', 'ip', 'prim', 'rtl'))
                    # Try to find the package file in typical locations
                    for ip_dir in os.listdir(os.path.join(ot, 'hw', 'ip')):
                        pkg_path = os.path.join(ot, 'hw', 'ip', ip_dir, 'rtl', f'{import_name}.sv')
                        if os.path.isfile(pkg_path):
                            search_paths.append(os.path.dirname(pkg_path))
                            break

            from ..parser.package_resolver import resolve_package_file, extract_types_from_package
            pkg_path = resolve_package_file(import_name, search_paths)
            if pkg_path:
                pkg_types = extract_types_from_package(pkg_path)
                for name, val in pkg_types.items():
                    if isinstance(val, int):
                        ts.params[name] = ('parameter', val)
        except Exception as e:
            print(f"  [package import] {import_name}: {e}", file=__import__('sys').stderr)

    def _extract_clock(self, timing) -> str | None:
        if hasattr(timing, 'at') and timing.at is not None:
            evt = timing.expr
            if evt.kind == SyntaxKind.ParenthesizedEventExpression:
                evt = evt.expr
            if evt.kind == SyntaxKind.SignalEventExpression:
                if evt.expr.kind == SyntaxKind.IdentifierName:
                    return self._token_text(evt.expr.identifier)
            if evt.kind == SyntaxKind.BinaryEventExpression:
                left = evt.left
                if left.kind == SyntaxKind.SignalEventExpression:
                    if left.expr.kind == SyntaxKind.IdentifierName:
                        return self._token_text(left.expr.identifier)
        elif hasattr(timing, 'expr'):
            evt = timing.expr
            if evt.kind == SyntaxKind.ParenthesizedEventExpression:
                evt = evt.expr
            if evt.kind == SyntaxKind.SignalEventExpression:
                if evt.expr.kind == SyntaxKind.IdentifierName:
                    return self._token_text(evt.expr.identifier)
            if evt.kind == SyntaxKind.BinaryEventExpression:
                left = evt.left
                if left.kind == SyntaxKind.SignalEventExpression:
                    if left.expr.kind == SyntaxKind.IdentifierName:
                        return self._token_text(left.expr.identifier)
        return None

    def _process_statement(self, stmt, ts: TransitionSystem):
        k = stmt.kind
        if k == SyntaxKind.ConditionalStatement:
            self._process_conditional(stmt, ts)
        elif k == SyntaxKind.ExpressionStatement:
            result = self._assign_targets(stmt.expr, ts)
            for target, expr in result.items():
                if target in ts.state_vars:
                    tw = ts.state_vars[target].width
                    ew = expr.size()
                    if tw != ew:
                        if tw > ew:
                            expr = z3.ZeroExt(tw - ew, expr)
                        else:
                            expr = z3.Extract(tw - 1, 0, expr)
                ts.set_next_state(target, expr)
        elif k == SyntaxKind.SequentialBlockStatement:
            for item in stmt.items:
                self._process_statement(item, ts)
        elif k == SyntaxKind.CaseStatement:
            self._process_case(stmt, ts)
        else:
            warnings.warn(f"Unhandled statement: {k}", stacklevel=2)

    def _process_conditional(self, stmt, ts: TransitionSystem):
        self._current_ts = ts
        result = self._stmt_next_conditional(stmt, ts)
        for target, expr in result.items():
            ts.set_next_state(target, expr)

    def _extract_clause_assignments(self, stmt, ts: TransitionSystem) -> dict:
        k = stmt.kind
        if k == SyntaxKind.ExpressionStatement:
            return self._assign_targets(stmt.expr, ts)
        elif k == SyntaxKind.SequentialBlockStatement:
            result = {}
            for item in stmt.items:
                result.update(self._extract_clause_assignments(item, ts))
            return result
        elif k == SyntaxKind.ConditionalStatement:
            return self._stmt_next_conditional(stmt, ts)
        else:
            warnings.warn(f"Unhandled clause assignment: {k}", stacklevel=2)
        return {}

    def _stmt_next_case(self, stmt, ts: TransitionSystem) -> dict:
        case_expr = self._node_to_z3(stmt.expr)
        items = list(stmt.items)
        result = {}
        for item in reversed(items):
            if item.kind == SyntaxKind.DefaultCaseItem:
                result = self._extract_clause_assignments(item.clause, ts)
            elif item.kind == SyntaxKind.StandardCaseItem:
                match_vals = [self._node_to_z3(e) for e in item.expressions]
                clause_dict = self._extract_clause_assignments(item.clause, ts)
                cond = z3.Or(*[case_expr == mv for mv in match_vals]) if len(match_vals) > 1 else (case_expr == match_vals[0])
                new_result = {}
                all_targets = set(result.keys()) | set(clause_dict.keys())
                for t in all_targets:
                    if t in clause_dict:
                        prev = result.get(t, ts.get_next(t))
                        cl_val = clause_dict[t]
                        pv, cv = self._z3_promote_pair(prev, cl_val)
                        new_result[t] = z3.If(cond, cv, pv)
                    else:
                        new_result[t] = result.get(t, ts.get_next(t))
                result = new_result
        return result

    def _process_case(self, stmt, ts: TransitionSystem):
        result = self._stmt_next_case(stmt, ts)
        for target, expr in result.items():
            ts.set_next_state(target, expr)

    def _stmt_next_conditional(self, stmt, ts: TransitionSystem) -> dict:
        self._current_ts = ts
        pred = stmt.predicate
        cond = self._node_to_z3(pred.conditions[0].expr)
        cond_bool = (cond != 0)

        if_true = self._stmt_next(stmt.statement, ts)

        if hasattr(stmt, 'elseClause') and stmt.elseClause is not None:
            clause = stmt.elseClause.clause
            if clause.kind == SyntaxKind.ConditionalStatement:
                if_false = self._stmt_next_conditional(clause, ts)
            else:
                if_false = self._stmt_next(clause, ts)
        else:
            if_false = {}

        result = {}
        for target in set(if_true) | set(if_false):
            t_val = if_true.get(target)
            f_val = if_false.get(target)
            cur = ts.get_cur(target)
            if t_val is not None and f_val is not None:
                tv, fv = self._z3_promote_pair(t_val, f_val)
                result[target] = z3.If(cond_bool, tv, fv)
            elif t_val is not None:
                tv, cv = self._z3_promote_pair(t_val, cur)
                result[target] = z3.If(cond_bool, tv, cv)
            elif f_val is not None:
                cv, fv = self._z3_promote_pair(cur, f_val)
                result[target] = z3.If(cond_bool, cv, fv)
        return result

    def _stmt_next(self, stmt, ts: TransitionSystem) -> dict:
        k = stmt.kind
        if k == SyntaxKind.ExpressionStatement:
            return self._assign_targets(stmt.expr, ts)
        if k == SyntaxKind.SequentialBlockStatement:
            result = {}
            for item in stmt.items:
                result.update(self._stmt_next(item, ts))
            return result
        if k == SyntaxKind.ConditionalStatement:
            return self._stmt_next_conditional(stmt, ts)
        if k == SyntaxKind.CaseStatement:
            return self._stmt_next_case(stmt, ts)
        return {}

    def _assign_targets(self, expr, ts: TransitionSystem) -> dict:
        self._current_ts = ts
        k = expr.kind
        if k in (SyntaxKind.NonblockingAssignmentExpression, SyntaxKind.AssignmentExpression):
            left = expr.left
            right = expr.right
            lname = self._extract_name(left)
            if lname is None:
                return {}
            if lname not in ts.state_vars and lname not in ts.inputs:
                w = self._expr_width(right, ts)
                ts.add_state_var(lname, w)
            r_expr = self._node_to_z3(right)
            return {lname: r_expr}
        return {}

    def _process_expr_stmt(self, stmt, ts: TransitionSystem):
        self._current_ts = ts
        expr = stmt.expr
        if expr.kind == SyntaxKind.AssignmentExpression:
            left = expr.left
            right = expr.right
            lname = self._extract_name(left)
            if lname is None:
                return
            if lname not in ts.state_vars and lname not in ts.inputs:
                w = self._expr_width(right, ts)
                ts.add_state_var(lname, w)
            r_expr = self._node_to_z3(right)
            ts.add_comb_constraint(ts.get_cur(lname) == r_expr)

    def _process_always_comb(self, block, ts: TransitionSystem):
        self._current_ts = ts
        self._comb_mode = True
        stmt = block.statement
        self._process_comb_stmt(stmt, ts)
        self._comb_mode = False

    def _process_comb_stmt(self, stmt, ts: TransitionSystem):
        k = stmt.kind
        if k == SyntaxKind.SequentialBlockStatement:
            for item in stmt.items:
                if not hasattr(item, 'kind') or not hasattr(item, 'getFirstToken'):
                    continue
                self._process_comb_stmt(item, ts)
        elif k == SyntaxKind.ExpressionStatement:
            expr = stmt.expr
            if expr is not None and hasattr(expr, 'kind') and expr.kind == SyntaxKind.AssignmentExpression:
                left = expr.left
                right = expr.right
                lname = self._extract_name(left)
                if lname is not None:
                    if lname not in ts.state_vars and lname not in ts.inputs:
                        w = self._expr_width(right, ts)
                        ts.add_state_var(lname, w)
                    l_expr = self._build_lhs_expr(left, lname, ts)
                    if l_expr is None:
                        l_expr = ts.get_cur(lname)
                    r_expr = self._node_to_z3(right)
                    lw = l_expr.size()
                    rw = r_expr.size()
                    if lw != rw:
                        if lw > rw:
                            r_expr = z3.ZeroExt(lw - rw, r_expr)
                        else:
                            r_expr = z3.Extract(lw - 1, 0, r_expr)
                    ts.add_comb_constraint(l_expr == r_expr)
        elif k in (SyntaxKind.ConditionalStatement,):
            collect_lhs = {}
            assignments = self._stmt_next_conditional(stmt, ts)
            for target, expr in assignments.items():
                lhs_node = collect_lhs.get(target)
                l_expr = self._build_lhs_expr(lhs_node, target, ts) if lhs_node is not None else None
                if l_expr is None:
                    l_expr = ts.get_cur(target)
                cw = l_expr.size()
                ew = expr.size()
                if cw != ew:
                    if cw > ew:
                        expr = z3.ZeroExt(cw - ew, expr)
                    else:
                        expr = z3.Extract(cw - 1, 0, expr)
                ts.add_comb_constraint(l_expr == expr)
        elif k == SyntaxKind.CaseStatement:
            collect_lhs = {}
            assignments = self._collect_case_assignments(stmt, ts)
            for target, expr in assignments.items():
                lhs_node = collect_lhs.get(target)
                l_expr = self._build_lhs_expr(lhs_node, target, ts) if lhs_node is not None else None
                if l_expr is None:
                    l_expr = ts.get_cur(target)
                cw = l_expr.size()
                ew = expr.size()
                if cw != ew:
                    if cw > ew:
                        expr = z3.ZeroExt(cw - ew, expr)
                    else:
                        expr = z3.Extract(cw - 1, 0, expr)
                ts.add_comb_constraint(l_expr == expr)
        elif k == SyntaxKind.ForLoopStatement:
            assignments = self._collect_for_assignments(stmt, ts)
            for target, expr in assignments.items():
                l_expr = ts.get_cur(target)
                cw = l_expr.size()
                ew = expr.size()
                if cw != ew:
                    if cw > ew:
                        expr = z3.ZeroExt(cw - ew, expr)
                    else:
                        expr = z3.Extract(cw - 1, 0, expr)
                ts.add_comb_constraint(l_expr == expr)

    def _collect_for_assignments(self, stmt, ts) -> dict:
        init_val = None; bound_val = None; step = 1; loop_body = None
        for child in stmt:
            if hasattr(child, 'kind') and not isinstance(child.kind, int):
                if child.kind.name == 'ForVariableDeclaration':
                    decls = child.declarators if hasattr(child, 'declarators') else [child.declarator] if hasattr(child, 'declarator') else []
                    for d in decls:
                        if hasattr(d, 'initializer') and d.initializer is not None:
                            init_val = self._eval_literal_expr(d.initializer.expr, ts)
                elif child.kind.name in ('LessThanExpression', 'LessThanEqualExpression'):
                    bound_val = self._eval_literal_expr(child.right, ts)
                    if child.kind.name == 'LessThanEqualExpression' and bound_val is not None:
                        bound_val += 1
                elif child.kind.name in ('PostincrementExpression', 'PreincrementExpression'):
                    step = 1
                elif child.kind.name in ('PostdecrementExpression', 'PredecrementExpression'):
                    step = -1
                elif child.kind == SyntaxKind.SequentialBlockStatement:
                    loop_body = child
        result = {}
        if init_val is not None and bound_val is not None and step != 0 and loop_body is not None:
            saved = getattr(self, '_genvar_subst', None) or {}
            for i in range(init_val, bound_val, step):
                self._genvar_subst = {**saved, 'i': i}
                body_result = self._collect_comb_assignments(loop_body, ts, result)
                if body_result is None:
                    continue
                for var_name, expr in body_result.items():
                    if var_name in result:
                        old_val = result[var_name]
                        bw = max(old_val.size(), expr.size())
                        if old_val.size() < bw:
                            old_val = z3.ZeroExt(bw - old_val.size(), old_val)
                        bit_val = z3.Extract(i, i, expr) if i < expr.size() else z3.BitVecVal(0, 1)
                        if i >= bw:
                            result[var_name] = z3.Concat(z3.ZeroExt(i - bw, old_val), bit_val)
                        elif i == bw - 1:
                            upper = z3.Extract(bw - 2, 0, old_val) if bw > 1 else z3.BitVecVal(0, 1)
                            result[var_name] = z3.Concat(bit_val, upper) if bw > 1 else bit_val
                        elif i == 0:
                            rest = z3.Extract(bw - 1, 1, old_val) if bw > 1 else z3.BitVecVal(0, 1)
                            result[var_name] = z3.Concat(rest, bit_val) if bw > 1 else bit_val
                        else:
                            upper = z3.Extract(bw - 1, i + 1, old_val)
                            lower = z3.Extract(i - 1, 0, old_val)
                            result[var_name] = z3.Concat(upper, bit_val, lower)
                    else:
                        result[var_name] = expr
        return result

    def _collect_comb_assignments(self, stmt, ts, prior: dict = None, _lhs_track: dict = None) -> dict:
        if prior is None:
            prior = {}
        k = stmt.kind
        if k == SyntaxKind.ExpressionStatement:
            result = {}
            expr = stmt.expr
            if expr is not None and hasattr(expr, 'kind') and expr.kind == SyntaxKind.AssignmentExpression:
                lname = self._extract_name(expr.left)
                if lname is not None:
                    if lname not in ts.state_vars and lname not in ts.inputs:
                        w = self._expr_width(expr.right, ts)
                        ts.add_state_var(lname, w)
                    result[lname] = self._node_to_z3(expr.right)
                    if _lhs_track is not None:
                        _lhs_track[lname] = expr.left
            return result
        if k in (SyntaxKind.ConditionalStatement,):
            return self._stmt_next_conditional(stmt, ts)
        if k == SyntaxKind.CaseStatement:
            return self._collect_case_assignments(stmt, ts, prior)
        if k == SyntaxKind.SequentialBlockStatement:
            result = dict(prior)
            for item in stmt.items:
                if not hasattr(item, 'kind') or not hasattr(item, 'getFirstToken'):
                    continue
                item_assignments = self._collect_comb_assignments(item, ts, result, _lhs_track)
                if item_assignments:
                    result.update(item_assignments)
            return result
        if k == SyntaxKind.ForLoopStatement:
            result = dict(prior)
            init_val = None; bound_val = None; step = 1; loop_body = None
            for child in stmt:
                if hasattr(child, 'kind') and not isinstance(child.kind, int):
                    if child.kind.name == 'ForVariableDeclaration':
                        decls = child.declarators if hasattr(child, 'declarators') else [child.declarator] if hasattr(child, 'declarator') else []
                        for d in decls:
                            if hasattr(d, 'initializer') and d.initializer is not None:
                                init_val = self._eval_literal_expr(d.initializer.expr, ts)
                    elif child.kind.name in ('LessThanExpression', 'LessThanEqualExpression'):
                        bound_val = self._eval_literal_expr(child.right, ts)
                        if child.kind.name == 'LessThanEqualExpression' and bound_val is not None:
                            bound_val += 1
                    elif child.kind.name in ('PostincrementExpression', 'PreincrementExpression'):
                        step = 1
                    elif child.kind.name in ('PostdecrementExpression', 'PredecrementExpression'):
                        step = -1
                    elif child.kind == SyntaxKind.SequentialBlockStatement:
                        loop_body = child
            if init_val is not None and bound_val is not None and step != 0 and loop_body is not None:
                saved = getattr(self, '_genvar_subst', None) or {}
                for i in range(init_val, bound_val, step):
                    self._genvar_subst = {**saved, 'i': i}
                    body_result = self._collect_comb_assignments(loop_body, ts, result)
                    if body_result is None:
                        continue
                    for var_name, expr in body_result.items():
                        if var_name in result:
                            old_val = result[var_name]
                            bw = max(old_val.size(), expr.size())
                            if old_val.size() < bw:
                                old_val = z3.ZeroExt(bw - old_val.size(), old_val)
                            bit_val = z3.Extract(i, i, expr) if i < expr.size() else z3.BitVecVal(0, 1)
                            if i >= bw:
                                result[var_name] = z3.Concat(z3.ZeroExt(i - bw, old_val), bit_val)
                            elif i == bw - 1:
                                upper = z3.Extract(bw - 2, 0, old_val) if bw > 1 else z3.BitVecVal(0, 1)
                                result[var_name] = z3.Concat(bit_val, upper) if bw > 1 else bit_val
                            elif i == 0:
                                rest = z3.Extract(bw - 1, 1, old_val) if bw > 1 else z3.BitVecVal(0, 1)
                                result[var_name] = z3.Concat(rest, bit_val) if bw > 1 else bit_val
                            else:
                                upper = z3.Extract(bw - 1, i + 1, old_val)
                                lower = z3.Extract(i - 1, 0, old_val)
                                result[var_name] = z3.Concat(upper, bit_val, lower)

    def _collect_case_assignments(self, stmt, ts, prior: dict = None) -> dict:
        """Process a case statement within always_comb, using prior as fallback defaults."""
        if prior is None:
            prior = {}
        case_expr = self._node_to_z3(stmt.expr)
        items = list(stmt.items)

        result = {}
        for item in reversed(items):
            if item.kind == SyntaxKind.DefaultCaseItem:
                result = self._extract_clause_assignments(item.clause, ts)
            elif item.kind == SyntaxKind.StandardCaseItem:
                match_vals = [self._node_to_z3(e) for e in item.expressions]
                clause_dict = self._extract_clause_assignments(item.clause, ts)
                cond = z3.Or(*[case_expr == mv for mv in match_vals]) if len(match_vals) > 1 else (case_expr == match_vals[0])
                new_result = {}
                all_targets = set(result.keys()) | set(clause_dict.keys())
                for t in all_targets:
                    if t in clause_dict:
                        prev = result.get(t)
                        if prev is None:
                            prev = prior.get(t, ts.get_next(t))
                        cl_val = clause_dict[t]
                        pv, cv = self._z3_promote_pair(prev, cl_val)
                        new_result[t] = z3.If(cond, cv, pv)
                    else:
                        val = result.get(t)
                        if val is None:
                            val = prior.get(t, ts.get_next(t))
                        if val is not None:
                            new_result[t] = val
                result = new_result
        return result

    def _process_cont_assign(self, assign, ts: TransitionSystem):
        self._current_ts = ts
        for a in assign.assignments:
            if a.kind == SyntaxKind.AssignmentExpression:
                left = a.left
                right = a.right
                lname = self._extract_name(left)
                if lname is None:
                    continue
                if lname not in ts.state_vars and lname not in ts.inputs:
                    w = self._expr_width(right, ts)
                    if w is None or w <= 0:
                        w = 1
                    ts.add_state_var(lname, w)
                l_expr = self._build_lhs_expr(left, lname, ts)
                if l_expr is None:
                    l_expr = ts.get_cur(lname)
                r_expr = self._node_to_z3(right)
                lw = l_expr.size()
                rw = r_expr.size()
                if lw != rw:
                    if lw > rw:
                        r_expr = z3.ZeroExt(lw - rw, r_expr)
                    else:
                        r_expr = z3.Extract(lw - 1, 0, r_expr)
                ts.add_comb_constraint(l_expr == r_expr)

    def _build_lhs_expr(self, left, lname, ts):
        if not hasattr(left, 'selectors') or not left.selectors:
            return None
        base = ts.get_cur(lname)
        bw = base.size()
        result = base
        var_dims = ts.get_var_dims(lname) if hasattr(ts, 'get_var_dims') else []
        num_sel = len(left.selectors)
        for idx, sel in enumerate(left.selectors):
            if sel.kind == SyntaxKind.ElementSelect:
                s = sel.selector
                sk = s.kind
                if sk == SyntaxKind.BitSelect:
                    idx_expr = self._eval_literal_expr(s.expr, ts)
                    if idx_expr is None:
                        continue
                    # Selectors match dimensions from outer-most to inner-most.
                    # full_dims = [packed_dims..., unpacked_dims...].
                    # The LAST dimension corresponds to the first selector (outer-most unpacked),
                    # the second-to-last to the second selector, etc.
                    dim_pos = num_sel - 1 - idx
                    if 0 <= dim_pos < len(var_dims):
                        ew = bw // var_dims[dim_pos]
                        if ew <= 0:
                            continue
                        offset = idx_expr * ew
                        if offset + ew > bw:
                            ts.widen_state_var(lname, offset + ew)
                            base = ts.get_cur(lname)
                            bw = base.size()
                            result = base
                        result = z3.Extract(offset + ew - 1, offset, result)
                        bw = result.size()
                    else:
                        if idx_expr >= bw:
                            ts.widen_state_var(lname, idx_expr + 1)
                            base = ts.get_cur(lname)
                            bw = base.size()
                            result = base
                        result = z3.Extract(idx_expr, idx_expr, result)
                elif sk == SyntaxKind.SimpleRangeSelect:
                    hi = self._eval_literal_expr(s.left, ts)
                    lo = self._eval_literal_expr(s.right, ts)
                    if hi is not None and lo is not None:
                        if lo > hi:
                            lo, hi = hi, lo
                        if hi >= bw:
                            ts.widen_state_var(lname, hi + 1)
                            base = ts.get_cur(lname)
                            result = base
                        result = z3.Extract(hi, lo, result)
        return result

    def _process_assertion(self, stmt, ts: TransitionSystem,
                           directive: str | None = None):
        self._current_ts = ts

        if stmt.kind == SyntaxKind.ConcurrentAssertionMember:
            stmt = stmt.statement

        try:
            source_text = str(stmt)
            if source_text.startswith('AssertPropertyStatement'):
                source_text = stmt.toString() if hasattr(stmt, 'toString') else str(stmt)
            source_text = source_text.strip()
        except Exception:
            source_text = ""

        if directive is None:
            if stmt.kind == SyntaxKind.AssumePropertyStatement:
                directive = "assume"
            elif stmt.kind == SyntaxKind.CoverPropertyStatement:
                directive = "cover"
            else:
                directive = "assert"

        if not hasattr(stmt, 'propertySpec') or stmt.propertySpec is None:
            return

        ps = stmt.propertySpec
        clock = None
        disable_cond = None

        for child in ps:
            if not hasattr(child, 'kind'):
                continue
            if child.kind == SyntaxKind.EventControlWithExpression:
                clock = self._extract_clock(child)
            elif child.kind == SyntaxKind.DisableIff:
                for dc in child:
                    if not hasattr(dc, 'kind'):
                        continue
                    dk = str(dc.kind)
                    if 'Expression' in dk and 'Keyword' not in dk and 'Operator' not in dk:
                        for sc in dc:
                            if hasattr(sc, 'kind') and 'Expression' in str(sc.kind) and 'Keyword' not in str(sc.kind):
                                dc = sc
                                break
                        bv = self._node_to_z3(dc)
                        if bv is not None:
                            disable_cond = (bv != 0)
                        break

        if hasattr(ps, 'expr') and ps.expr is not None:
            self._disable_cond = disable_cond
            result = self._property_to_z3(ps.expr, clock, ts, directive, source=source_text)
            self._disable_cond = None
            if result is not None:
                if disable_cond is not None:
                    result = z3.Implies(z3.Not(disable_cond), result)
                if directive == "assume":
                    prefix = f"assume_{len(ts.assumptions)}"
                    ts.add_assumption(result, source=source_text)
                elif directive == "cover":
                    prefix = f"cover_{len(ts.cover_properties)}"
                    ts.add_cover_property(prefix, result, source=source_text)
                else:
                    prefix = f"assert_{len(ts.properties)}"
                    ts.add_property(prefix, result, source=source_text)

    def _build_step_chain(self, ts: TransitionSystem, n_steps: int
                          ) -> tuple[list[dict[str, z3.BitVecRef]], list[z3.BoolRef]]:
        """Build a chain of step variables for n_steps future cycles.

        Returns (step_vars, step_constraints):
          step_vars[k] = {name: z3_var} for step k (0 = current state)
          step_constraints link each step to the next via ts transition functions.

        Step variables have unique names per call to avoid collisions.
        """
        chain_id = self._chain_counter
        self._chain_counter += 1
        step_vars = [{name: ts.get_cur(name) for name in ts.state_vars}]
        step_constraints = []
        for k in range(1, n_steps + 1):
            cur = step_vars[k - 1]
            nxt = {}
            for name in ts.state_vars:
                w = ts.state_vars[name].width
                nxt[name] = z3.BitVec(f"{name}_c{chain_id}_s{k}", w)
            step_vars.append(nxt)
            for name in ts.state_vars:
                if name in ts._next_state_exprs:
                    nexpr = ts._next_state_exprs[name]
                    shifted = z3.substitute(
                        nexpr,
                        *[(ts.get_cur(n), cur[n]) for n in ts.state_vars]
                    )
                    step_constraints.append(nxt[name] == shifted)
        return step_vars, step_constraints

    def _apply_repetition(self, inner_expr: z3.BoolRef, ts: TransitionSystem,
                          rep_node) -> z3.BoolRef:
        """Apply SequenceRepetition ([*N], [+], [*M:N]) to an already-evaluated inner expression."""
        rep_count = 1
        is_plus = False
        has_range = False
        range_lo = 1
        range_hi = 1
        for child in rep_node:
            if hasattr(child, 'kind'):
                ck = str(child.kind)
                if 'Plus' in ck:
                    is_plus = True
                elif 'Star' in ck:
                    pass
                elif 'BitSelect' in ck:
                    for sc in child:
                        if hasattr(sc, 'kind') and 'IntegerLiteral' in str(sc.kind):
                            try:
                                rep_count = int(self._token_text(sc), 0)
                            except:
                                pass
                elif 'RangeSelect' in ck:
                    lo_node = child.left if hasattr(child, 'left') else None
                    hi_node = child.right if hasattr(child, 'right') else None
                    lo = self._eval_literal_expr(lo_node) if lo_node is not None else None
                    hi = self._eval_literal_expr(hi_node) if hi_node is not None else None
                    if lo is not None and hi is not None:
                        has_range = True
                        range_lo, range_hi = min(lo, hi), max(lo, hi)

        if is_plus:
            MAX_REP = 8
            self._delay_context["inner_steps"] = max(
                self._delay_context.get("inner_steps", 0), MAX_REP)
            options = []
            for n in range(1, MAX_REP + 1):
                if n == 1:
                    options.append(inner_expr)
                else:
                    sv, sc = self._build_step_chain(ts, n - 1)
                    checks = [z3.substitute(
                        inner_expr,
                        *[(ts.get_cur(name), sv[k][name]) for name in ts.state_vars]
                    ) for k in range(n)]
                    opt = z3.And(*checks)
                    if sc:
                        opt = z3.And(z3.And(*sc), opt)
                    options.append(opt)
            return z3.Or(*options)

        if has_range:
            self._delay_context["inner_steps"] = max(
                self._delay_context.get("inner_steps", 0), range_hi)
            options = []
            for n in range(range_lo, range_hi + 1):
                if n == 1:
                    options.append(inner_expr)
                else:
                    sv, sc = self._build_step_chain(ts, n - 1)
                    checks = [z3.substitute(
                        inner_expr,
                        *[(ts.get_cur(name), sv[k][name]) for name in ts.state_vars]
                    ) for k in range(n)]
                    opt = z3.And(*checks)
                    if sc:
                        opt = z3.And(z3.And(*sc), opt)
                    options.append(opt)
            return z3.Or(*options)

        if rep_count == 1:
            return inner_expr

        self._delay_context["inner_steps"] = max(
            self._delay_context.get("inner_steps", 0), rep_count)
        sv, sc = self._build_step_chain(ts, rep_count - 1)
        checks = [z3.substitute(
            inner_expr,
            *[(ts.get_cur(name), sv[k][name]) for name in ts.state_vars]
        ) for k in range(rep_count)]
        result = z3.And(*checks)
        if sc:
            result = z3.And(z3.And(*sc), result)
        return result

    def _property_to_z3(self, node, clock: str | None, ts: TransitionSystem,
                        directive: str = "assert", source: str = "") -> z3.BoolRef | None:
        k = node.kind

        if k == SyntaxKind.ImplicationPropertyExpr:
            ant = self._property_to_z3(node.left, clock, ts, directive, source=source)
            cons = self._property_to_z3(node.right, clock, ts, directive, source=source)
            if ant is None or cons is None:
                return None
            op_text = str(node.op.rawText) if hasattr(node.op, 'rawText') else "|->"
            if op_text == "|=>":
                dc = self._delay_context
                # Ensure step_vars exist; create if [*N] without ##N
                if not dc.get("step_vars") and dc.get("inner_steps", 1) > 1:
                    inner = dc["inner_steps"]
                    sv, sc = self._build_step_chain(ts, inner - 1)
                    dc["step_vars"] = sv
                    dc["total_steps"] = inner - 1
                    dc["_step_constraints"] = sc

                if dc.get("range_options"):
                    step_vars = dc["step_vars"]
                    total_steps = dc["total_steps"]
                    ext_constraints = []
                    ext_map = {}
                    cur = step_vars[total_steps]
                    for name in ts.state_vars:
                        ext = z3.BitVec(f"{name}_ext_{total_steps + 1}", ts.state_vars[name].width)
                        ext_map[name] = ext
                        if name in ts._next_state_exprs:
                            nexpr = ts._next_state_exprs[name]
                            shifted = z3.substitute(
                                nexpr,
                                *[(ts.get_cur(n), cur[n]) for n in ts.state_vars]
                            )
                            ext_constraints.append(ext == shifted)
                    cons_delayed = z3.substitute(
                        cons,
                        *[(ts.get_cur(name), ext_map[name]) for name in ts.state_vars]
                    )
                    shifted_options = []
                    for k, opt_expr in dc["range_options"]:
                        opt_shifted = z3.substitute(
                            opt_expr,
                            *[(ts.get_cur(name), step_vars[k][name])
                              for name in ts.state_vars]
                        )
                        if k < total_steps:
                            cons_k = z3.substitute(
                                cons,
                                *[(ts.get_cur(name), step_vars[k + 1][name])
                                  for name in ts.state_vars]
                            )
                        else:
                            cons_k = cons_delayed
                        shifted_options.append(z3.And(opt_shifted, cons_k))
                    tp_expr = z3.Implies(
                        z3.And(ant, *ext_constraints),
                        z3.Or(*shifted_options)
                    )
                elif dc.get("step_vars"):
                    step_vars = dc["step_vars"]
                    total_steps = dc["total_steps"]
                    cur = step_vars[total_steps]
                    ext = {}
                    extra = list(dc.get("_step_constraints", []))
                    for name in ts.state_vars:
                        w = ts.state_vars[name].width
                        ext[name] = z3.BitVec(f"{name}_ext_{total_steps + 1}", w)
                        if name in ts._next_state_exprs:
                            nexpr = ts._next_state_exprs[name]
                            shifted = z3.substitute(
                                nexpr,
                                *[(ts.get_cur(n), cur[n]) for n in ts.state_vars]
                            )
                            extra.append(ext[name] == shifted)
                    cons_delayed = z3.substitute(
                        cons,
                        *[(ts.get_cur(name), ext[name]) for name in ts.state_vars]
                    )
                    tp_expr = z3.Implies(z3.And(ant, *extra), cons_delayed)
                else:
                    cons_next = z3.substitute(
                        cons,
                        *[(ts.get_cur(name), ts.get_next(name)) for name in ts.state_vars]
                    )
                    tp_expr = z3.Implies(ant, cons_next)
                self._delay_context = {}
                dc = self._disable_cond
                if dc is not None:
                    tp_expr = z3.Implies(z3.Not(dc), tp_expr)
                if directive == "assume":
                    ts.add_assumption(tp_expr, source=source)
                else:
                    tn = f"trans_{directive}_{len(ts.trans_properties)}"
                    ts.add_trans_property(tn, tp_expr, source=source)
                return None
            else:
                imp_expr = z3.Implies(ant, cons)
                dc = self._disable_cond
                if dc is not None:
                    imp_expr = z3.Implies(z3.Not(dc), imp_expr)
                if directive == "assume":
                    ts.add_assumption(imp_expr, source=source)
                else:
                    ts.add_property(f"{directive}_{len(ts.properties)}",
                                    imp_expr, source=source)
                return None

        if k in (SyntaxKind.ParenthesizedPropertyExpr, SyntaxKind.SimplePropertyExpr, SyntaxKind.SimpleSequenceExpr):
            if hasattr(node, 'expr'):
                inner_expr = self._property_to_z3(node.expr, clock, ts, directive, source=source)
                if inner_expr is None:
                    return None
                for child in node:
                    if hasattr(child, 'kind') and child.kind == SyntaxKind.SequenceRepetition:
                        return self._apply_repetition(inner_expr, ts, child)
                return inner_expr
            return None

        if k == SyntaxKind.ClockingPropertyExpr:
            if hasattr(node, 'expr'):
                return self._property_to_z3(node.expr, clock, ts, directive, source=source)
            return None

        if k == SyntaxKind.ClockingSequenceExpr:
            if hasattr(node, 'expr'):
                return self._property_to_z3(node.expr, clock, ts, directive, source=source)
            return None

        if k == SyntaxKind.ParenthesizedSequenceExpr:
            if hasattr(node, 'expr'):
                return self._property_to_z3(node.expr, clock, ts, directive, source=source)
            return None

        if k == SyntaxKind.UnaryPropertyExpr:
            inner = None
            keyword = None
            for child in node:
                if hasattr(child, 'kind'):
                    ck = str(child.kind)
                    if 'NotKeyword' in ck:
                        keyword = 'not'
                    elif 'AlwaysKeyword' in ck:
                        keyword = 'always'
                    elif 'SEventuallyKeyword' in ck:
                        keyword = 's_eventually'
                    elif 'SNexttimeKeyword' in ck:
                        keyword = 's_nexttime'
                    else:
                        inner = self._property_to_z3(child, clock, ts, directive, source=source)
            if inner is None:
                return None
            if keyword == 'not':
                return z3.Not(inner)
            if keyword == 's_eventually':
                return inner
            if keyword == 'always':
                return inner
            return inner

        if k == SyntaxKind.AndSequenceExpr:
            children = [c for c in node if hasattr(c, 'kind') and 'Keyword' not in str(c.kind)]
            if len(children) >= 2:
                l = self._property_to_z3(children[0], clock, ts, directive, source=source)
                r = self._property_to_z3(children[1], clock, ts, directive, source=source)
                if l is not None and r is not None:
                    return z3.And(l, r)
            return None

        if k == SyntaxKind.OrSequenceExpr:
            children = [c for c in node if hasattr(c, 'kind') and 'Keyword' not in str(c.kind)]
            if len(children) >= 2:
                l = self._property_to_z3(children[0], clock, ts, directive, source=source)
                r = self._property_to_z3(children[1], clock, ts, directive, source=source)
                if l is not None and r is not None:
                    return z3.Or(l, r)
            return None

        if k == SyntaxKind.IntersectSequenceExpr:
            children = [c for c in node if hasattr(c, 'kind') and 'Keyword' not in str(c.kind)]
            if len(children) >= 2:
                l = self._property_to_z3(children[0], clock, ts, directive, source=source)
                r = self._property_to_z3(children[1], clock, ts, directive, source=source)
                if l is not None and r is not None:
                    return z3.And(l, r)
            return None

        if k == SyntaxKind.IffPropertyExpr:
            children = [c for c in node if hasattr(c, 'kind') and 'Keyword' not in str(c.kind)]
            if len(children) >= 2:
                l = self._property_to_z3(children[0], clock, ts, directive, source=source)
                r = self._property_to_z3(children[1], clock, ts, directive, source=source)
                if l is not None and r is not None:
                    return (l == r)
            return None

        if k == SyntaxKind.SUntilPropertyExpr:
            children = [c for c in node if hasattr(c, 'kind') and 'Keyword' not in str(c.kind)]
            if len(children) >= 2:
                l = self._property_to_z3(children[0], clock, ts, directive, source=source)
                r = self._property_to_z3(children[1], clock, ts, directive, source=source)
                if l is not None and r is not None:
                    return z3.Or(r, l)
            return None

        if k == SyntaxKind.UntilPropertyExpr:
            children = [c for c in node if hasattr(c, 'kind') and 'Keyword' not in str(c.kind)]
            if len(children) >= 2:
                l = self._property_to_z3(children[0], clock, ts, directive, source=source)
                r = self._property_to_z3(children[1], clock, ts, directive, source=source)
                if l is not None and r is not None:
                    return z3.Or(r, l)
            return None

        if k == SyntaxKind.SUntilWithPropertyExpr:
            children = [c for c in node if hasattr(c, 'kind') and 'Keyword' not in str(c.kind)]
            if len(children) >= 2:
                l = self._property_to_z3(children[0], clock, ts, directive, source=source)
                r = self._property_to_z3(children[1], clock, ts, directive, source=source)
                if l is not None and r is not None:
                    return z3.Or(r, l)
            return None

        if k == SyntaxKind.UntilWithPropertyExpr:
            children = [c for c in node if hasattr(c, 'kind') and 'Keyword' not in str(c.kind)]
            if len(children) >= 2:
                l = self._property_to_z3(children[0], clock, ts, directive, source=source)
                r = self._property_to_z3(children[1], clock, ts, directive, source=source)
                if l is not None and r is not None:
                    return z3.Or(r, l)
            return None

        if k == SyntaxKind.ConditionalPropertyExpr:
            ant = None
            cons = None
            cond = None
            items = [c for c in node if hasattr(c, 'kind') and 'Keyword' not in str(c.kind)]
            if len(items) >= 3:
                cond = self._property_to_z3(items[0], clock, ts, directive, source=source)
                ant = self._property_to_z3(items[1], clock, ts, directive, source=source)
                cons = self._property_to_z3(items[2], clock, ts, directive, source=source)
            elif len(items) >= 2:
                cond = items[0]
                ant = self._property_to_z3(items[0] if cond else items[1], clock, ts, directive, source=source)
                cons = self._property_to_z3(items[1] if cond else items[0], clock, ts, directive, source=source)
            if cond is not None and ant is not None and cons is not None:
                return z3.Or(z3.Not(cond), z3.And(ant, cons))
            if ant is not None and cons is not None:
                return z3.And(ant, cons)
            return ant if ant is not None else cons

        if k == SyntaxKind.DelayedSequenceExpr:
            children = [c for c in node if hasattr(c, 'kind')]
            if len(children) >= 2:
                left_seq = children[0]
                delay_elem = children[1]
                left_expr = self._property_to_z3(left_seq, clock, ts, directive, source=source)
                if left_expr is None:
                    return None
                delay_cycles = 1
                right_seq = None
                range_delays = None
                for dc in delay_elem:
                    if hasattr(dc, 'kind'):
                        dk = str(dc.kind)
                        if 'IntegerLiteral' in dk or 'Litera' in dk:
                            try:
                                delay_cycles = int(self._token_text(dc), 0)
                            except:
                                pass
                        elif 'RangeSelect' in dk or dk == 'SimpleRangeSelect':
                            delay_left = self._eval_literal_expr(dc.left)
                            delay_right = (self._eval_literal_expr(dc.right)
                                           if hasattr(dc, 'right') and dc.right
                                           else None)
                            if (delay_left is not None and delay_right is not None
                                    and delay_left != delay_right):
                                lo, hi = min(delay_left, delay_right), max(delay_left, delay_right)
                                range_delays = (lo, hi)
                            elif delay_left is not None:
                                delay_cycles = delay_left
                        elif 'SimpleSequenceExpr' in dk or 'SimplePropertyExpr' in dk:
                            right_seq = dc
                if right_seq is None:
                    for dc in delay_elem:
                        if hasattr(dc, 'kind') and 'SimpleSequence' in str(dc.kind):
                            right_seq = dc
                            break
                if right_seq is None:
                    return left_expr
                right_expr = self._property_to_z3(right_seq, clock, ts, directive, source=source)
                if right_expr is None:
                    return None

                max_delay = delay_cycles
                if range_delays:
                    max_delay = max(max_delay, range_delays[1])

                # Build step-variable chain for multi-cycle delay
                step_constraints = []
                if max_delay > 0 and ts.state_vars:
                    step_vars, step_constraints = self._build_step_chain(ts, max_delay)
                else:
                    step_vars = [{name: ts.get_cur(name) for name in ts.state_vars},
                                 {name: ts.get_next(name) for name in ts.state_vars}]

                # Incorporate inner steps (from [*N] etc) into total
                inner = self._delay_context.get("inner_steps", 1)
                if range_delays:
                    total_steps = range_delays[1] + inner - 1
                else:
                    total_steps = delay_cycles + inner - 1

                # Extend step_vars if needed to cover total_steps
                while len(step_vars) <= total_steps:
                    k = len(step_vars)
                    cur = step_vars[k - 1]
                    nxt = {}
                    for name in ts.state_vars:
                        w = ts.state_vars[name].width
                        nxt[name] = z3.BitVec(f"{name}_c{ts.name}_s{k}", w)
                    step_vars.append(nxt)
                    for name in ts.state_vars:
                        if name in ts._next_state_exprs:
                            nexpr = ts._next_state_exprs[name]
                            shifted = z3.substitute(
                                nexpr,
                                *[(ts.get_cur(n), cur[n]) for n in ts.state_vars]
                            )
                            step_constraints.append(nxt[name] == shifted)

                self._delay_context = {
                    "step_vars": step_vars,
                    "total_steps": total_steps,
                }

                if range_delays:
                    lo, hi = range_delays
                    options = []
                    for k in range(lo, hi + 1):
                        delayed = z3.substitute(
                            right_expr,
                            *[(ts.get_cur(name), step_vars[k][name])
                              for name in ts.state_vars]
                        )
                        options.append(delayed)
                    self._delay_context = {
                        "step_vars": step_vars,
                        "total_steps": total_steps,
                        "range_options": list(zip(range(lo, hi + 1), options)),
                    }
                    combined = z3.Or(*options)
                    if step_constraints:
                        return z3.And(left_expr, z3.And(*step_constraints), combined)
                    return z3.And(left_expr, combined)

                if delay_cycles == 0:
                    return z3.And(left_expr, right_expr)

                delayed = z3.substitute(
                    right_expr,
                    *[(ts.get_cur(name), step_vars[delay_cycles][name])
                      for name in ts.state_vars]
                )
                if step_constraints:
                    return z3.And(left_expr, z3.And(*step_constraints), delayed)
                return z3.And(left_expr, delayed)
            return None

        if k == SyntaxKind.WithinSequenceExpr:
            children = [c for c in node if hasattr(c, 'kind') and 'Keyword' not in str(c.kind)]
            if len(children) >= 2:
                l = self._property_to_z3(children[0], clock, ts, directive, source=source)
                r = self._property_to_z3(children[1], clock, ts, directive, source=source)
                if l is not None and r is not None:
                    return z3.And(l, r)
            return None

        if k == SyntaxKind.ThroughoutSequenceExpr:
            children = [c for c in node if hasattr(c, 'kind') and 'Keyword' not in str(c.kind)]
            if len(children) >= 2:
                l = self._property_to_z3(children[0], clock, ts, directive, source=source)
                r = self._property_to_z3(children[1], clock, ts, directive, source=source)
                if l is not None and r is not None:
                    return z3.And(l, r)
            return None

        if k == SyntaxKind.FirstMatchSequenceExpr:
            for child in node:
                if hasattr(child, 'kind') and 'Sequence' in str(child.kind):
                    return self._property_to_z3(child, clock, ts, directive, source=source)
            return None

        if k == SyntaxKind.SequenceRepetition:
            return None

        prop_bv = self._node_to_z3(node)
        if prop_bv is not None:
            return (prop_bv != 0)
        return None

    def parse_to_ts(self, filepath: str, top_name: str = None) -> TransitionSystem:
        systems = self.parse_file(filepath)
        if not systems:
            raise RuntimeError("No modules found")
        if top_name:
            for ts in systems:
                if ts.name == top_name:
                    return ts
            raise RuntimeError(f"Module '{top_name}' not found in {filepath}")
        return systems[0]

    def parse_text_to_ts(self, text: str, top_name: str = None) -> TransitionSystem:
        systems = self.parse_text(text)
        if not systems:
            raise RuntimeError("No modules found")
        if top_name:
            for ts in systems:
                if ts.name == top_name:
                    return ts
            raise RuntimeError(f"Module '{top_name}' not found")
        return systems[0]
