import z3
import os
import warnings
from pyslang.driver import Driver
from pyslang.syntax import SyntaxKind
from pyslang.parsing import TokenKind
from ..ir.transition_system import TransitionSystem


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
    def __init__(self):
        self.driver = Driver()
        self.driver.addStandardArgs()
        self._past_counter = 0

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
        self._extract_header_params(header, ts)
        self._extract_ports(header, ts)
        self._resolve_header_imports(header, ts)
        self._extract_body(mod_node, ts)
        return ts

    def _extract_header_params(self, header, ts: TransitionSystem):
        if hasattr(header, 'parameters') and header.parameters is not None:
            for p in header.parameters:
                if hasattr(p, 'kind') and p.kind == SyntaxKind.ParameterDeclaration:
                    self._process_param_decl(p, ts)

    def _process_param_decl(self, node, ts: TransitionSystem, width_override: int = None):
        w = width_override
        if w is None and hasattr(node, 'type') and node.type is not None:
            w = self._extract_width_from_node(node.type, ts)
        if w is None or w <= 0:
            w = 1
        for decl in node.declarators:
            name = self._token_text(decl.name)
            init_val = None
            if hasattr(decl, 'initializer') and decl.initializer is not None:
                init_val = self._eval_literal_expr(decl.initializer.expr, ts)
            if name not in ts.params:
                ts.add_param(name, w, init_val)

    def _resolve_header_imports(self, header, ts: TransitionSystem):
        """Resolve package imports from the module header and inject params."""
        for child in header:
            if hasattr(child, 'kind') and child.kind == SyntaxKind.PackageImportDeclaration:
                self._resolve_package_import(child, ts)

    def _is_signed_expr(self, node) -> bool:
        ts = getattr(self, '_current_ts', None)
        if ts is None or not ts.signed_vars:
            return False
        k = node.kind
        if k == SyntaxKind.IdentifierName:
            name = self._token_text(node.identifier)
            return name in ts.signed_vars
        if hasattr(node, 'left') and node.left is not None and hasattr(node.left, 'kind'):
            if self._is_signed_expr(node.left):
                return True
        if hasattr(node, 'right') and node.right is not None and hasattr(node.right, 'kind'):
            if self._is_signed_expr(node.right):
                return True
        if hasattr(node, 'operand') and node.operand is not None and hasattr(node.operand, 'kind'):
            if self._is_signed_expr(node.operand):
                return True
        return False

    def _is_signed_type(self, node) -> bool:
        if hasattr(node, 'signing') and node.signing is not None:
            sk = node.signing.kind
            if hasattr(sk, 'name'):
                return 'Signed' in sk.name
            return sk == TokenKind.SignedKeyword
        return False

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

    def _token_text(self, tok) -> str:
        if hasattr(tok, 'valueText'):
            return str(tok.valueText)
        if hasattr(tok, 'rawText'):
            return str(tok.rawText)
        return str(tok).strip()

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

    def _extract_width_from_node(self, node, ts: TransitionSystem = None) -> int | None:
        if node.kind == SyntaxKind.ImplicitType:
            if hasattr(node, 'dimensions') and node.dimensions:
                for dim in node.dimensions:
                    w = self._dimension_width(dim, ts)
                    if w is not None and w > 1:
                        return w
            return None
        if node.kind == SyntaxKind.NamedType:
            type_name = None
            for child in node:
                if hasattr(child, 'kind'):
                    if child.kind == SyntaxKind.IdentifierName:
                        type_name = str(child).strip()
                    elif child.kind == SyntaxKind.IdentifierSelectName:
                        type_name = self._token_text(child.identifier).strip()
            if type_name and ts and type_name in ts.params and ts.params[type_name][0] == 'type_width':
                bw = ts.params[type_name][1]
                return bw
            if hasattr(node, 'dimensions') and node.dimensions:
                for dim in node.dimensions:
                    w = self._dimension_width(dim, ts)
                    if w is not None and w > 1:
                        return w
            return None
        if hasattr(node, 'dimensions') and node.dimensions:
            for dim in node.dimensions:
                w = self._dimension_width(dim, ts)
                if w is not None and w > 1:
                    return w
        return None

    def _dimension_width(self, dim, ts: TransitionSystem = None) -> int:
        if ts is None:
            ts = getattr(self, '_current_ts', None)
        if not hasattr(dim, 'specifier'):
            return 1
        spec = dim.specifier
        if not hasattr(spec, 'selector'):
            return 1
        sel = spec.selector
        if hasattr(sel, 'left') and hasattr(sel, 'right'):
            lo = self._eval_literal_expr(sel.left, ts)
            ro = self._eval_literal_expr(sel.right, ts)
            if lo is not None and ro is not None:
                return abs(lo - ro) + 1
        return 1

    def _eval_literal(self, node) -> int | None:
        if hasattr(node, 'literal'):
            return self._eval_literal(node.literal)
        text = self._token_text(node) if hasattr(node, 'valueText') or hasattr(node, 'rawText') else None
        if text:
            try:
                return int(text, 0)
            except (ValueError, AttributeError):
                return None
        return None

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
                pass

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
        elif it_expr.kind == SyntaxKind.PreincrementExpression:
            step = 1
        elif it_expr.kind == SyntaxKind.PostdecrementExpression:
            step = -1
        elif it_expr.kind == SyntaxKind.PredecrementExpression:
            step = -1
        elif it_expr.kind == SyntaxKind.AssignmentExpression:
            step_val = self._eval_literal_expr(it_expr.rhs, ts)
            if step_val is not None:
                step = step_val

        for i in range(init_val, bound_val, step):
            self._process_generate_body(node.block, ts, genvar_subst={genvar_name: i})

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
        if genvar_subst:
            self._genvar_subst = genvar_subst
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
            pass
        elif k == SyntaxKind.ModuleInstantiation:
            pass
        else:
            warnings.warn(f"Unhandled generate member: {k}", stacklevel=2)
        if genvar_subst:
            self._genvar_subst = None

    def _eval_literal_expr(self, node, ts: TransitionSystem = None) -> int | None:
        if node is None:
            return None
        k = node.kind

        if k == SyntaxKind.IntegerLiteralExpression:
            return self._eval_literal(node.literal)
        if k == SyntaxKind.IntegerVectorExpression:
            val = self._eval_literal(node.value) if hasattr(node, 'value') else None
            return val

        if k == SyntaxKind.IdentifierName:
            name = self._token_text(node.identifier)
            if getattr(self, '_genvar_subst', None) and name in self._genvar_subst:
                return self._genvar_subst[name]
            if ts is not None and name in ts.params:
                return ts.params[name][1]
            return None

        if k == SyntaxKind.ParenthesizedExpression:
            return self._eval_literal_expr(node.expression, ts)

        has_operand = hasattr(node, 'operand') and node.operand is not None
        has_left = hasattr(node, 'left') and node.left is not None
        has_right = hasattr(node, 'right') and node.right is not None

        if has_operand and not has_left and not has_right:
            inner = self._eval_literal_expr(node.operand, ts)
            if inner is None:
                return None
            if k == SyntaxKind.UnaryMinusExpression:
                return -inner
            if k == SyntaxKind.UnaryPlusExpression:
                return inner
            if k == SyntaxKind.UnaryBitwiseNotExpression:
                return ~inner
            if k == SyntaxKind.UnaryLogicalNotExpression:
                return 0 if inner else 1
            return None

        if has_left and has_right:
            left = self._eval_literal_expr(node.left, ts)
            right = self._eval_literal_expr(node.right, ts)
            if left is None or right is None:
                return None
            if k == SyntaxKind.AddExpression:
                return left + right
            if k == SyntaxKind.SubtractExpression:
                return left - right
            if k == SyntaxKind.MultiplyExpression:
                return left * right
            if k == SyntaxKind.DivideExpression:
                return left // right if right != 0 else None
            if k == SyntaxKind.ModExpression:
                return left % right if right != 0 else None
            if k == SyntaxKind.EqualityExpression:
                return 1 if left == right else 0
            if k == SyntaxKind.InequalityExpression:
                return 1 if left != right else 0
            if k == SyntaxKind.LessThanExpression:
                return 1 if left < right else 0
            if k == SyntaxKind.GreaterThanExpression:
                return 1 if left > right else 0
            if k == SyntaxKind.LessThanEqualExpression:
                return 1 if left <= right else 0
            if k == SyntaxKind.GreaterThanEqualExpression:
                return 1 if left >= right else 0
            if k == SyntaxKind.BinaryAndExpression:
                return left & right
            if k == SyntaxKind.BinaryOrExpression:
                return left | right
            if k == SyntaxKind.BinaryXorExpression:
                return left ^ right
            if k == SyntaxKind.LogicalAndExpression:
                return 1 if (left and right) else 0
            if k == SyntaxKind.LogicalOrExpression:
                return 1 if (left or right) else 0
            if k == SyntaxKind.LogicalShiftRightExpression:
                return left >> right
            if k == SyntaxKind.LogicalShiftLeftExpression:
                return left << right
            if k == SyntaxKind.ArithmeticShiftRightExpression:
                return left >> right
            if k == SyntaxKind.ArithmeticShiftLeftExpression:
                return left << right
            return None

        return None

    def _process_data_declaration(self, node, ts: TransitionSystem):
        w = self._extract_width_from_node(node.type, ts)
        if w is None or w <= 0:
            w = 1
        signed = self._is_signed_type(node.type)
        array_dims = self._extract_array_dims(node.type, ts)
        # Multiply base width by array dimensions for total packed width
        for d in array_dims:
            w *= d
        for decl in node.declarators:
            if not hasattr(decl, 'name'):
                continue
            try:
                name = self._token_text(decl.name)
            except Exception:
                continue
            if name not in ts.state_vars and name not in ts.inputs:
                ts.add_state_var(name, w, signed=signed)
            if array_dims:
                ts.set_var_dims(name, array_dims)

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

    def _signal_width(self, name: str, ts: TransitionSystem) -> int:
        if name in ts.state_vars:
            return ts.state_vars[name].width
        if name in ts.inputs:
            return ts.inputs[name].width
        return 1

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

    def _extract_name(self, node) -> str | None:
        if node.kind == SyntaxKind.IdentifierName:
            return self._token_text(node.identifier)
        if node.kind == SyntaxKind.IdentifierSelectName:
            return self._token_text(node.identifier)
        return None

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
        assignments = self._collect_comb_assignments(stmt, ts)
        for target, expr in assignments.items():
            cur = ts.get_cur(target)
            cw = cur.size()
            ew = expr.size()
            if cw != ew:
                if cw > ew:
                    expr = z3.ZeroExt(cw - ew, expr)
                else:
                    expr = z3.Extract(cw - 1, 0, expr)
            ts.add_comb_constraint(cur == expr)
        self._comb_mode = False

    def _collect_comb_assignments(self, stmt, ts, prior: dict = None) -> dict:
        if prior is None:
            prior = {}
        k = stmt.kind
        if k == SyntaxKind.ExpressionStatement:
            result = {}
            expr = stmt.expr
            if expr.kind == SyntaxKind.AssignmentExpression:
                lname = self._extract_name(expr.left)
                if lname is not None:
                    if lname not in ts.state_vars and lname not in ts.inputs:
                        w = self._expr_width(expr.right, ts)
                        ts.add_state_var(lname, w)
                    result[lname] = self._node_to_z3(expr.right)
            return result
        if k in (SyntaxKind.ConditionalStatement,):
            return self._stmt_next_conditional(stmt, ts)
        if k == SyntaxKind.CaseStatement:
            return self._collect_case_assignments(stmt, ts, prior)
        if k == SyntaxKind.SequentialBlockStatement:
            result = dict(prior)
            for item in stmt.items:
                item_assignments = self._collect_comb_assignments(item, ts, result)
                result.update(item_assignments)
            return result
        return {}

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
                    ts.add_state_var(lname, w)
                r_expr = self._node_to_z3(right)
                cur = ts.get_cur(lname)
                cw = cur.size()
                ew = r_expr.size()
                if cw != ew:
                    if cw > ew:
                        r_expr = z3.ZeroExt(cw - ew, r_expr)
                    else:
                        r_expr = z3.Extract(cw - 1, 0, r_expr)
                ts.add_comb_constraint(cur == r_expr)

    def _process_assertion(self, stmt, ts: TransitionSystem,
                           directive: str | None = None):
        self._current_ts = ts

        if stmt.kind == SyntaxKind.ConcurrentAssertionMember:
            stmt = stmt.statement

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
        if hasattr(ps, 'clocking') and ps.clocking is not None:
            clock = self._extract_clock(ps.clocking)

        if hasattr(ps, 'expr') and ps.expr is not None:
            result = self._property_to_z3(ps.expr, clock, ts, directive)
            if result is not None:
                if directive == "assume":
                    prefix = f"assume_{len(ts.assumptions)}"
                    ts.add_assumption(result)
                elif directive == "cover":
                    prefix = f"cover_{len(ts.cover_properties)}"
                    ts.add_cover_property(prefix, result)
                else:
                    prefix = f"assert_{len(ts.properties)}"
                    ts.add_property(prefix, result)

    def _property_to_z3(self, node, clock: str | None, ts: TransitionSystem,
                        directive: str = "assert") -> z3.BoolRef | None:
        k = node.kind

        if k == SyntaxKind.ImplicationPropertyExpr:
            ant = self._property_to_z3(node.left, clock, ts, directive)
            cons = self._property_to_z3(node.right, clock, ts, directive)
            if ant is None or cons is None:
                return None
            op_text = str(node.op.rawText) if hasattr(node.op, 'rawText') else "|->"
            if op_text == "|=>":
                cons_next = z3.substitute(
                    cons,
                    *[(ts.get_cur(name), ts.get_next(name)) for name in ts.state_vars]
                )
                tp_expr = z3.Implies(ant, cons_next)
                if directive == "assume":
                    ts.add_assumption(tp_expr)
                else:
                    ts.add_trans_property(f"{directive}_{len(ts.trans_properties)}", tp_expr)
                return None
            else:
                imp_expr = z3.Implies(ant, cons)
                if directive == "assume":
                    ts.add_assumption(imp_expr)
                else:
                    ts.add_property(f"{directive}_{len(ts.properties)}", imp_expr)
                return None

        if k in (SyntaxKind.ParenthesizedPropertyExpr, SyntaxKind.SimplePropertyExpr, SyntaxKind.SimpleSequenceExpr):
            if hasattr(node, 'expr'):
                return self._property_to_z3(node.expr, clock, ts, directive)
            return None

        if k == SyntaxKind.ClockingPropertyExpr:
            if hasattr(node, 'expr'):
                return self._property_to_z3(node.expr, clock, ts, directive)
            return None

        if k == SyntaxKind.ClockingSequenceExpr:
            if hasattr(node, 'expr'):
                return self._property_to_z3(node.expr, clock, ts, directive)
            return None

        if k == SyntaxKind.ParenthesizedSequenceExpr:
            if hasattr(node, 'expr'):
                return self._property_to_z3(node.expr, clock, ts, directive)
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
                        inner = self._property_to_z3(child, clock, ts, directive)
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
                l = self._property_to_z3(children[0], clock, ts, directive)
                r = self._property_to_z3(children[1], clock, ts, directive)
                if l is not None and r is not None:
                    return z3.And(l, r)
            return None

        if k == SyntaxKind.OrSequenceExpr:
            children = [c for c in node if hasattr(c, 'kind') and 'Keyword' not in str(c.kind)]
            if len(children) >= 2:
                l = self._property_to_z3(children[0], clock, ts, directive)
                r = self._property_to_z3(children[1], clock, ts, directive)
                if l is not None and r is not None:
                    return z3.Or(l, r)
            return None

        if k == SyntaxKind.IntersectSequenceExpr:
            children = [c for c in node if hasattr(c, 'kind') and 'Keyword' not in str(c.kind)]
            if len(children) >= 2:
                l = self._property_to_z3(children[0], clock, ts, directive)
                r = self._property_to_z3(children[1], clock, ts, directive)
                if l is not None and r is not None:
                    return z3.And(l, r)
            return None

        if k == SyntaxKind.IffPropertyExpr:
            children = [c for c in node if hasattr(c, 'kind') and 'Keyword' not in str(c.kind)]
            if len(children) >= 2:
                l = self._property_to_z3(children[0], clock, ts, directive)
                r = self._property_to_z3(children[1], clock, ts, directive)
                if l is not None and r is not None:
                    return (l == r)
            return None

        if k == SyntaxKind.SUntilPropertyExpr:
            children = [c for c in node if hasattr(c, 'kind') and 'Keyword' not in str(c.kind)]
            if len(children) >= 2:
                l = self._property_to_z3(children[0], clock, ts, directive)
                r = self._property_to_z3(children[1], clock, ts, directive)
                if l is not None and r is not None:
                    return z3.Or(r, l)
            return None

        if k == SyntaxKind.UntilPropertyExpr:
            children = [c for c in node if hasattr(c, 'kind') and 'Keyword' not in str(c.kind)]
            if len(children) >= 2:
                l = self._property_to_z3(children[0], clock, ts, directive)
                r = self._property_to_z3(children[1], clock, ts, directive)
                if l is not None and r is not None:
                    return z3.Or(r, l)
            return None

        if k == SyntaxKind.SUntilWithPropertyExpr:
            children = [c for c in node if hasattr(c, 'kind') and 'Keyword' not in str(c.kind)]
            if len(children) >= 2:
                l = self._property_to_z3(children[0], clock, ts, directive)
                r = self._property_to_z3(children[1], clock, ts, directive)
                if l is not None and r is not None:
                    return z3.Or(r, l)
            return None

        if k == SyntaxKind.UntilWithPropertyExpr:
            children = [c for c in node if hasattr(c, 'kind') and 'Keyword' not in str(c.kind)]
            if len(children) >= 2:
                l = self._property_to_z3(children[0], clock, ts, directive)
                r = self._property_to_z3(children[1], clock, ts, directive)
                if l is not None and r is not None:
                    return z3.Or(r, l)
            return None

        if k == SyntaxKind.ConditionalPropertyExpr:
            ant = None
            cons = None
            cond = None
            items = [c for c in node if hasattr(c, 'kind') and 'Keyword' not in str(c.kind)]
            if len(items) >= 3:
                cond = self._property_to_z3(items[0], clock, ts, directive)
                ant = self._property_to_z3(items[1], clock, ts, directive)
                cons = self._property_to_z3(items[2], clock, ts, directive)
            elif len(items) >= 2:
                cond = items[0]
                ant = self._property_to_z3(items[0] if cond else items[1], clock, ts, directive)
                cons = self._property_to_z3(items[1] if cond else items[0], clock, ts, directive)
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
                left_expr = self._property_to_z3(left_seq, clock, ts, directive)
                if left_expr is None:
                    return None
                delay_cycles = 1
                right_seq = None
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
                            if delay_left is not None:
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
                right_expr = self._property_to_z3(right_seq, clock, ts, directive)
                if right_expr is None:
                    return None
                if delay_cycles == 0:
                    return z3.And(left_expr, right_expr)
                for _ in range(delay_cycles):
                    right_expr = z3.substitute(
                        right_expr,
                        *[(ts.get_cur(name), ts.get_next(name)) for name in ts.state_vars]
                    )
                return z3.And(left_expr, right_expr)
            return None

        if k == SyntaxKind.SequenceRepetition:
            rep_count = 1
            is_plus = False
            inner_seq = None
            for child in node:
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
                    elif 'SimpleSequence' in ck or 'SimpleProperty' in ck:
                        inner_seq = child
            if inner_seq is None:
                return None
            inner_expr = self._property_to_z3(inner_seq, clock, ts, directive)
            if inner_expr is None:
                return None
            if is_plus:
                return inner_expr
            return inner_expr

        prop_bv = self._node_to_z3(node)
        if prop_bv is not None:
            return (prop_bv != 0)
        return None

    def _expr_width(self, node, ts: TransitionSystem) -> int:
        k = node.kind
        if k == SyntaxKind.IdentifierName:
            name = self._token_text(node.identifier)
            return self._signal_width(name, ts)
        if k == SyntaxKind.IntegerLiteralExpression:
            try:
                val = int(self._token_text(node.literal), 0)
                return max(val.bit_length(), 1)
            except ValueError:
                return 1
        if k == SyntaxKind.IntegerVectorExpression:
            sz = node.size
            try:
                return int(self._token_text(sz), 0)
            except (ValueError, AttributeError):
                return 8
        if k in (SyntaxKind.AddExpression, SyntaxKind.SubtractExpression,
                 SyntaxKind.MultiplyExpression):
            return max(self._expr_width(node.left, ts), self._expr_width(node.right, ts))
        if k in (SyntaxKind.EqualityExpression, SyntaxKind.InequalityExpression,
                 SyntaxKind.LessThanExpression, SyntaxKind.GreaterThanExpression,
                 SyntaxKind.LessThanEqualExpression, SyntaxKind.GreaterThanEqualExpression,
                 SyntaxKind.CaseEqualityExpression, SyntaxKind.CaseInequalityExpression):
            return 1
        if k == SyntaxKind.ConcatenationExpression:
            total = 0
            for op in node.operands:
                total += self._expr_width(op, ts)
            return total
        if k == SyntaxKind.UnaryLogicalNotExpression:
            return self._expr_width(node.operand, ts)
        if k == SyntaxKind.ConditionalExpression:
            return max(self._expr_width(node.left, ts), self._expr_width(node.right, ts))
        if k == SyntaxKind.ParenthesizedExpression:
            return self._expr_width(node.expression, ts)
        if k == SyntaxKind.UnaryBitwiseNotExpression:
            return self._expr_width(node.operand, ts)
        if k == SyntaxKind.SimplePropertyExpr:
            return self._expr_width(node.expr, ts) if hasattr(node, 'expr') else 1
        if k == SyntaxKind.SimpleSequenceExpr:
            return self._expr_width(node.expr, ts) if hasattr(node, 'expr') else 1
        if k in (SyntaxKind.AndSequenceExpr, SyntaxKind.OrSequenceExpr,
                 SyntaxKind.IntersectSequenceExpr):
            return 1
        if k == SyntaxKind.IffPropertyExpr:
            return 1
        if k in (SyntaxKind.SUntilPropertyExpr, SyntaxKind.UntilPropertyExpr,
                 SyntaxKind.SUntilWithPropertyExpr, SyntaxKind.UntilWithPropertyExpr):
            return 1
        if k == SyntaxKind.UnaryPropertyExpr:
            return 1
        if k == SyntaxKind.DelayedSequenceExpr:
            return 1
        if k == SyntaxKind.SequenceRepetition:
            return 1
        if k == SyntaxKind.InvocationExpression:
            if hasattr(node, 'left') and hasattr(node.left, 'systemIdentifier'):
                func_name = node.left.systemIdentifier.valueText
                if func_name in ('$rose', '$fell', '$stable', '$changed'):
                    return 1
                if func_name == '$isunknown':
                    return 1
                if func_name == '$past':
                    args = self._extract_call_args(node)
                    if args:
                        return self._expr_width(args[0], ts)
                    return 1
            return 1
        return 1

    def _node_to_z3(self, node) -> z3.BitVecRef:
        if node is None:
            return z3.BitVecVal(0, 1)
        k = node.kind

        if k == SyntaxKind.IdentifierName:
            name = self._token_text(node.identifier)
            if getattr(self, '_genvar_subst', None) and name in self._genvar_subst:
                val = self._genvar_subst[name]
                if isinstance(val, int):
                    bw = max(val.bit_length(), 1)
                    return z3.BitVecVal(val, bw)
                return z3.BitVecVal(val, 1)
            w = self._signal_width(name, self._current_ts)
            if name in self._current_ts.state_vars:
                return self._current_ts.get_cur(name)
            if name in self._current_ts.inputs:
                return self._current_ts.get_inp(name)
            self._current_ts.add_state_var(name, w)
            return self._current_ts.get_cur(name)

        if k == SyntaxKind.IdentifierSelectName:
            name = self._token_text(node.identifier)
            w = self._signal_width(name, self._current_ts)
            if name in self._current_ts.state_vars:
                base = self._current_ts.get_cur(name)
            elif name in self._current_ts.inputs:
                base = self._current_ts.get_inp(name)
            else:
                self._current_ts.add_state_var(name, w)
                base = self._current_ts.get_cur(name)

            def _zext(expr, target_w):
                ew = expr.size()
                if ew < target_w:
                    return z3.ZeroExt(target_w - ew, expr)
                return expr

            result = base
            array_dims = self._current_ts.get_var_dims(name) if hasattr(self._current_ts, 'get_var_dims') else []
            dim_idx = 0
            for sel in node.selectors:
                if sel.kind == SyntaxKind.ElementSelect:
                    selector = sel.selector
                    sk = selector.kind

                    if sk == SyntaxKind.SimpleRangeSelect:
                        left_val = self._node_to_z3(selector.left)
                        right_val = self._node_to_z3(selector.right)
                        if z3.is_bv_value(left_val) and z3.is_bv_value(right_val):
                            hi = left_val.as_long()
                            lo = right_val.as_long()
                            if lo > hi:
                                lo, hi = hi, lo
                            w_sel = hi - lo + 1
                            if w_sel == w:
                                return result
                            result = z3.Extract(hi, lo, result)
                        else:
                            right_width = self._extract_width_from_node(selector.right)
                            if right_width is None or right_width <= 0:
                                right_width = 1
                            base_z = _zext(result, w + right_width)
                            shift = _zext(left_val, w)
                            result = z3.Extract(right_width - 1, 0, z3.LShR(result, shift))

                    elif sk == SyntaxKind.BitSelect:
                        idx = self._node_to_z3(selector.expr)
                        if dim_idx < len(array_dims):
                            ew = result.size() // array_dims[dim_idx]
                            if z3.is_bv_value(idx):
                                bit = idx.as_long()
                                offset = bit * ew
                                result = z3.Extract(offset + ew - 1, offset, result)
                            else:
                                shift = _zext(idx, result.size())
                                result = z3.Extract(ew - 1, 0, z3.LShR(result, shift * ew))
                            dim_idx += 1
                        else:
                            if z3.is_bv_value(idx):
                                bit = idx.as_long()
                                result = z3.Extract(bit, bit, result)
                            else:
                                shift = _zext(idx, w)
                                result = z3.Extract(0, 0, z3.LShR(result, shift))

                    elif sk == SyntaxKind.AscendingRangeSelect:
                        base_expr = self._node_to_z3(selector.left)
                        width_val = self._node_to_z3(selector.right)
                        sw = width_val.as_long() if z3.is_bv_value(width_val) else 1
                        shift = _zext(base_expr, w)
                        result = z3.Extract(sw - 1, 0, z3.LShR(result, shift))

                    elif sk == SyntaxKind.DescendingRangeSelect:
                        base_expr = self._node_to_z3(selector.left)
                        width_val = self._node_to_z3(selector.right)
                        sw = width_val.as_long() if z3.is_bv_value(width_val) else 1
                        shift = _zext(base_expr - (sw - 1), w)
                        result = z3.Extract(sw - 1, 0, z3.LShR(result, shift))
            return result

        if k == SyntaxKind.IntegerLiteralExpression:
            try:
                val = int(self._token_text(node.literal), 0)
                bw = max(val.bit_length(), 1)
                return z3.BitVecVal(val, bw)
            except ValueError:
                return z3.BitVecVal(0, 1)

        if k == SyntaxKind.IntegerVectorExpression:
            size_str = self._token_text(node.size) if hasattr(node, 'size') else "1"
            val_str = self._token_text(node.value) if hasattr(node, 'value') else "0"
            base_str = self._token_text(node.base) if hasattr(node, 'base') else ""
            try:
                bw = int(size_str, 0)
                base_prefix = base_str.replace("'", "")
                if base_prefix == "h":
                    val = int(val_str, 16)
                elif base_prefix == "d":
                    val = int(val_str, 10)
                elif base_prefix == "b":
                    val = int(val_str, 2)
                elif base_prefix == "o":
                    val = int(val_str, 8)
                else:
                    val = int(val_str, 10)
                return z3.BitVecVal(val, bw)
            except (ValueError, AttributeError):
                return z3.BitVecVal(0, 8)

        if k == SyntaxKind.UnaryLogicalNotExpression:
            op = self._node_to_z3(node.operand)
            return z3.If(op == 0, z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))

        if k == SyntaxKind.UnaryBitwiseNotExpression:
            op = self._node_to_z3(node.operand)
            return ~op

        if k == SyntaxKind.AddExpression:
            l = self._node_to_z3(node.left)
            r = self._node_to_z3(node.right)
            return self._z3_promote(l, r, lambda a, b: a + b)

        if k == SyntaxKind.SubtractExpression:
            l = self._node_to_z3(node.left)
            r = self._node_to_z3(node.right)
            return self._z3_promote(l, r, lambda a, b: a - b)

        if k == SyntaxKind.MultiplyExpression:
            l = self._node_to_z3(node.left)
            r = self._node_to_z3(node.right)
            return self._z3_promote(l, r, lambda a, b: a * b)

        if k in (SyntaxKind.DivideExpression, SyntaxKind.ModExpression):
            l = self._node_to_z3(node.left)
            r = self._node_to_z3(node.right)
            return self._z3_promote(l, r, lambda a, b: z3.UDiv(a, b))

        if k in (SyntaxKind.EqualityExpression, SyntaxKind.CaseEqualityExpression):
            l = self._node_to_z3(node.left)
            r = self._node_to_z3(node.right)
            l, r = self._z3_promote_pair(l, r)
            return z3.If(l == r, z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))

        if k in (SyntaxKind.InequalityExpression, SyntaxKind.CaseInequalityExpression):
            l = self._node_to_z3(node.left)
            r = self._node_to_z3(node.right)
            l, r = self._z3_promote_pair(l, r)
            return z3.If(l != r, z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))

        if k == SyntaxKind.BinaryAndExpression:
            l = self._node_to_z3(node.left)
            r = self._node_to_z3(node.right)
            l, r = self._z3_promote_pair(l, r)
            return l & r

        if k == SyntaxKind.BinaryOrExpression:
            l = self._node_to_z3(node.left)
            r = self._node_to_z3(node.right)
            l, r = self._z3_promote_pair(l, r)
            return l | r

        if k == SyntaxKind.BinaryXorExpression:
            l = self._node_to_z3(node.left)
            r = self._node_to_z3(node.right)
            l, r = self._z3_promote_pair(l, r)
            return l ^ r

        if k == SyntaxKind.LogicalAndExpression:
            l = self._node_to_z3(node.left)
            r = self._node_to_z3(node.right)
            l, r = self._z3_promote_pair(l, r)
            return z3.If(z3.And(l != 0, r != 0), z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))

        if k == SyntaxKind.LogicalOrExpression:
            l = self._node_to_z3(node.left)
            r = self._node_to_z3(node.right)
            l, r = self._z3_promote_pair(l, r)
            return z3.If(z3.Or(l != 0, r != 0), z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))

        if k in (SyntaxKind.LogicalShiftLeftExpression, SyntaxKind.ArithmeticShiftLeftExpression):
            l = self._node_to_z3(node.left)
            r = self._node_to_z3(node.right)
            return l << r

        if k in (SyntaxKind.LogicalShiftRightExpression,):
            l = self._node_to_z3(node.left)
            r = self._node_to_z3(node.right)
            return z3.LShR(l, r)

        if k == SyntaxKind.ArithmeticShiftRightExpression:
            l = self._node_to_z3(node.left)
            r = self._node_to_z3(node.right)
            use_signed = self._is_signed_expr(node.left)
            if use_signed:
                return z3.AShr(l, r)
            return l >> r

        if k == SyntaxKind.GreaterThanExpression:
            l = self._node_to_z3(node.left)
            r = self._node_to_z3(node.right)
            l, r = self._z3_promote_pair(l, r)
            if self._is_signed_expr(node.left) or self._is_signed_expr(node.right):
                return z3.If(_z3_sgt(l, r), z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))
            return z3.If(z3.UGT(l, r), z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))

        if k == SyntaxKind.GreaterThanEqualExpression:
            l = self._node_to_z3(node.left)
            r = self._node_to_z3(node.right)
            l, r = self._z3_promote_pair(l, r)
            if self._is_signed_expr(node.left) or self._is_signed_expr(node.right):
                return z3.If(_z3_sge(l, r), z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))
            return z3.If(z3.UGE(l, r), z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))

        if k == SyntaxKind.LessThanExpression:
            l = self._node_to_z3(node.left)
            r = self._node_to_z3(node.right)
            l, r = self._z3_promote_pair(l, r)
            if self._is_signed_expr(node.left) or self._is_signed_expr(node.right):
                return z3.If(_z3_slt(l, r), z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))
            return z3.If(z3.ULT(l, r), z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))

        if k == SyntaxKind.LessThanEqualExpression:
            l = self._node_to_z3(node.left)
            r = self._node_to_z3(node.right)
            l, r = self._z3_promote_pair(l, r)
            if self._is_signed_expr(node.left) or self._is_signed_expr(node.right):
                return z3.If(_z3_sle(l, r), z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))
            return z3.If(z3.ULE(l, r), z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))

        if k == SyntaxKind.ConditionalExpression:
            pred_group = node.predicate
            cond = self._node_to_z3(pred_group.conditions[0].expr)
            l = self._node_to_z3(node.left)
            r = self._node_to_z3(node.right)
            return self._z3_promote(
                l, r,
                lambda a, b: z3.If(cond != 0, a, b)
            )

        if k == SyntaxKind.ParenthesizedExpression:
            return self._node_to_z3(node.expression)

        if k == SyntaxKind.ConcatenationExpression:
            parts = []
            for child in node.expressions:
                if hasattr(child, 'kind') and 'Token' in str(type(child).__name__):
                    continue
                parts.append(self._node_to_z3(child))
            result = parts[0] if parts else z3.BitVecVal(0, 1)
            for p in parts[1:]:
                result = z3.Concat(result, p)
            return result

        if k == SyntaxKind.MultipleConcatenationExpression:
            count_node = node.expression
            operand = self._node_to_z3(node.concatenation)
            cnt = self._eval_literal(count_node)
            if cnt is not None and cnt > 0:
                parts = [operand] * cnt
                result = parts[0]
                for p in parts[1:]:
                    result = z3.Concat(result, p)
                return result
            return operand

        if k == SyntaxKind.SimplePropertyExpr:
            if hasattr(node, 'expr'):
                return self._node_to_z3(node.expr)
            return z3.BitVecVal(0, 1)

        if k == SyntaxKind.SimpleSequenceExpr:
            if hasattr(node, 'expr'):
                return self._node_to_z3(node.expr)
            return z3.BitVecVal(0, 1)

        if k == SyntaxKind.AndSequenceExpr:
            children = [c for c in node if hasattr(c, 'kind') and 'Keyword' not in str(c.kind)]
            if len(children) >= 2:
                l = self._node_to_z3(children[0])
                r = self._node_to_z3(children[1])
                l, r = self._z3_promote_pair(l, r)
                return z3.If(z3.And(l != 0, r != 0), z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))
            return z3.BitVecVal(0, 1)

        if k == SyntaxKind.OrSequenceExpr:
            children = [c for c in node if hasattr(c, 'kind') and 'Keyword' not in str(c.kind)]
            if len(children) >= 2:
                l = self._node_to_z3(children[0])
                r = self._node_to_z3(children[1])
                l, r = self._z3_promote_pair(l, r)
                return z3.If(z3.Or(l != 0, r != 0), z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))
            return z3.BitVecVal(0, 1)

        if k == SyntaxKind.InvocationExpression:
            if hasattr(node, 'left') and hasattr(node.left, 'systemIdentifier'):
                func_name = node.left.systemIdentifier.valueText
                if func_name.startswith('$'):
                    func_name = func_name[1:]
                args = self._extract_call_args(node)
                return self._process_system_func(func_name, args)
            return z3.BitVecVal(0, 1)

        if k == SyntaxKind.InsideExpression:
            left = self._node_to_z3(node.expr)
            ranges_node = node.ranges
            elements = []
            for child in ranges_node:
                kind = child.kind
                if kind in (TokenKind.OpenBrace, TokenKind.CloseBrace, TokenKind.Comma):
                    continue
                elements.append(child)
            if not elements:
                return z3.BitVecVal(0, 1)
            range_vals = [self._node_to_z3(e) for e in elements]
            return z3.If(
                z3.Or(*[left == rv for rv in range_vals]),
                z3.BitVecVal(1, 1),
                z3.BitVecVal(0, 1)
            )

        if k == SyntaxKind.UnbasedUnsizedLiteralExpression:
            txt = str(node)
            if txt.strip() in ("'0", "'b0", "'B0"):
                return z3.BitVecVal(0, 1)
            if txt.strip() in ("'1", "'b1", "'B1"):
                return z3.BitVecVal(1, 1)
            return z3.BitVecVal(0, 1)

        if k == SyntaxKind.ScopedName:
            return self._node_to_z3(list(node)[0])

        warnings.warn(f"Unhandled expression node: {k}", stacklevel=2)
        return z3.BitVecVal(0, 1)

    def _z3_promote_pair(self, a, b):
        if z3.is_bv(a) and z3.is_bv(b):
            wa, wb = a.size(), b.size()
            if wa == wb:
                return a, b
            elif wa > wb:
                return a, z3.ZeroExt(wa - wb, b)
            else:
                return z3.ZeroExt(wb - wa, a), b
        return a, b

    def _z3_promote(self, a, b, op):
        a, b = self._z3_promote_pair(a, b)
        return op(a, b) if z3.is_bv(a) else b

    def _extract_call_args(self, node) -> list:
        args = []
        if hasattr(node, 'arguments') and node.arguments is not None:
            for p in node.arguments.parameters:
                if hasattr(p, 'expr'):
                    args.append(p.expr)
        return args

    def _unwrap_property_wrapper(self, node):
        while hasattr(node, 'expr') and node.kind in (SyntaxKind.SimplePropertyExpr, SyntaxKind.SimpleSequenceExpr):
            node = node.expr
        return node

    def _process_system_func(self, func_name: str, args: list) -> z3.BitVecRef:
        ts = self._current_ts

        if func_name in ('rose', 'fell', 'stable', 'changed'):
            if not args:
                return z3.BitVecVal(0, 1)
            arg_node = args[0]
            arg_expr = self._node_to_z3(arg_node)
            arg_width = self._expr_width(arg_node, ts)

            reg_name = f"__past_{func_name}_{self._past_counter}"
            self._past_counter += 1
            ts.add_state_var(reg_name, arg_width)
            ts.set_next_state(reg_name, arg_expr)

            past_val = ts.get_cur(reg_name)

            if func_name == 'rose':
                return z3.If(z3.And(arg_expr != 0, past_val == 0),
                             z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))
            elif func_name == 'fell':
                return z3.If(z3.And(arg_expr == 0, past_val != 0),
                             z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))
            elif func_name == 'stable':
                return z3.If(arg_expr == past_val,
                             z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))
            elif func_name == 'changed':
                return z3.If(arg_expr != past_val,
                             z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))
            return z3.BitVecVal(0, 1)

        if func_name == 'isunknown':
            return z3.BitVecVal(0, 1)

        if func_name == 'past':
            if not args:
                return z3.BitVecVal(0, 1)
            arg_node = args[0]
            depth = 1
            if len(args) >= 2:
                depth_node = self._unwrap_property_wrapper(args[1])
                depth_val = self._eval_literal(depth_node)
                if depth_val is not None:
                    depth = max(depth_val, 1)
            arg_expr = self._node_to_z3(arg_node)
            arg_width = self._expr_width(arg_node, ts)

            # Create depth registers forming a shift chain
            reg_names = [f"__past_{func_name}_{self._past_counter}_{i}" for i in range(depth)]
            self._past_counter += 1
            for i, rname in enumerate(reg_names):
                ts.add_state_var(rname, arg_width)
                if i == 0:
                    ts.set_next_state(rname, arg_expr)
                else:
                    ts.set_next_state(rname, ts.get_cur(reg_names[i - 1]))

            return ts.get_cur(reg_names[-1])

        return z3.BitVecVal(0, 1)

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
