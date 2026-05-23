import z3
from pyslang.driver import Driver
from pyslang.syntax import SyntaxKind
from pyslang.parsing import TokenKind
from ..ir.transition_system import TransitionSystem


class RTLParser:
    def __init__(self):
        self.driver = Driver()
        self.driver.addStandardArgs()
        self._past_counter = 0

    def parse_file(self, filepath: str) -> list[TransitionSystem]:
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
        self._extract_ports(header, ts)
        self._extract_body(mod_node, ts)
        return ts

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
            if direction == "input":
                ts.add_input(name, width)
            elif direction == "output":
                ts.add_state_var(name, width)

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

    def _extract_width_from_node(self, node) -> int | None:
        if node.kind == SyntaxKind.ImplicitType:
            return None
        if hasattr(node, 'dimensions') and node.dimensions:
            for dim in node.dimensions:
                w = self._dimension_width(dim)
                if w is not None and w > 1:
                    return w
        return None

    def _dimension_width(self, dim) -> int:
        if not hasattr(dim, 'specifier'):
            return 1
        spec = dim.specifier
        if not hasattr(spec, 'selector'):
            return 1
        sel = spec.selector
        if hasattr(sel, 'left') and hasattr(sel, 'right'):
            lo = self._eval_literal(sel.left)
            ro = self._eval_literal(sel.right)
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

    def _process_data_declaration(self, node, ts: TransitionSystem):
        w = self._extract_width_from_node(node.type)
        if w is None or w <= 0:
            w = 1
        for decl in node.declarators:
            name = self._token_text(decl.name)
            if name not in ts.state_vars and name not in ts.inputs:
                ts.add_state_var(name, w)

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
                        new_result[t] = z3.If(cond, clause_dict[t], prev)
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
        if stmt.kind == SyntaxKind.SequentialBlockStatement:
            for item in stmt.items:
                self._process_comb_item(item, ts)
        else:
            self._process_comb_stmt(stmt, ts)
        self._comb_mode = False

    def _process_comb_item(self, stmt, ts):
        k = stmt.kind
        if k == SyntaxKind.ExpressionStatement:
            self._process_expr_stmt(stmt, ts)
        elif k == SyntaxKind.ConditionalStatement:
            result = self._stmt_next_conditional(stmt, ts)
            for target, expr in result.items():
                ts.add_comb_constraint(ts.get_cur(target) == expr)
        elif k == SyntaxKind.SequentialBlockStatement:
            for item in stmt.items:
                self._process_comb_item(item, ts)

    def _process_comb_stmt(self, stmt, ts):
        k = stmt.kind
        if k == SyntaxKind.ConditionalStatement:
            result = self._stmt_next_conditional(stmt, ts)
            for target, expr in result.items():
                ts.add_comb_constraint(ts.get_cur(target) == expr)
        elif k == SyntaxKind.ExpressionStatement:
            self._process_expr_stmt(stmt, ts)

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
                ts.add_comb_constraint(ts.get_cur(lname) == r_expr)

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
            result = self._property_to_z3(ps.expr, clock, ts)
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

    def _property_to_z3(self, node, clock: str | None, ts: TransitionSystem) -> z3.BoolRef | None:
        k = node.kind

        if k == SyntaxKind.ImplicationPropertyExpr:
            ant = self._property_to_z3(node.left, clock, ts)
            cons = self._property_to_z3(node.right, clock, ts)
            if ant is None or cons is None:
                return None
            op_text = str(node.op.rawText) if hasattr(node.op, 'rawText') else "|->"
            if op_text == "|=>":
                cons_next = z3.substitute(
                    cons,
                    *[(ts.get_cur(name), ts.get_next(name)) for name in ts.state_vars]
                )
                tp_expr = z3.Implies(ant, cons_next)
                ts.add_trans_property(f"assert_{len(ts.trans_properties)}", tp_expr)
                return None
            else:
                ts.add_property(f"assert_{len(ts.properties)}", z3.Implies(ant, cons))
                return None

        if k == SyntaxKind.SimplePropertyExpr:
            if hasattr(node, 'expr'):
                return self._property_to_z3(node.expr, clock, ts)
            return None

        if k == SyntaxKind.SimpleSequenceExpr:
            if hasattr(node, 'expr'):
                return self._property_to_z3(node.expr, clock, ts)
            return None

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
        if k == SyntaxKind.InvocationExpression:
            if hasattr(node, 'left') and hasattr(node.left, 'systemIdentifier'):
                func_name = node.left.systemIdentifier.valueText
                if func_name in ('$rose', '$fell', '$stable'):
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

            result = base
            for sel in node.selectors:
                if sel.kind == SyntaxKind.ElementSelect:
                    selector = sel.selector
                    if selector.kind == SyntaxKind.SimpleRangeSelect:
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
                    elif selector.kind == SyntaxKind.BitSelect:
                        idx = self._node_to_z3(selector.expr)
                        if z3.is_bv_value(idx):
                            bit = idx.as_long()
                            result = z3.Extract(bit, bit, result)
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
            return l >> r

        if k == SyntaxKind.GreaterThanExpression:
            l = self._node_to_z3(node.left)
            r = self._node_to_z3(node.right)
            l, r = self._z3_promote_pair(l, r)
            return z3.If(z3.UGT(l, r), z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))

        if k == SyntaxKind.GreaterThanEqualExpression:
            l = self._node_to_z3(node.left)
            r = self._node_to_z3(node.right)
            l, r = self._z3_promote_pair(l, r)
            return z3.If(z3.UGE(l, r), z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))

        if k == SyntaxKind.LessThanExpression:
            l = self._node_to_z3(node.left)
            r = self._node_to_z3(node.right)
            l, r = self._z3_promote_pair(l, r)
            return z3.If(z3.ULT(l, r), z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))

        if k == SyntaxKind.LessThanEqualExpression:
            l = self._node_to_z3(node.left)
            r = self._node_to_z3(node.right)
            l, r = self._z3_promote_pair(l, r)
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
            parts = [self._node_to_z3(op) for op in node.operands]
            result = parts[0] if parts else z3.BitVecVal(0, 1)
            for p in parts[1:]:
                result = z3.Concat(result, p)
            return result

        if k == SyntaxKind.MultipleConcatenationExpression:
            count_node = node.count
            operand = self._node_to_z3(node.operand)
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

        if k == SyntaxKind.InvocationExpression:
            if hasattr(node, 'left') and hasattr(node.left, 'systemIdentifier'):
                func_name = node.left.systemIdentifier.valueText
                if func_name.startswith('$'):
                    func_name = func_name[1:]
                args = self._extract_call_args(node)
                return self._process_system_func(func_name, args)
            return z3.BitVecVal(0, 1)

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

        if func_name in ('rose', 'fell', 'stable'):
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

    def parse_to_ts(self, filepath: str) -> TransitionSystem:
        systems = self.parse_file(filepath)
        if not systems:
            raise RuntimeError("No modules found")
        return systems[0]

    def parse_text_to_ts(self, text: str) -> TransitionSystem:
        systems = self.parse_text(text)
        if not systems:
            raise RuntimeError("No modules found")
        return systems[0]
