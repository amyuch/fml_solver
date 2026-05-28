"""Z3 expression construction for RTL parser."""
from pyslang.syntax import SyntaxKind
from pyslang.parsing import TokenKind
import z3
import warnings
from .eval_expr import _eval_literal_expr, _expr_width, _signal_width


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
        genvar_ctx = getattr(self, '_genvar_subst', None) or {}
        for suffix in self._genvar_suffix_prefixes(genvar_ctx):
            lookup = name + suffix
            if lookup in self._current_ts.params:
                pv = self._current_ts.params[lookup][1]
                if pv is not None:
                    bw = self._current_ts.params[lookup][0]
                    return z3.BitVecVal(pv, bw)
                break
        w = self._signal_width(name, self._current_ts)
        if name in self._current_ts.state_vars:
            return self._current_ts.get_cur(name)
        if name in self._current_ts.inputs:
            return self._current_ts.get_inp(name)
        self._current_ts.add_state_var(name, w)
        return self._current_ts.get_cur(name)

    if k == SyntaxKind.IdentifierSelectName:
        name = self._token_text(node.identifier)
        # Check params with known values before creating state var
        genvar_ctx = getattr(self, '_genvar_subst', None) or {}
        param_found = False
        for suffix in self._genvar_suffix_prefixes(genvar_ctx):
            lookup = name + suffix
            if lookup in self._current_ts.params:
                pv = self._current_ts.params[lookup][1]
                if pv is not None:
                    bw = self._current_ts.params[lookup][0]
                    result = z3.BitVecVal(pv, bw)
                    param_dims = self._current_ts.get_param_dims(lookup)
                    dim_idx = 0
                    for sel in node.selectors:
                        if sel.kind == SyntaxKind.ElementSelect:
                            s = sel.selector
                            sk = s.kind
                            if sk == SyntaxKind.BitSelect:
                                if dim_idx < len(param_dims):
                                    ew = bw // param_dims[dim_idx]
                                    idx_expr = self._eval_literal_expr(s.expr, None)
                                    if idx_expr is not None:
                                        offset = idx_expr * ew
                                        result = z3.Extract(offset + ew - 1, offset, result)
                                else:
                                    idx_expr = self._eval_literal_expr(s.expr, None)
                                    if idx_expr is not None and 0 <= idx_expr < bw:
                                        result = z3.Extract(idx_expr, idx_expr, result)
                            elif sk == SyntaxKind.SimpleRangeSelect:
                                hi = self._eval_literal_expr(s.left, None)
                                lo = self._eval_literal_expr(s.right, None)
                                if hi is not None and lo is not None:
                                    if lo > hi: lo, hi = hi, lo
                                    if 0 <= lo <= hi < bw:
                                        result = z3.Extract(hi, lo, result)
                            dim_idx += 1
                    return result
                param_found = True
                break
        if not param_found:
            # Check unsuffixed name too
            if name in self._current_ts.params and self._current_ts.params[name][1] is not None:
                bw = self._current_ts.params[name][0]
                result = z3.BitVecVal(self._current_ts.params[name][1], bw)
                param_dims = self._current_ts.get_param_dims(name)
                dim_idx = 0
                for sel in node.selectors:
                    if sel.kind == SyntaxKind.ElementSelect:
                        s = sel.selector
                        sk = s.kind
                        if sk == SyntaxKind.BitSelect:
                            if dim_idx < len(param_dims):
                                ew = bw // param_dims[dim_idx]
                                idx_expr = self._eval_literal_expr(s.expr, None)
                                if idx_expr is not None:
                                    offset = idx_expr * ew
                                    result = z3.Extract(offset + ew - 1, offset, result)
                            else:
                                idx_expr = self._eval_literal_expr(s.expr, None)
                                if idx_expr is not None and 0 <= idx_expr < bw:
                                    result = z3.Extract(idx_expr, idx_expr, result)
                        elif sk == SyntaxKind.SimpleRangeSelect:
                            hi = self._eval_literal_expr(s.left, None)
                            lo = self._eval_literal_expr(s.right, None)
                            if hi is not None and lo is not None:
                                if lo > hi: lo, hi = hi, lo
                                if 0 <= lo <= hi < bw:
                                    result = z3.Extract(hi, lo, result)
                        dim_idx += 1
                return result
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
                        if hi >= result.size():
                            result = _zext(result, hi + 1)
                        if w_sel == w:
                            return result
                        result = z3.Extract(hi, lo, result)
                    else:
                        right_width = self._extract_width_from_node(selector.right)
                        if right_width is None or right_width <= 0:
                            right_width = 1
                        max_w = max(result.size(), w + right_width, left_val.size(), w)
                        base_z = _zext(result, max_w)
                        shift = _zext(left_val, max_w)
                        result = z3.Extract(right_width - 1, 0, z3.LShR(base_z, shift))

                elif sk == SyntaxKind.BitSelect:
                    idx = self._node_to_z3(selector.expr)
                    if dim_idx < len(array_dims):
                        ew = result.size() // array_dims[dim_idx]
                        if z3.is_bv_value(idx):
                            bit = idx.as_long()
                            offset = bit * ew
                            if offset + ew > result.size():
                                result = _zext(result, offset + ew)
                            result = z3.Extract(offset + ew - 1, offset, result)
                        else:
                            shift_w = max(result.size(), idx.size())
                            result_z = _zext(result, shift_w)
                            shift = _zext(idx, shift_w)
                            scaled = shift * ew if isinstance(ew, int) else shift
                            result = z3.Extract(ew - 1, 0, z3.LShR(result_z, scaled))
                        dim_idx += 1
                    else:
                        if z3.is_bv_value(idx):
                            bit = idx.as_long()
                            if bit >= result.size():
                                result = _zext(result, bit + 1)
                            result = z3.Extract(bit, bit, result)
                        else:
                            lshr_w = max(result.size(), idx.size())
                            result_z = _zext(result, lshr_w)
                            shift = _zext(idx, lshr_w)
                            result = z3.Extract(0, 0, z3.LShR(result_z, shift))

                elif sk == SyntaxKind.AscendingRangeSelect:
                    base_expr = self._node_to_z3(selector.left)
                    width_val = self._node_to_z3(selector.right)
                    sw = width_val.as_long() if z3.is_bv_value(width_val) else 1
                    if sw <= 0:
                        sw = 1
                    lshr_w = max(result.size(), base_expr.size())
                    shift = _zext(base_expr, lshr_w)
                    result = z3.Extract(sw - 1, 0, z3.LShR(_zext(result, lshr_w), shift))

                elif sk == SyntaxKind.DescendingRangeSelect:
                    base_expr = self._node_to_z3(selector.left)
                    width_val = self._node_to_z3(selector.right)
                    sw = width_val.as_long() if z3.is_bv_value(width_val) else 1
                    if sw <= 0:
                        sw = 1
                    adjusted = base_expr - (sw - 1)
                    lshr_w = max(result.size(), adjusted.size())
                    shift = _zext(adjusted, lshr_w)
                    result = z3.Extract(sw - 1, 0, z3.LShR(_zext(result, lshr_w), shift))
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

    if k == SyntaxKind.UnaryBitwiseOrExpression:
        op = self._node_to_z3(node.operand)
        bits = [z3.Extract(i, i, op) for i in range(op.size())]
        return z3.If(z3.Or(*[b != 0 for b in bits]),
                     z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))

    if k == SyntaxKind.UnaryBitwiseAndExpression:
        op = self._node_to_z3(node.operand)
        bits = [z3.Extract(i, i, op) for i in range(op.size())]
        return z3.If(z3.And(*[b != 0 for b in bits]),
                     z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))

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
        l, r = self._z3_promote_pair(l, r)
        return l << r

    if k in (SyntaxKind.LogicalShiftRightExpression,):
        l = self._node_to_z3(node.left)
        r = self._node_to_z3(node.right)
        l, r = self._z3_promote_pair(l, r)
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

    if k == SyntaxKind.CastExpression:
        result = self._node_to_z3(node.right)
        lw = self._expr_width(node, self._current_ts)
        if lw is not None and result.size() < lw:
            result = z3.ZeroExt(lw - result.size(), result)
        elif lw is not None and result.size() > lw:
            result = z3.Extract(lw - 1, 0, result)
        return result

    if k == SyntaxKind.UnaryBitwiseXorExpression:
        op = self._node_to_z3(node.operand)
        xor_result = z3.BitVecVal(0, 1)
        for i in range(op.size()):
            xor_result = xor_result ^ z3.Extract(i, i, op)
        return z3.ZeroExt(0, xor_result)

    if k == SyntaxKind.PostincrementExpression:
        return self._node_to_z3(node.operand) + 1

    if k == SyntaxKind.PostdecrementExpression:
        return self._node_to_z3(node.operand) - 1

    if k == SyntaxKind.LogicalImplicationExpression:
        l = self._node_to_z3(node.left)
        r = self._node_to_z3(node.right)
        l, r = self._z3_promote_pair(l, r)
        return z3.If(z3.Or(l == 0, r != 0), z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))

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
        if arg_expr.size() != arg_width:
            if arg_expr.size() < arg_width:
                arg_expr = z3.ZeroExt(arg_width - arg_expr.size(), arg_expr)
            else:
                arg_expr = z3.Extract(arg_width - 1, 0, arg_expr)
        ts.set_next_state(reg_name, arg_expr)

        past_val = ts.get_cur(reg_name)

        aw = arg_expr.size()
        pw = past_val.size()
        if aw != pw:
            if aw > pw:
                past_val = z3.ZeroExt(aw - pw, past_val)
            else:
                arg_expr = z3.ZeroExt(pw - aw, arg_expr)

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
        return z3.BitVecVal(1, 1)

    if func_name in ('onehot0', 'onehot'):
        if not args:
            return z3.BitVecVal(0, 1)
        arg_expr = self._node_to_z3(args[0])
        minus1 = arg_expr - 1
        no_overlap = (arg_expr & minus1) == 0
        if func_name == 'onehot0':
            return z3.If(z3.Or(no_overlap, arg_expr == 0),
                         z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))
        else:
            return z3.If(z3.And(no_overlap, arg_expr != 0),
                         z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))

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


