"""Expression evaluation for RTL parser."""
from pyslang.syntax import SyntaxKind
from ..ir.transition_system import TransitionSystem
import z3


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


def _signal_width(self, name: str, ts: TransitionSystem) -> int:
    if name in ts.state_vars:
        return ts.state_vars[name].width
    if name in ts.inputs:
        return ts.inputs[name].width
    if name in ts.params:
        return ts.params[name][0]
    return 1


def _eval_literal_expr(self, node, ts: TransitionSystem = None) -> int | None:
    if node is None:
        return None
    k = node.kind

    if k == SyntaxKind.IntegerLiteralExpression:
        return self._eval_literal(node.literal)
    if k == SyntaxKind.IntegerVectorExpression:
        val = self._eval_literal(node.value) if hasattr(node, 'value') else None
        return val

    if k == SyntaxKind.UnbasedUnsizedLiteralExpression:
        txt = str(node).strip()
        if txt in ("'0", "'b0", "'B0"):
            return 0
        if txt in ("'1", "'b1", "'B1"):
            return 1
        return 0

    if k == SyntaxKind.IdentifierName:
        name = self._token_text(node.identifier)
        if getattr(self, '_genvar_subst', None) and name in self._genvar_subst:
            return self._genvar_subst[name]
        if ts is not None and name in ts.params:
            return ts.params[name][1]
        return None

    if k == SyntaxKind.InvocationExpression:
        if hasattr(node, 'left') and hasattr(node.left, 'systemIdentifier'):
            func_name = node.left.systemIdentifier.valueText
            if func_name == '$clog2':
                args = self._extract_call_args(node)
                if args and len(args) > 0:
                    arg_val = self._eval_literal_expr(args[0], ts)
                    if arg_val is not None and arg_val > 0:
                        return (arg_val - 1).bit_length()
        return None

    if k in (SyntaxKind.SimplePropertyExpr, SyntaxKind.SimpleSequenceExpr):
        if hasattr(node, 'expr') and node.expr is not None:
            return self._eval_literal_expr(node.expr, ts)
        return None

    if k == SyntaxKind.ParenthesizedExpression:
        return self._eval_literal_expr(node.expression, ts)

    if k == SyntaxKind.ConcatenationExpression:
        ops = node.expressions if hasattr(node, 'expressions') else node.operands
        total = 0
        for op in ops:
            oval = self._eval_literal_expr(op, ts)
            ow = self._expr_width(op, ts)
            if oval is None or ow is None or ow <= 0:
                return None
            total = (total << ow) | (oval & ((1 << ow) - 1))
        return total

    if k == SyntaxKind.MultipleConcatenationExpression:
        count = self._eval_literal_expr(node.expression, ts)
        if count is None or count <= 0:
            return None
        inner_val = self._eval_literal_expr(node.concatenation, ts)
        inner_w = self._expr_width(node.concatenation, ts)
        if inner_val is None or inner_w is None or inner_w <= 0:
            return None
        result = 0
        mask = (1 << inner_w) - 1
        for _ in range(count):
            result = (result << inner_w) | (inner_val & mask)
        return result

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
        if k == SyntaxKind.PowerExpression:
            return left ** right
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


def _expr_width(self, node, ts: TransitionSystem) -> int:
    k = node.kind
    if k == SyntaxKind.IdentifierName:
        name = self._token_text(node.identifier)
        return self._signal_width(name, ts)
    if k == SyntaxKind.IdentifierSelectName:
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
        ops = node.expressions if hasattr(node, 'expressions') else node.operands
        for op in ops:
            total += self._expr_width(op, ts)
        return total
    if k == SyntaxKind.MultipleConcatenationExpression:
        count = self._eval_literal_expr(node.expression, ts)
        inner_w = self._expr_width(node.concatenation, ts)
        if count is not None and count > 0 and inner_w is not None:
            return count * inner_w
        return 1
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


