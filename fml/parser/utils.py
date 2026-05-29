"""Utility functions for RTL parser."""


def _token_text(tok) -> str:
    txt = str(tok).strip()
    # Remove leading comment trivia (pyslang attaches comments to the next token)
    if '//' in txt or '\n' in txt:
        lines = txt.split('\n')
        for line in reversed(lines):
            line = line.strip()
            if line and not line.startswith('//'):
                return line
    return txt


def _eval_literal(node) -> int | None:
    try:
        return int(_token_text(node), 0)
    except (ValueError, AttributeError, TypeError):
        return None


def _extract_name(node) -> str | None:
    if hasattr(node, 'kind') and 'IdentifierName' in str(node.kind):
        return _token_text(node.identifier)
    if hasattr(node, 'kind') and 'IdentifierSelectName' in str(node.kind):
        return _token_text(node.identifier)
    if hasattr(node, 'kind') and 'ScopedName' in str(node.kind):
        if hasattr(node, 'left') and hasattr(node, 'right'):
            left = node.left
            right = node.right
            if hasattr(left, 'kind') and 'IdentifierName' in str(left.kind):
                base = _token_text(left.identifier)
                if hasattr(right, 'identifier'):
                    sig = _token_text(right.identifier)
                    return f"{base}_{sig}"
    return None


def _dim_pos_for_selector(sel_idx: int, num_packed: int, total_dims: int) -> int:
    """Map selector index to dimension position in full_dims.
    
    full_dims = [packed_dims..., unpacked_dims...].
    
    Selectors L-to-R: first select from unpacked (outer), then from packed (inner).
    The LAST dims in full_dims are unpacked; the FIRST are packed.
    
    For sel_idx < num_unpacked: dim_pos = total - 1 - sel_idx (right-to-left through unpacked)
    For sel_idx >= num_unpacked: dim_pos = sel_idx - num_unpacked (left-to-right through packed)
    """
    num_unpacked = total_dims - num_packed
    if sel_idx < num_unpacked:
        return total_dims - 1 - sel_idx
    else:
        return sel_idx - num_unpacked
