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
    return None
