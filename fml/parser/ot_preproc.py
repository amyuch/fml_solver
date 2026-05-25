"""OpenTitan prim_assert macro preprocessor (proper paren-matching)."""

import re
import os


DEFAULT_CLK = "clk_i"
DEFAULT_RST = "!rst_ni"


def _find_matching_paren(text, start):
    """Find the matching ) for the ( at position start."""
    depth = 0
    i = start
    while i < len(text):
        if text[i] == '(':
            depth += 1
        elif text[i] == ')':
            depth -= 1
            if depth == 0:
                return i
        elif text[i] == '"' or text[i] == "'":
            # Skip string literals
            quote = text[i]
            i += 1
            while i < len(text) and text[i] != quote:
                if text[i] == '\\':
                    i += 1
                i += 1
        i += 1
    return -1


def _split_macro_args(s):
    """Split macro args respecting nested parens/braces/brackets and commas."""
    args = []
    depth_paren = 0
    depth_brace = 0
    depth_brack = 0
    current = []
    in_str = False
    str_char = None
    i = 0
    while i < len(s):
        c = s[i]
        if in_str:
            if c == '\\' and i + 1 < len(s):
                current.append(s[i:i+2])
                i += 2
                continue
            if c == str_char:
                in_str = False
            current.append(c)
        elif c in ('"', "'"):
            in_str = True
            str_char = c
            current.append(c)
        elif c == '(':
            depth_paren += 1
            current.append(c)
        elif c == ')':
            depth_paren -= 1
            current.append(c)
        elif c == '{':
            depth_brace += 1
            current.append(c)
        elif c == '}':
            depth_brace -= 1
            current.append(c)
        elif c == '[':
            depth_brack += 1
            current.append(c)
        elif c == ']':
            depth_brack -= 1
            current.append(c)
        elif c == ',' and depth_paren == 0 and depth_brace == 0 and depth_brack == 0:
            args.append(''.join(current).strip())
            current = []
        else:
            current.append(c)
        i += 1
    args.append(''.join(current).strip())
    return args


def _expand_assert(text, start):
    """Expand `ASSERT(name, prop, clk, rst)"""
    end = _find_matching_paren(text, start)
    args = _split_macro_args(text[start+1:end])
    name = args[0]
    prop = args[1]
    clk = args[2] if len(args) > 2 else DEFAULT_CLK
    rst = args[3] if len(args) > 3 else DEFAULT_RST
    return f'{name}: assert property (@(posedge {clk}) disable iff (({rst}) !== \'0) ({prop}));', end + 1


def _expand_assume(text, start):
    """Expand `ASSUME(name, prop, clk, rst)"""
    end = _find_matching_paren(text, start)
    args = _split_macro_args(text[start+1:end])
    name = args[0]
    prop = args[1]
    clk = args[2] if len(args) > 2 else DEFAULT_CLK
    rst = args[3] if len(args) > 3 else DEFAULT_RST
    return f'{name}: assume property (@(posedge {clk}) disable iff (({rst}) !== \'0) ({prop}));', end + 1


def _expand_cover(text, start):
    """Expand `COVER(name, prop, clk, rst)"""
    end = _find_matching_paren(text, start)
    args = _split_macro_args(text[start+1:end])
    name = args[0]
    prop = args[1]
    clk = args[2] if len(args) > 2 else DEFAULT_CLK
    rst = args[3] if len(args) > 3 else DEFAULT_RST
    return f'{name}: cover property (@(posedge {clk}) disable iff (({rst}) !== \'0) ({prop}));', end + 1


def _expand_assert_known_if(text, start):
    """`ASSERT_KNOWN_IF(name, sig, en, clk, rst) → drop"""
    end = _find_matching_paren(text, start)
    return '', end + 1


def _expand_assert_known(text, start):
    """`ASSERT_KNOWN(name, sig, clk, rst) → drop ($isunknown stripped)"""
    end = _find_matching_paren(text, start)
    return '', end + 1


def _expand_assert_if(text, start):
    """`ASSERT_IF(name, prop, en, clk, rst)"""
    end = _find_matching_paren(text, start)
    args = _split_macro_args(text[start+1:end])
    name, prop, en = args[0], args[1], args[2]
    clk = args[3] if len(args) > 3 else DEFAULT_CLK
    rst = args[4] if len(args) > 4 else DEFAULT_RST
    return f'{name}: assert property (@(posedge {clk}) disable iff (({rst}) !== \'0) ({en} |-> {prop}));', end + 1


def _expand_assert_never(text, start):
    """`ASSERT_NEVER(name, prop, clk, rst)"""
    end = _find_matching_paren(text, start)
    args = _split_macro_args(text[start+1:end])
    name, prop = args[0], args[1]
    clk = args[2] if len(args) > 2 else DEFAULT_CLK
    rst = args[3] if len(args) > 3 else DEFAULT_RST
    return f'{name}: assert property (@(posedge {clk}) disable iff (({rst}) !== \'0) not ({prop}));', end + 1


def _expand_assert_pulse(text, start):
    """`ASSERT_PULSE(name, sig, clk, rst)"""
    end = _find_matching_paren(text, start)
    args = _split_macro_args(text[start+1:end])
    name, sig = args[0], args[1]
    clk = args[2] if len(args) > 2 else DEFAULT_CLK
    rst = args[3] if len(args) > 3 else DEFAULT_RST
    return f'{name}: assert property (@(posedge {clk}) disable iff (({rst}) !== \'0) ($rose({sig}) |=> !({sig})));', end + 1


def _expand_assert_init(text, start):
    """`ASSERT_INIT(name, prop) → ignore for formal"""
    end = _find_matching_paren(text, start)
    return '', end + 1


def _expand_assert_static_lint(text, start):
    """`ASSERT_STATIC_LINT_ERROR(name, prop) → ignore"""
    end = _find_matching_paren(text, start)
    return '', end + 1


def _expand_assert_at_reset(text, start):
    """`ASSERT_AT_RESET(name, prop, rst) and `ASSERT_AT_RESET_AND_FINAL"""
    end = _find_matching_paren(text, start)
    return '', end + 1


HANDLERS = {
    'ASSERT': _expand_assert,
    'ASSERT_KNOWN': _expand_assert_known,
    'ASSERT_KNOWN_IF': _expand_assert_known_if,
    'ASSERT_IF': _expand_assert_if,
    'ASSERT_NEVER': _expand_assert_never,
    'ASSERT_PULSE': _expand_assert_pulse,
    'ASSERT_INIT': _expand_assert_init,
    'ASSERT_INIT_NET': _expand_assert_init,
    'ASSERT_FINAL': _expand_assert_init,
    'ASSERT_STATIC_LINT_ERROR': _expand_assert_static_lint,
    'ASSERT_AT_RESET': _expand_assert_at_reset,
    'ASSERT_AT_RESET_AND_FINAL': _expand_assert_at_reset,
    'ASSERT_ERROR': _expand_assert_init,
    'ASSUME': _expand_assume,
    'COVER': _expand_cover,
}


def _strip_ifdef_blocks(text):
    """Strip `ifdef/`ifndef FPV_ON blocks, keeping the FPV path.
    Also strip other `ifdef blocks that contain only macro definitions.
    """
    lines = text.split('\n')
    result = []
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()

        if stripped.startswith('`ifdef FPV_ON'):
            depth = 1
            i += 1
            while i < len(lines) and depth > 0:
                s = lines[i].strip()
                if s.startswith('`ifdef') or s.startswith('`ifndef'):
                    depth += 1
                elif s.startswith('`endif'):
                    depth -= 1
                elif s.startswith('`else') and depth == 1:
                    # Skip else branch
                    i += 1
                    else_depth = 1
                    while i < len(lines) and else_depth > 0:
                        s2 = lines[i].strip()
                        if s2.startswith('`ifdef') or s2.startswith('`ifndef'):
                            else_depth += 1
                        elif s2.startswith('`endif'):
                            else_depth -= 1
                        i += 1
                    break
                if depth > 0:
                    result.append(lines[i])
                    i += 1
            continue

        elif stripped.startswith('`ifndef FPV_ON'):
            depth = 1
            i += 1
            found_else = False
            while i < len(lines) and depth > 0:
                s = lines[i].strip()
                if s.startswith('`ifdef') or s.startswith('`ifndef'):
                    depth += 1
                elif s.startswith('`endif'):
                    depth -= 1
                elif s.startswith('`else') and depth == 1:
                    found_else = True
                    i += 1
                    break
                i += 1
            if found_else:
                else_depth = 1
                while i < len(lines) and else_depth > 0:
                    s2 = lines[i].strip()
                    if s2.startswith('`ifdef') or s2.startswith('`ifndef'):
                        else_depth += 1
                    elif s2.startswith('`endif'):
                        else_depth -= 1
                    if else_depth > 0:
                        result.append(lines[i])
                    i += 1
            continue

        elif (stripped.startswith('`ifdef') or stripped.startswith('`ifndef') or
              stripped.startswith('`else') or stripped.startswith('`endif')):
            i += 1
            continue

        result.append(line)
        i += 1
    return '\n'.join(result)


def preprocess(text: str) -> str:
    """Preprocess OpenTitan RTL text, expanding prim_assert macros to SVA."""

    text = _strip_ifdef_blocks(text)

    # Remove `include and `define lines for prim_assert
    text = re.sub(r'`include\s+["<]prim_assert[^>]*?[>"]\s*\n?', '', text)
    text = re.sub(r'`include\s+["<]prim_macros[^>]*?[>"]\s*\n?', '', text)
    text = re.sub(r'`include\s+["<]prim_assert_sec_cm[^>]*?[>"]\s*\n?', '', text)
    text = re.sub(r'`include\s+["<]prim_flop_macros[^>]*?[>"]\s*\n?', '', text)

    # Remove `define lines
    for kw in ['ASSERT', 'COVER', 'ASSUME', 'PRIM_STRINGIFY', 'ASSERT_ERROR',
               'ASSERT_DEFAULT_CLK', 'ASSERT_DEFAULT_RST']:
        text = re.sub(r'`define\s+' + kw + r'\b.*?\n', '', text)

    # Replace $isunknown with 1'b1
    text = re.sub(r'\$isunknown\s*\([^)]*\)', "1'b1", text)
    text = re.sub(r'\$stable\s*\([^)]*\)', "1'b0", text)

    # Scan for `MACRO(...) calls and expand them
    result = []
    i = 0
    while i < len(text):
        if text[i] == '`':
            # Check for macro name
            rest = text[i+1:]
            m = re.match(r'(ASSERT_\w+|ASSERT|COVER|ASSUME)\b', rest)
            if m:
                macro_name = m.group(1)
                after_name = text[i + 1 + m.end():].lstrip()
                if after_name and after_name[0] == '(':
                    paren_start = i + 1 + m.end() + (len(after_name) - len(after_name.lstrip()))
                    handler = HANDLERS.get(macro_name)
                    if handler:
                        expanded, next_pos = handler(text, paren_start)
                        result.append(expanded)
                        i = next_pos
                        continue
                    else:
                        # Unknown macro: skip it
                        end = _find_matching_paren(text, paren_start)
                        result.append(text[i:end+1])
                        i = end + 1
                        continue
            # Not a recognized macro, pass through
            result.append(text[i])
            i += 1
        else:
            result.append(text[i])
            i += 1

    return ''.join(result)


def preprocess_file(path: str) -> str:
    with open(path, 'r') as f:
        text = f.read()
    return preprocess(text)


if __name__ == '__main__':
    import sys
    for path in sys.argv[1:]:
        if os.path.isfile(path):
            print(f"=== {os.path.basename(path)} ===")
            result = preprocess_file(path)
            n_assert = result.count('assert property')
            n_assert_tot = result.count('assert ')
            non_comment = re.sub(r'//.*', '', result)
            # Count original macro calls (many might be in comments)
            print(f"  expanded to {n_assert} SVA assertions")
            print(f"  file size: {len(result)} chars")
            for line in result.split('\n'):
                if 'assert property' in line and '//' not in line.split('assert')[0]:
                    cleaned = line.strip()[:130]
                    print(f"    {cleaned}")
