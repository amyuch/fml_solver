"""Module flattening for multi-module SystemVerilog designs.

Flattens module hierarchies by inlining submodule instances at the
Z3 constraint level, producing a single TransitionSystem.
"""
import os
import z3
from pyslang.syntax import SyntaxKind
from pyslang.parsing import TokenKind
from .rtl_parser import RTLParser


def _token_text(tok):
    if hasattr(tok, 'valueText'):
        return str(tok.valueText)
    if hasattr(tok, 'rawText'):
        return str(tok.rawText)
    return str(tok).strip()


def _get_identifier_text(node):
    if hasattr(node, 'identifier'):
        return _token_text(node.identifier)
    if hasattr(node, 'rawText') and node.rawText:
        return node.rawText
    if hasattr(node, 'toString') and node.toString:
        return node.toString()
    return str(node)


def _walk_children(node):
    """Safely walk AST children, handling non-iterable nodes."""
    try:
        return list(node)
    except (TypeError, AttributeError):
        return []


def _find_module_in_tree(tree_root, mod_name):
    """Find a module declaration node by name."""
    def walk(node):
        if node.kind == SyntaxKind.ModuleDeclaration:
            if hasattr(node, 'header') and node.header is not None:
                hdr = node.header
                if hasattr(hdr, 'name') and hdr.name is not None:
                    name = _token_text(hdr.name)
                    if name == mod_name:
                        return node
        for child in _walk_children(node):
            result = walk(child)
            if result is not None:
                return result
        return None
    return walk(tree_root)


def _collect_instances(mod_node, parser):
    """Find all submodule instances in a module declaration."""
    instances = []
    for child in _walk_children(mod_node):
        if child.kind == SyntaxKind.HierarchyInstantiation:
            info = _parse_instance(child)
            if info:
                instances.append(info)
    return instances


def _parse_instance(inst_node):
    """Parse a HierarchyInstantiation node.
    Returns (module_type, instance_name, {port_name: expr_node})
    or None.
    """
    children = _walk_children(inst_node)
    if len(children) < 2:
        return None

    # First child is the module type name (Identifier token)
    type_tok = children[0]
    if type_tok.kind != TokenKind.Identifier:
        return None
    mod_type = _token_text(type_tok)

    # Find HierarchicalInstance child
    inst_name = None
    port_map = {}
    for child in children:
        if child.kind == SyntaxKind.HierarchicalInstance:
            for c2 in _walk_children(child):
                if c2.kind == SyntaxKind.InstanceName:
                    inst_name = _get_identifier_text(c2).strip()
                elif c2.kind == SyntaxKind.NamedPortConnection:
                    pname, pexpr = _parse_named_port(c2)
                    if pname:
                        port_map[pname] = pexpr

    if mod_type is None or inst_name is None:
        return None

    return (mod_type, inst_name, port_map)


def _parse_named_port(conn_node):
    """Parse a NamedPortConnection node.
    Returns (port_name, expr_node) or (None, None).
    """
    children = _walk_children(conn_node)
    port_name = None
    expr_node = None
    for child in children:
        kind = child.kind
        if isinstance(kind, SyntaxKind):
            # This is a syntax node (expression), not a token
            expr_node = _unwrap_expr(child)
        elif kind == TokenKind.Identifier and port_name is None:
            port_name = _token_text(child)
    return port_name, expr_node


def _unwrap_expr(node):
    """Unwrap SimplePropertyExpr/SimpleSequenceExpr wrappers to get to the real expression."""
    if node.kind == SyntaxKind.SimplePropertyExpr:
        for c in _walk_children(node):
            return _unwrap_expr(c)
    if node.kind == SyntaxKind.SimpleSequenceExpr:
        for c in _walk_children(node):
            return _unwrap_expr(c)
    return node


def _find_submodule_file(mod_name, search_dirs):
    """Search for a submodule file by module name."""
    for d in search_dirs:
        candidates = _find_sv_files(d, mod_name)
        if candidates:
            return candidates[0]
    return None


def _find_sv_files(directory, mod_name):
    """Find SV files matching a module name in a directory."""
    results = []
    # Check common locations
    for candidate in [
        os.path.join(directory, f"{mod_name}.sv"),
        os.path.join(directory, f"{mod_name}.v"),
    ]:
        if os.path.exists(candidate):
            results.append(candidate)
    if results:
        return results
    # Walk directory
    for root, _dirs, files in os.walk(directory):
        for f in files:
            if f == f"{mod_name}.sv" or f == f"{mod_name}.v":
                results.append(os.path.join(root, f))
    return results


def _find_parent_var(name_str, ts):
    """Find a Z3 variable in the parent TS by signal name."""
    name_str = name_str.strip()
    if name_str in ts.state_vars:
        return ts.get_cur(name_str)
    if name_str in ts.inputs:
        return ts.get_inp(name_str)
    # Check with _inp suffix (input variables are stored as name_inp in the parser)
    if name_str + "_inp" in ts.inputs:
        return ts.get_inp(name_str + "_inp")
    return None


def _z3_rename(expr, name_map):
    """Rename variables in a Z3 expression."""
    if name_map and expr is not None:
        try:
            return z3.substitute(expr, *[(k, v) for k, v in name_map.items()])
        except Exception:
            return expr
    return expr


def _collect_sub_state_vars(ts):
    """Collect submodule state vars and build rename map."""
    rename_map = {}
    result = []
    for name, sv in ts.state_vars.items():
        result.append((name, sv.width, sv.init_val))
        rename_map[ts.get_cur(name)] = None  # placeholder
        if name in ts._next:
            rename_map[ts.get_next(name)] = None
    return result, rename_map


def flatten_and_parse(top_file, top_module=None, search_dirs=None):
    """Parse a multi-module design into a single TransitionSystem.

    Recursively flattens module instantiations starting from top_module.
    If top_module is None, uses the last module in the file.
    """
    if search_dirs is None:
        search_dirs = [os.path.dirname(os.path.abspath(top_file))]

    # Global module cache: module_name -> (ts, ast_node, parser)
    module_cache = {}
    visited_files = set()

    # Parse the top file
    _parse_file_into_cache(top_file, module_cache, visited_files)

    if top_module is None:
        # Use the last module in the top file
        top_module = list(module_cache.keys())[-1]

    if top_module not in module_cache:
        raise ValueError(f"Top module '{top_module}' not found")

    ts = _flatten_from(module_cache[top_module], top_module,
                       search_dirs, visited_files, module_cache)
    return ts


def _parse_file_into_cache(filepath, module_cache, visited_files):
    """Parse a file and add all its modules to the cache."""
    abspath = os.path.abspath(filepath)
    if abspath in visited_files:
        return
    visited_files.add(abspath)

    modules = _parse_all_modules(filepath)
    for name, data in modules.items():
        if name not in module_cache:
            module_cache[name] = data


def _parse_all_modules(filepath):
    """Parse a file and return dict of module_name -> (ts, ast_node, parser)."""
    parser = RTLParser()
    parser.parse_file(filepath)
    modules = {}
    for tree in parser.driver.syntaxTrees:
        root = tree.root
        for member in _walk_children(root):
            if member.kind == SyntaxKind.ModuleDeclaration:
                hdr = member.header
                if hasattr(hdr, 'name') and hdr.name is not None:
                    mod_name = _token_text(hdr.name)
                    # Re-process into TS
                    ts = parser._process_module(member)
                    modules[mod_name] = (ts, member, parser)
    return modules


def _flatten_from(top_data, mod_name, search_dirs, visited_files, module_cache, _processing=None):
    if _processing is None:
        _processing = set()

    if mod_name in _processing:
        return ts

    _processing.add(mod_name)

    # Find instances in this module
    instances = _collect_instances(mod_node, _parser)

    for sub_type, inst_name, port_map in instances:
        if sub_type == mod_name:
            continue

        # Check module cache first
        if sub_type not in module_cache:
            sub_file = _find_submodule_file(sub_type, search_dirs)
            if sub_file is not None:
                _parse_file_into_cache(sub_file, module_cache, visited_files)

        if sub_type not in module_cache:
            continue

        sub_data = module_cache[sub_type]
        sub_ts = _flatten_from(sub_data, sub_type, search_dirs, visited_files, module_cache, _processing)
        if sub_ts is None:
            continue

        _merge_ts(ts, sub_ts, inst_name, port_map, search_dirs)

    _processing.discard(mod_name)
    return ts


def _expr_node_to_constant(node):
    """Extract integer constant value from an expression node.
    Handles IntegerVectorExpression (e.g., 8'd10) and IntegerLiteralExpression.
    Returns int or None.
    """
    if node is None:
        return None
    # Unwrap wrappers
    k = node.kind
    if k in (SyntaxKind.SimplePropertyExpr, SyntaxKind.SimpleSequenceExpr):
        for c in _walk_children(node):
            return _expr_node_to_constant(c)

    if k == SyntaxKind.IntegerVectorExpression:
        children = _walk_children(node)
        # Children: literal, base, literal (e.g., '8', 'd', '10')
        if len(children) >= 3:
            try:
                val = int(_token_text(children[2]), 0)
                return val
            except (ValueError, TypeError, AttributeError):
                pass
        return None

    if k == SyntaxKind.IntegerLiteralExpression:
        for c in _walk_children(node):
            if c.kind == TokenKind.IntegerLiteral:
                try:
                    return int(_token_text(c), 0)
                except (ValueError, TypeError):
                    pass
        return None

    return None


def _signal_name_from_expr(node):
    """Extract a simple signal name from an expression node."""
    if node is None:
        return None
    k = node.kind
    
    # Unwrap wrappers
    if k in (SyntaxKind.SimplePropertyExpr, SyntaxKind.SimpleSequenceExpr):
        for c in _walk_children(node):
            return _signal_name_from_expr(c)
    
    if k == SyntaxKind.IdentifierName:
        for c in _walk_children(node):
            if c.kind == TokenKind.Identifier:
                return _token_text(c)
    
    if k == SyntaxKind.IntegerVectorExpression:
        # e.g., 8'd10 — constant
        return None  # Return None for constants (they get inlined)
    
    if k == SyntaxKind.IntegerLiteralExpression:
        return None  # Constant
    
    # For other expressions, return the toString representation
    if hasattr(node, 'toString') and node.toString:
        return node.toString()
    
    return None


def _merge_ts(parent_ts, sub_ts, inst_name, port_map, search_dirs):
    """Merge a submodule TransitionSystem into the parent.

    All submodule variables get prefixed with inst_name + '_'.
    Port connections become combinational equality constraints.
    """
    prefix = f"{inst_name}_"

    # --- 1. Add prefixed state vars ---
    var_map = {}
    for name, sv in sub_ts.state_vars.items():
        new_name = prefix + name
        if new_name not in parent_ts.state_vars:
            parent_ts.add_state_var(new_name, sv.width, sv.init_val)
        var_map[sub_ts.get_cur(name)] = parent_ts.get_cur(new_name)
        var_map[sub_ts.get_next(name)] = parent_ts.get_next(new_name)

    # --- 2. Map submodule inputs. If connected to a parent signal, alias directly.
    for name, iv in sub_ts.inputs.items():
        if name in port_map:
            # Check if connected to a parent signal
            sn = _signal_name_from_expr(port_map[name])
            if sn is not None:
                if sn in parent_ts.state_vars:
                    var_map[sub_ts.get_inp(name)] = parent_ts.get_cur(sn)
                    continue
                elif sn in parent_ts.inputs:
                    var_map[sub_ts.get_inp(name)] = parent_ts.get_inp(sn)
                    continue
        # Otherwise create a prefixed input
        new_name = prefix + name
        if new_name not in parent_ts.inputs:
            parent_ts.add_input(new_name, iv.width)
        var_map[sub_ts.get_inp(name)] = parent_ts.get_inp(new_name)

    # --- 3. Rename and add transition constraints ---
    for name, expr in sub_ts._next_state_exprs.items():
        new_name = prefix + name
        renamed = _z3_rename(expr, var_map)
        parent_ts.set_next_state(new_name, renamed)

    # --- 4. Rename and add combinational constraints ---
    for c in sub_ts._comb_constraints:
        renamed = _z3_rename(c, var_map)
        parent_ts.add_comb_constraint(renamed)

    # --- 5. Add port connection constraints ---
    for port_name, expr_node in port_map.items():
        if expr_node is None:
            continue

        signal_name = _signal_name_from_expr(expr_node)
        sub_var_name = prefix + port_name
        sub_is_input = port_name in sub_ts.inputs
        sub_is_output = port_name in sub_ts.state_vars

        if sub_is_input:
            # Inputs already aliased in var_map if connected to a parent signal.
            # Only add constraint if connected to a constant.
            if signal_name is None:
                if sub_var_name in parent_ts.inputs:
                    const_val = _expr_node_to_constant(expr_node)
                    if const_val is not None:
                        port_width = sub_ts.inputs[port_name].width
                        parent_ts.add_comb_constraint(
                            parent_ts.get_inp(sub_var_name) == z3.BitVecVal(const_val, port_width)
                        )
            continue

        if sub_is_output:
            # Get or create parent-side Z3 expression
            parent_var = None
            if signal_name is not None:
                if signal_name in parent_ts.state_vars:
                    parent_var = parent_ts.get_cur(signal_name)
                elif signal_name in parent_ts.inputs:
                    parent_var = parent_ts.get_inp(signal_name)

            if parent_var is None and signal_name is not None:
                sv = sub_ts.state_vars.get(port_name)
                if sv:
                    parent_ts.add_state_var(signal_name, sv.width, sv.init_val)
                    parent_var = parent_ts.get_cur(signal_name)

            if parent_var is not None and sub_var_name in parent_ts.state_vars:
                parent_ts.add_comb_constraint(parent_var == parent_ts.get_cur(sub_var_name))

    # --- 6. Add renamed properties ---
    for pname, p_expr in sub_ts.properties:
        renamed = _z3_rename(p_expr, var_map)
        parent_ts.add_property(f"{inst_name}_{pname}", renamed)

    for tpname, tp_expr in sub_ts.trans_properties:
        renamed = _z3_rename(tp_expr, var_map)
        parent_ts.add_trans_property(f"{inst_name}_{tpname}", renamed)
