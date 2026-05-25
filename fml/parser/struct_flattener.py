"""Struct flattener — replaces packed struct ports with flat logic ports.

Usage:
    from fml.parser.struct_flattener import flatten_module
    flat_text = flatten_module(module_text, module_path, ot_search_paths)
"""

import os
import re
from pyslang.syntax import SyntaxKind
from pyslang.driver import Driver
from .package_resolver import resolve_package_file, extract_types_from_package, StructType


def _find_imports(text: str) -> list[str]:
    """Extract package import names from module text."""
    imports = []
    for m in re.finditer(r'import\s+(\w+)::', text):
        imports.append(m.group(1))
    return imports


def _resolve_package_types(imports: list[str], search_paths: list[str]) -> dict:
    """Resolve all imported packages and return known_types dict."""
    known_types = {}
    for imp in imports:
        pkg_path = resolve_package_file(imp, search_paths)
        if pkg_path:
            pkg_types = extract_types_from_package(pkg_path)
            known_types.update(pkg_types)
        else:
            # Try to find the package file by name convention
            for sp in search_paths:
                candidates = [
                    os.path.join(sp, f"{imp}.sv"),
                    os.path.join(sp, f"{imp}.svh"),
                    os.path.join(sp, "..", "prim", "rtl", f"{imp}.sv"),
                ]
                for cand in candidates:
                    cand = os.path.normpath(cand)
                    if os.path.isfile(cand):
                        pkg_types = extract_types_from_package(cand)
                        known_types.update(pkg_types)
                        break
    return known_types


def flatten_module(text: str, module_path: str = "",
                   ot_search_paths: list[str] = None,
                   struct_types: dict = None) -> str:
    """Flatten packed struct ports in a SystemVerilog module.

    Args:
        text: Module source text.
        module_path: Path to the module file (for resolving includes).
        ot_search_paths: Directories to search for package files.
        struct_types: Pre-resolved struct types (if None, auto-resolve).

    Returns:
        Flattened RTL text with struct ports replaced by flat logic ports.
    """
    if struct_types is None:
        imports = _find_imports(text)
        search_paths = ot_search_paths or _default_search_paths(module_path)
        known_types = _resolve_package_types(imports, search_paths)
    else:
        known_types = struct_types

    if not known_types:
        return text  # No struct types found, return as-is

    # Parse with pyslang to find struct ports and member accesses
    import tempfile
    tmp = tempfile.NamedTemporaryFile(mode='w', suffix='.sv', delete=False)
    tmp.write(text)
    tmp.close()

    d = Driver()
    d.addStandardArgs()
    d.parseCommandLine(f"parse {tmp.name}")
    d.processOptions()
    ok = d.parseAllSources()
    os.unlink(tmp.name)

    if not ok or not d.syntaxTrees:
        return text

    # Collect replacements: (start_offset, end_offset, new_text)
    replacements = []

    for tree in d.syntaxTrees:
        root = tree.root
        for member in root.members:
            if hasattr(member, 'kind') and member.kind == SyntaxKind.ModuleDeclaration:
                _process_module(member, known_types, replacements)

    # Apply replacements in reverse order
    if not replacements:
        return text

    text_bytes = bytearray(text.encode('utf-8'))
    for start, end, new_text in sorted(replacements, key=lambda x: -x[0]):
        old_len = end - start
        if old_len < 0:
            continue
        new_bytes = new_text.encode('utf-8')
        # Adjust indices for accumulated shifts
        actual_start = start
        actual_end = actual_start + old_len
        text_bytes[actual_start:actual_end] = new_bytes

    return text_bytes.decode('utf-8')


def _process_module(mod_node, known_types: dict, replacements: list):
    if not _is_syntax_node(mod_node):
        return
    header = getattr(mod_node, 'header', None) or getattr(mod_node, 'moduleHeader', None)
    if header is None:
        for child in mod_node:
            if _is_syntax_node(child) and child.kind in (
                SyntaxKind.ModuleHeader,):
                header = child
                break

    if header is None:
        return

    port_list = None
    for child in header:
        if _is_syntax_node(child) and child.kind in (
            SyntaxKind.AnsiPortList,
            SyntaxKind.NonAnsiPortList,
        ):
            port_list = child
            break

    if port_list is None:
        return

    struct_ports = {}
    for port in port_list:
        if not _is_syntax_node(port):
            continue
        port_name = _get_port_name(port)
        port_type = _get_port_type_name(port)
        if port_type and port_type in known_types:
            st = known_types[port_type]
            if isinstance(st, StructType):
                if port_name:
                    struct_ports[port_name] = st

    if not struct_ports:
        return

    for port in list(port_list):
        if not _is_syntax_node(port):
            continue
        port_name = _get_port_name(port)
        if not port_name or port_name not in struct_ports:
            continue

        st = struct_ports[port_name]
        dir_str = _get_port_direction(port)

        flat_ports = []
        for flat_name, width, _ in st.flat_fields:
            full_name = f"{port_name}_{flat_name}"
            if width == 1:
                flat_ports.append(f"  {dir_str} logic                      {full_name}")
            else:
                flat_ports.append(f"  {dir_str} logic [{width-1}:0]               {full_name}")

        try:
            src_range = port.sourceRange
            start_byte = src_range.start.offset if hasattr(src_range.start, 'offset') else None
            end_byte = src_range.end.offset if hasattr(src_range.end, 'offset') else None
        except Exception:
            start_byte = None

        if start_byte is not None and end_byte is not None:
            new_text = "\n".join(flat_ports)
            replacements.append((start_byte, end_byte, new_text))

    _find_struct_accesses(mod_node, struct_ports, replacements)


def _find_struct_accesses(node, struct_ports: dict, replacements: list):
    if not _is_syntax_node(node):
        return
    if hasattr(node, 'kind'):
        k = node.kind
        if k == SyntaxKind.ScopedName:
            _try_replace_scoped_name(node, struct_ports, replacements)

    try:
        for child in node:
            _find_struct_accesses(child, struct_ports, replacements)
    except Exception:
        pass


def _try_replace_scoped_name(node, struct_ports: dict, replacements: list):
    """Try to replace a ScopedName like reg2hw_i.field.sub.q with flat name."""
    parts = _get_scoped_parts(node)
    if not parts:
        return

    base = parts[0]
    if base not in struct_ports:
        return

    st = struct_ports[base]
    field_path = parts[1:]

    if not field_path:
        return

    flat_name = _resolve_field_path(st, field_path)
    if flat_name is None:
        return

    full_flat = f"{base}_{flat_name}"

    try:
        src_range = node.sourceRange
        start = src_range.start.offset if hasattr(src_range.start, 'offset') else None
        end = src_range.end.offset if hasattr(src_range.end, 'offset') else None
    except Exception:
        start = None

    if start is not None and end is not None:
        replacements.append((start, end, full_flat))


def _get_scoped_parts(node) -> list[str]:
    """Extract parts from a ScopedName like 'a.b.c' → ['a', 'b', 'c']."""
    parts = []
    current = node
    while _is_syntax_node(current) and current.kind == SyntaxKind.ScopedName:
        children = list(current)
        if len(children) >= 2:
            left = children[0]
            right = children[-1]
            if _is_syntax_node(right) and right.kind == SyntaxKind.IdentifierName:
                parts.insert(0, str(right).strip())
            current = left
        else:
            break
    if _is_syntax_node(current) and current.kind == SyntaxKind.IdentifierName:
        parts.insert(0, str(current).strip())
    return parts


def _resolve_field_path(st: StructType, path: list[str]) -> str | None:
    """Resolve a field path like ['prescaler', 'q'] through a struct type."""
    fields = st.fields
    result_parts = []
    for p in path:
        if p in fields:
            result_parts.append(p)
            field = fields[p]
            if field.children:
                fields = field.children
            else:
                fields = {}
        else:
            return None
    return "_".join(result_parts)


def _is_syntax_node(node):
    """Check if node is a syntax node (iterable), not a token."""
    return hasattr(node, 'kind') and 'Token' not in str(type(node).__name__)


def _get_port_name(port) -> str | None:
    """Extract the port name from a port declaration."""
    def _find_name(node):
        if not _is_syntax_node(node):
            return None
        for child in node:
            if hasattr(child, 'kind'):
                if child.kind == SyntaxKind.Declarator:
                    for c2 in child:
                        if hasattr(c2, 'kind'):
                            k_str = str(c2.kind)
                            if 'Identifier' in k_str:
                                return str(c2).strip()
                result = _find_name(child)
                if result:
                    return result
        return None
    try:
        return _find_name(port)
    except Exception:
        return None


def _get_port_type_name(port) -> str | None:
    """Extract the type name from a port declaration (e.g. 'aon_timer_reg2hw_t')."""
    def _extract_named_type(node):
        if not _is_syntax_node(node):
            return None
        for child in node:
            if hasattr(child, 'kind'):
                if child.kind == SyntaxKind.NamedType:
                    for c2 in child:
                        if hasattr(c2, 'kind') and c2.kind == SyntaxKind.IdentifierName:
                            raw = str(c2).strip()
                            if '//' in raw:
                                raw = raw.split('//')[0].strip()
                            return raw
                if child.kind in (SyntaxKind.VariablePortHeader, SyntaxKind.PortDeclaration):
                    result = _extract_named_type(child)
                    if result:
                        return result
        return None
    try:
        return _extract_named_type(port)
    except Exception:
        return None


def _get_port_direction(port) -> str:
    """Extract port direction (input/output/inout)."""
    def _find_dir(node):
        if not _is_syntax_node(node):
            return None
        for child in node:
            if hasattr(child, 'kind'):
                k_str = str(child.kind)
                if 'Input' in k_str and 'Keyword' in k_str:
                    return "input "
                if 'Output' in k_str and 'Keyword' in k_str:
                    return "output"
                if 'InOut' in k_str and 'Keyword' in k_str:
                    return "inout "
                if child.kind in (SyntaxKind.VariablePortHeader, SyntaxKind.PortDeclaration):
                    result = _find_dir(child)
                    if result:
                        return result
        return None
    try:
        result = _find_dir(port)
        return result or "input "
    except Exception:
        pass
    return "input "


def _default_search_paths(module_path: str) -> list[str]:
    """Generate default search paths for OpenTitan packages."""
    paths = []
    mod_dir = os.path.dirname(module_path) if module_path else ""
    if mod_dir:
        paths.append(mod_dir)
    # OpenTitan standard paths
    ot_root = None
    if '/opentitan/' in module_path:
        idx = module_path.index('/opentitan/')
        ot_root = module_path[:idx + len('/opentitan/')]
    if ot_root:
        paths.append(os.path.join(ot_root, "hw", "ip", "prim", "rtl"))
        paths.append(os.path.join(ot_root, "hw", "ip", "aon_timer", "rtl"))
    return paths
