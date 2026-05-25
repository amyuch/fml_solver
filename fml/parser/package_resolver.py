"""Package resolver — finds SV package files and extracts type definitions."""

import os
from pyslang.syntax import SyntaxKind


class StructField:
    def __init__(self, name: str, width: int, offset: int = 0, children: dict = None):
        self.name = name
        self.width = width
        self.offset = offset
        self.children = children or {}

    def __repr__(self):
        ch = f" [{', '.join(repr(c) for c in self.children.values())}]" if self.children else ""
        return f"{self.name}[{self.offset}:{self.offset+self.width-1}]{ch}"


class StructType:
    def __init__(self, name: str, width: int, fields: dict[str, StructField]):
        self.name = name
        self.width = width
        self.fields = fields

    @property
    def flat_fields(self) -> list[tuple[str, int, int]]:
        """Return (flat_name, width, lsb_offset) for every leaf field."""
        result = []
        def _walk(fields, prefix):
            for fname, f in fields.items():
                full = f"{prefix}_{fname}" if prefix else fname
                if f.children:
                    _walk(f.children, full)
                else:
                    result.append((full, f.width, f.offset))
        _walk(self.fields, "")
        return result

    def __repr__(self):
        return f"StructType({self.name}, {self.width}b, {len(self.fields)} fields)"


def resolve_package_file(import_name: str, search_paths: list[str]) -> str | None:
    """Find a package file given its import name (e.g. 'aon_timer_reg_pkg')."""
    candidates = [
        f"{import_name}.sv",
        f"{import_name}.svh",
        f"{import_name.lower()}.sv",
    ]
    for path in search_paths:
        for cand in candidates:
            full = os.path.join(path, cand)
            if os.path.isfile(full):
                return full
            # Try without version suffix
            base = os.path.join(path, import_name)
            if os.path.isfile(base + ".sv"):
                return base + ".sv"
            if os.path.isfile(base + ".svh"):
                return base + ".svh"
    return None


def _resolve_type_width(type_node, known_types: dict, visited: set = None) -> int:
    """Compute the bit-width of a type node."""
    if visited is None:
        visited = set()
    k = type_node.kind
    if k == SyntaxKind.LogicType:
        dims = list(type_node.dimensions) if hasattr(type_node, 'dimensions') else []
        if dims:
            for d in dims:
                for child in d:
                    if hasattr(child, 'kind'):
                        if child.kind == SyntaxKind.RangeDimensionSpecifier:
                            # RangeSpecifier -> SimpleRangeSelect -> left/right
                            for c2 in child:
                                if c2.kind == SyntaxKind.SimpleRangeSelect:
                                    vals = []
                                    for c3 in c2:
                                        if c3.kind == SyntaxKind.IntegerLiteralExpression:
                                            try:
                                                vals.append(int(str(c3), 0))
                                            except ValueError:
                                                pass
                                    if len(vals) >= 2:
                                        return abs(vals[0] - vals[1]) + 1
        return 1
    if k == SyntaxKind.IntegerType:
        return 32
    if k == SyntaxKind.NamedType:
        for child in type_node:
            if hasattr(child, 'kind') and child.kind == SyntaxKind.IdentifierName:
                tname = str(child).strip()
                if tname in known_types:
                    if isinstance(known_types[tname], StructType):
                        return known_types[tname].width
                    if isinstance(known_types[tname], int):
                        return known_types[tname]
        return 32
    return 1
    if k == SyntaxKind.IntegerType:
        return 32
    if k == SyntaxKind.NamedType:
        for child in type_node:
            if hasattr(child, 'kind') and child.kind == SyntaxKind.IdentifierName:
                tname = str(child).strip()
                if tname in known_types:
                    if isinstance(known_types[tname], StructType):
                        return known_types[tname].width
                    if isinstance(known_types[tname], int):
                        return known_types[tname]
        return 32
    return 1
    if k == SyntaxKind.IntegerType:
        return 32
    if k == SyntaxKind.NamedType:
        for child in type_node:
            if hasattr(child, 'kind') and child.kind == SyntaxKind.IdentifierName:
                raw = str(child)
                tname = raw.strip()
                lines = [l.strip() for l in tname.split('\n')]
                tname = lines[-1] if lines else tname
                if '//' in tname:
                    tname = tname.split('//')[0].strip()
                if tname in known_types:
                    if isinstance(known_types[tname], StructType):
                        return known_types[tname].width
                    if isinstance(known_types[tname], int):
                        return known_types[tname]
        return 1
    return 1


def _try_eval(node) -> int | None:
    if hasattr(node, 'literal') and hasattr(node, 'kind') and node.kind == SyntaxKind.IntegerLiteralExpression:
        try:
            return int(str(node), 0)
        except ValueError:
            pass
    if hasattr(node, 'kind') and node.kind == SyntaxKind.IdentifierName:
        return None
    return None


def extract_types_from_package(filepath: str) -> dict:
    """Parse a package file and return known_types dict.

    Uses iterative passes until type widths converge.
    """
    from pyslang.driver import Driver
    known_types = {}

    d = Driver()
    d.addStandardArgs()
    d.parseCommandLine(f"parse {filepath}")
    d.processOptions()
    if not d.parseAllSources():
        return known_types

    # Multiple passes until no new widths are resolved
    prev_count = -1
    while len(known_types) != prev_count:
        prev_count = len(known_types)
        for tree in d.syntaxTrees:
            _extract_from_node(tree.root, known_types, filepath)

    return known_types

    for tree in d.syntaxTrees:
        _extract_from_node(tree.root, known_types, filepath)
    return known_types


def _extract_from_node(node, known_types: dict, filepath: str):
    if hasattr(node, 'kind') and node.kind == SyntaxKind.TypedefDeclaration:
        for child in node:
            k = child.kind
            if k == SyntaxKind.StructType:
                type_name = _get_typedef_name(node)
                if type_name:
                    st = _parse_struct_type(child, known_types, type_name)
                    if st:
                        known_types[type_name] = st
            elif k == SyntaxKind.EnumType:
                type_name = _get_typedef_name(node)
                if type_name:
                    _parse_enum_type(child, known_types, type_name)
            elif k == SyntaxKind.LogicType or k == SyntaxKind.IntegerType:
                type_name = _get_typedef_name(node)
                if type_name:
                    w = _resolve_type_width(child, known_types)
                    if isinstance(known_types.get(type_name), StructType):
                        pass  # Don't overwrite struct types
                    else:
                        known_types[type_name] = w

    # Extract parameters (localparam, parameter)
    if hasattr(node, 'kind') and node.kind == SyntaxKind.ParameterDeclarationStatement:
        _extract_parameter(node, known_types)

    if hasattr(node, 'members'):
        for m in node.members:
            _extract_from_node(m, known_types, filepath)
    try:
        for child in node:
            _extract_from_node(child, known_types, filepath)
    except Exception:
        pass


def _get_typedef_name(node) -> str | None:
    for child in node:
        if hasattr(child, 'kind'):
            if child.kind == SyntaxKind.IdentifierName:
                return str(child).strip()
            k_str = str(child.kind)
            if 'Identifier' in k_str and 'Token' in k_str:
                return str(child).strip()
    return None


def _get_member_name(node) -> str | None:
    for child in node:
        if hasattr(child, 'kind') and child.kind == SyntaxKind.Declarator:
            for c2 in child:
                if hasattr(c2, 'kind'):
                    if c2.kind == SyntaxKind.IdentifierName:
                        return str(c2).strip()
                    k_str = str(c2.kind)
                    if 'Identifier' in k_str and 'Token' in k_str:
                        return str(c2).strip()
    return None


def _parse_struct_type(node, known_types: dict, type_name: str) -> StructType | None:
    member_names = []
    member_widths = []
    member_children = []

    for child in node:
        if hasattr(child, 'kind') and child.kind == SyntaxKind.StructUnionMember:
            fname = _get_member_name(child)
            if fname is None:
                continue
            fwidth, children = _resolve_member_type(child, known_types)
            member_names.append(fname)
            member_widths.append(fwidth)
            member_children.append(children)

    total_width = sum(member_widths)
    fields = {}
    running = 0
    for i in range(len(member_names) - 1, -1, -1):
        fname = member_names[i]
        fwidth = member_widths[i]
        children = member_children[i]
        field = StructField(fname, fwidth, running, children)
        fields[fname] = field
        running += fwidth

    return StructType(type_name, total_width, fields)


def _parse_struct_type(node, known_types: dict, type_name: str) -> StructType | None:
    member_widths = []
    member_names = []
    member_children = []

    for child in node:
        if hasattr(child, 'kind') and child.kind == SyntaxKind.StructUnionMember:
            fname = _get_member_name(child)
            if fname is None:
                continue
            fwidth, children = _resolve_member_type(child, known_types)
            member_names.append(fname)
            member_widths.append(fwidth)
            member_children.append(children)

    total_width = sum(member_widths)
    fields = {}
    running = 0
    for i in range(len(member_names) - 1, -1, -1):
        fname = member_names[i]
        fwidth = member_widths[i]
        children = member_children[i]
        field = StructField(fname, fwidth, running, children)
        fields[fname] = field
        running += fwidth

    return StructType(type_name, total_width, fields)


def _extract_parameter(node, known_types: dict):
    """Extract parameter/localparam values from a ParameterDeclarationStatement."""
    for child in node:
        if hasattr(child, 'kind') and child.kind == SyntaxKind.ParameterDeclaration:
            for decl in child:
                if hasattr(decl, 'kind') and decl.kind == SyntaxKind.Declarator:
                    param_name = None
                    param_val = None
                    for c2 in decl:
                        if hasattr(c2, 'kind'):
                            k_str = str(c2.kind)
                            if 'Identifier' in k_str and 'Token' in k_str:
                                param_name = str(c2).strip()
                            elif c2.kind == SyntaxKind.EqualsValueClause:
                                for c3 in c2:
                                    if hasattr(c3, 'kind'):
                                        if c3.kind == SyntaxKind.IntegerLiteralExpression:
                                            try:
                                                param_val = int(str(c3), 0)
                                            except ValueError:
                                                pass
                    if param_name and param_val is not None:
                        known_types[param_name] = param_val


def _resolve_member_type(node, known_types: dict) -> tuple[int, dict]:
    """Resolve a struct member's type width and nested children."""
    for child in node:
        k = child.kind
        if k == SyntaxKind.StructType:
            nested = _parse_struct_type(child, known_types, "__nested__")
            if nested:
                return nested.width, nested.fields
            return 1, {}
        if k == SyntaxKind.LogicType:
            return _resolve_type_width(child, known_types), {}
        if k == SyntaxKind.NamedType:
            for c2 in child:
                if hasattr(c2, 'kind') and c2.kind == SyntaxKind.IdentifierName:
                    raw = str(c2)
                    # Extract just the identifier name, stripping trivia/comments
                    tname = raw.strip()
                    # Take the last non-empty line (after any // comments)
                    lines = [l.strip() for l in tname.split('\n')]
                    tname = lines[-1] if lines else tname
                    # Remove // line comments
                    if '//' in tname:
                        tname = tname.split('//')[0].strip()
                    if tname in known_types:
                        if isinstance(known_types[tname], StructType):
                            return known_types[tname].width, dict(known_types[tname].fields)
                        if isinstance(known_types[tname], int):
                            return known_types[tname], {}
                    return 1, {}
    return 1, {}


def _parse_enum_type(node, known_types: dict, type_name: str):
    """Parse an enum type and add its literal values to known_types."""
    width = 1
    for child in node:
        if hasattr(child, 'kind'):
            if child.kind == SyntaxKind.IntegerType:
                w = _resolve_type_width(child, known_types)
                if w > 1:
                    width = w
            elif child.kind == SyntaxKind.Declarator:
                enum_name = None
                enum_val = None
                for c2 in child:
                    if hasattr(c2, 'kind'):
                        k_str = str(c2.kind)
                        if 'Identifier' in k_str and 'Token' in k_str:
                            enum_name = str(c2).strip()
                        elif c2.kind == SyntaxKind.EqualsValueClause:
                            for c3 in c2:
                                if c3.kind == SyntaxKind.IntegerVectorExpression:
                                    try:
                                        enum_val = int(str(c3), 0)
                                    except ValueError:
                                        pass

                if enum_name and enum_val is not None:
                    # Store as a constant with its width
                    known_types[enum_name] = (width, enum_val)
    known_types[type_name] = width
