import os
import subprocess
import tempfile
import z3
from ..ir.transition_system import TransitionSystem


def ts_to_verilog(ts, module_name="top"):
    """Export a TransitionSystem to Verilog RTL (Verilog-95 compatible).

    Uses default Z3 variable names matching the parser's naming:
    - State vars: name (current), name_next (next)
    - Inputs: name_inp

    For trans_properties (involving |=> or =>), generates next-state
    wires so the bad output properly checks future-state conditions.

    Only the `bad` output is exposed as a port — state variables are
    internal registers. This ensures ABC miter/PDR treats only the
    property violation as the verification target.
    """
    lines = [f"module {module_name}(clk"]

    inp_names = [n for n in ts.inputs.keys() if n != "clk"]
    for name in inp_names:
        lines[-1] += f", {name}"

    has_props = bool(ts.properties or ts.trans_properties)
    if has_props:
        lines[-1] += ", bad"

    lines[-1] += ");"

    # Port declarations
    lines.append("  input clk;")
    for name in inp_names:
        w = ts.inputs[name].width
        if w == 1:
            lines.append(f"  input {name};")
        else:
            lines.append(f"  input [{w-1}:0] {name};")

    # State variables as internal registers
    for name, sv in ts.state_vars.items():
        w = sv.width
        if w == 1:
            lines.append(f"  reg {name};")
        else:
            lines.append(f"  reg [{w-1}:0] {name};")

    if has_props:
        lines.append("  output bad;")

    # Next-state wires
    next_wires = {}
    for name in ts.state_vars:
        if name in ts._next_state_exprs:
            w = ts.state_vars[name].width
            next_name = f"next_{name}"
            next_wires[name] = next_name
            if w == 1:
                lines.append(f"  wire {next_name};")
            else:
                lines.append(f"  wire [{w-1}:0] {next_name};")

    # Init
    for name, sv in ts.state_vars.items():
        w = sv.width
        init_val = sv.init_val
        lines.append(f"  initial {name} = {w}'d{init_val};")

    # Next-state logic as combinational assigns
    for name in ts.state_vars:
        if name in ts._next_state_exprs:
            next_name = next_wires[name]
            expr = ts._next_state_exprs[name]
            verilog_expr = _z3_to_verilog_expr(expr, ts)
            lines.append(f"  assign {next_name} = {verilog_expr};")

    # Sequential always block
    lines.append("")
    lines.append("  always @(posedge clk) begin")
    for name in ts.state_vars:
        if name in ts._next_state_exprs:
            lines.append(f"    {name} <= next_{name};")
        else:
            lines.append(f"    {name} <= {name};")
    lines.append("  end")

    # Bad state logic — property negation
    if has_props:
        lines.append("")
        bad_conds = []
        for pname, p_expr in ts.properties:
            viol = _z3_to_verilog_expr(z3.Not(p_expr), ts)
            bad_conds.append(f"({viol})")
        for pname, p_expr in ts.trans_properties:
            viol = _z3_to_verilog_expr(z3.Not(p_expr), ts)
            bad_conds.append(f"({viol})")
        if bad_conds:
            lines.append(f"  assign bad = {' || '.join(bad_conds)};")
        else:
            lines.append("  assign bad = 1'b0;")

    lines.append("endmodule")
    return "\n".join(lines)


def _z3_to_verilog_expr(expr, ts, paren=False):
    """Convert a simple Z3 expression to Verilog expression string.

    Handles basic operations: +, -, *, &, |, ^, ~, comparisons, constants, variables.
    For complex expressions, falls back to a placeholder.
    """
    if z3.is_const(expr):
        try:
            v = expr.as_long()
            w = _z3_width(expr)
            return f"{w}'d{v}"
        except Exception:
            name = str(expr)
            if name.endswith("_next"):
                base = name[:-5]
                # Use next_ wire name for trans_property references
                if base in ts.state_vars and base in ts._next_state_exprs:
                    return f"next_{base}"
                return base
            if name.endswith("_inp"):
                orig = name[:-4]
                if orig in ts.inputs:
                    return orig
            for sv_name in ts.state_vars:
                if name == sv_name:
                    return sv_name
            return name

    if z3.is_app(expr):
        kind = expr.decl().kind()
        children = expr.children()

        # BitVec arithmetic
        if kind == 1028:  # Z3_OP_BADD (bvadd)
            return f"({_z3_to_verilog_expr(children[0], ts)} + {_z3_to_verilog_expr(children[1], ts)})"
        if kind == 1029:  # Z3_OP_BSUB (bvsub)
            return f"({_z3_to_verilog_expr(children[0], ts)} - {_z3_to_verilog_expr(children[1], ts)})"
        if kind == 1030:  # Z3_OP_BMUL (bvmul)
            return f"({_z3_to_verilog_expr(children[0], ts)} * {_z3_to_verilog_expr(children[1], ts)})"

        # Bitwise
        if kind == 1049:  # Z3_OP_BAND (bvand)
            return f"({_z3_to_verilog_expr(children[0], ts)} & {_z3_to_verilog_expr(children[1], ts)})"
        if kind == 1050:  # Z3_OP_BOR (bvor)
            return f"({_z3_to_verilog_expr(children[0], ts)} | {_z3_to_verilog_expr(children[1], ts)})"
        if kind == 1052:  # Z3_OP_BXOR (bvxor)
            return f"({_z3_to_verilog_expr(children[0], ts)} ^ {_z3_to_verilog_expr(children[1], ts)})"
        if kind == 1051:  # Z3_OP_BNOT (bvnot)
            return f"(~{_z3_to_verilog_expr(children[0], ts)})"
        if kind == 1027:  # Z3_OP_BNEG (bvneg) — 2's complement negation
            return f"(-{_z3_to_verilog_expr(children[0], ts)})"

        # Comparisons
        if kind == 258:  # Z3_OP_EQ
            return f"({_z3_to_verilog_expr(children[0], ts)} == {_z3_to_verilog_expr(children[1], ts)})"
        if kind == 259:  # Z3_OP_DISTINCT (!=)
            return f"({_z3_to_verilog_expr(children[0], ts)} != {_z3_to_verilog_expr(children[1], ts)})"
        if kind == 1045:  # Z3_OP_ULT
            return f"({_z3_to_verilog_expr(children[0], ts)} < {_z3_to_verilog_expr(children[1], ts)})"
        if kind == 1041:  # Z3_OP_ULEQ
            return f"({_z3_to_verilog_expr(children[0], ts)} <= {_z3_to_verilog_expr(children[1], ts)})"
        if kind == 1047:  # Z3_OP_UGT
            return f"({_z3_to_verilog_expr(children[0], ts)} > {_z3_to_verilog_expr(children[1], ts)})"
        if kind == 1043:  # Z3_OP_UGEQ
            return f"({_z3_to_verilog_expr(children[0], ts)} >= {_z3_to_verilog_expr(children[1], ts)})"

        if kind == 1046:  # Z3_OP_SLT
            return f"($signed({_z3_to_verilog_expr(children[0], ts)}) < $signed({_z3_to_verilog_expr(children[1], ts)}))"
        if kind == 1042:  # Z3_OP_SLEQ
            return f"($signed({_z3_to_verilog_expr(children[0], ts)}) <= $signed({_z3_to_verilog_expr(children[1], ts)}))"
        if kind == 1044:  # Z3_OP_SGEQ
            return f"($signed({_z3_to_verilog_expr(children[0], ts)}) >= $signed({_z3_to_verilog_expr(children[1], ts)}))"

        # Shift
        if kind == 1064:  # Z3_OP_BSHL
            return f"({_z3_to_verilog_expr(children[0], ts)} << {_z3_to_verilog_expr(children[1], ts)})"
        if kind == 1065:  # Z3_OP_BLSHR
            return f"({_z3_to_verilog_expr(children[0], ts)} >> {_z3_to_verilog_expr(children[1], ts)})"
        if kind == 1066:  # Z3_OP_BASHR
            return f"($signed({_z3_to_verilog_expr(children[0], ts)}) >>> {_z3_to_verilog_expr(children[1], ts)})"

        # Concat
        if kind == 1056:  # Z3_OP_CONCAT
            n0 = _z3_to_verilog_expr(children[0], ts)
            n1 = _z3_to_verilog_expr(children[1], ts)
            return f"{{{n0}, {n1}}}"

        # Extract — params are [hi, lo]
        if kind == 1059:  # Z3_OP_EXTRACT
            params = expr.params()
            hi = params[0]
            lo = params[1]
            inner = _z3_to_verilog_expr(children[0], ts)
            return f"{inner}[{hi}:{lo}]"

        # ZeroExt / SignExt
        if kind == 1058:  # Z3_OP_ZERO_EXT
            params = expr.params()
            ext_bits = params[0]
            inner = children[0]
            inner_w = _z3_width(inner)
            if inner.decl().kind() == 1024:  # BNUM constant
                val = inner.as_long()
                return f"{(ext_bits + inner_w)}'d{val}"
            inner_str = _z3_to_verilog_expr(inner, ts)
            return f"{{{ext_bits}'d0, {inner_str}}}"
        if kind == 1057:  # Z3_OP_SIGN_EXT (rare in practice)
            inner_str = _z3_to_verilog_expr(children[0], ts)
            return f"{{($signed({inner_str}))}}"

        # ITE (conditional)
        if kind == 260:  # Z3_OP_ITE
            cond = _z3_to_verilog_expr(children[0], ts)
            t = _z3_to_verilog_expr(children[1], ts)
            f = _z3_to_verilog_expr(children[2], ts)
            return f"({cond} ? {t} : {f})"

        # Boolean operations
        if kind == 266:  # Z3_OP_IMPLIES
            c = _z3_to_verilog_expr(children[0], ts)
            i = _z3_to_verilog_expr(children[1], ts)
            # !cond || impl
            return f"(!({c}) || ({i}))"
        if kind == 261:  # Z3_OP_AND (Boolean)
            parts = [_z3_to_verilog_expr(c, ts) for c in children]
            return f"({' && '.join(f'({p})' for p in parts)})"
        if kind == 262:  # Z3_OP_OR (Boolean)
            parts = [_z3_to_verilog_expr(c, ts) for c in children]
            return f"({' || '.join(f'({p})' for p in parts)})"
        if kind == 263:  # Z3_OP_XOR (Boolean)
            return f"(({_z3_to_verilog_expr(children[0], ts)} ^ {_z3_to_verilog_expr(children[1], ts)}))"
        if kind == 265:  # Z3_OP_NOT (Boolean)
            return f"(!{_z3_to_verilog_expr(children[0], ts, True)})"

    return f"/* UNSUPPORTED: {expr} */"


def _z3_width(expr):
    try:
        return expr.sort().size()
    except Exception:
        return 1


def find_abc():
    """Find ABC binary on the system."""
    for path in ["abc", "/usr/bin/abc", "/usr/local/bin/abc"]:
        try:
            result = subprocess.run([path, "-h"], capture_output=True, text=True, timeout=5)
            if result.returncode == 0 or "ABC" in result.stdout:
                return path
        except (FileNotFoundError, subprocess.TimeoutExpired):
            continue
    try:
        result = subprocess.run(["yosys", "-V"], capture_output=True, text=True, timeout=5)
        if result.returncode == 0:
            return "yosys-abc"
    except (FileNotFoundError, subprocess.TimeoutExpired):
        pass
    return None


def ts_verify_via_abc(ts, yosys_bin="yosys", abc_bin="yosys-abc", timeout=60):
    """Verify TS properties using yosys + ABC PDR pipeline.

    1. Export TS to Verilog-95 with property encoded as `bad` output
    2. Yosys synthesizes to BLIF
    3. ABC strash + PDR on BLIF
    4. Parse result

    Returns dict with result, or None on failure.
    """
    verilog = ts_to_verilog(ts)

    v_path = tempfile.mktemp(suffix=".v")
    blif_path = tempfile.mktemp(suffix=".blif")

    try:
        with open(v_path, "w") as f:
            f.write(verilog)

        # Yosys: read Verilog, synthesize, write BLIF
        ys_result = subprocess.run(
            [yosys_bin, "-s", "-"],
            input=f"read_verilog {v_path}\nsynth -top top\nwrite_blif {blif_path}\n",
            capture_output=True, text=True, timeout=timeout / 2,
        )
        if ys_result.returncode != 0 or not os.path.exists(blif_path):
            return {"result": "unknown", "engine": "abc_blif",
                    "error": f"yosys failed: {ys_result.stderr[:200]}"}

        # ABC: read BLIF, strash to AIG, run PDR
        abc_script = f"read_blif {blif_path}; strash; pdr; print_stats"
        abc_result = subprocess.run(
            [abc_bin, "-f", "-"],
            input=abc_script,
            capture_output=True, text=True, timeout=timeout / 2,
        )
        output = abc_result.stdout + "\n" + abc_result.stderr

        # Parse ABC output — look for PDR result
        for line in output.split('\n'):
            if 'was asserted in frame' in line:
                return {"result": "fail", "engine": "abc_pdr",
                        "frame": line.strip()}
            if 'The network was proved' in line or 'Property proved' in line:
                return {"result": "proved", "engine": "abc_pdr"}

        return {"result": "unknown", "engine": "abc_pdr", "output": output[:500]}

    except FileNotFoundError as e:
        return {"result": "unknown", "engine": "abc_blif", "error": f"binary not found: {e}"}
    except subprocess.TimeoutExpired:
        return {"result": "unknown", "engine": "abc_blif", "error": "timeout"}
    finally:
        for p in [v_path, blif_path]:
            try:
                os.unlink(p)
            except Exception:
                pass


def ts_to_aiger(ts, yosys_bin="yosys", output_file=None):
    """Export TransitionSystem to AIGER format via yosys.

    Writes a Verilog representation of the TS, then calls yosys
    to convert to AIGER. Returns the path to the AIGER file.

    Requires yosys to be installed on the system.
    """
    verilog = ts_to_verilog(ts)

    if output_file is None:
        output_file = tempfile.mktemp(suffix=".aig")

    with tempfile.NamedTemporaryFile(suffix=".v", mode="w", delete=False) as f:
        v_path = f.name
        f.write(verilog)

    try:
        result = subprocess.run(
            [yosys_bin, "-p", f"read_verilog {v_path}; write_aiger {output_file}"],
            capture_output=True,
            text=True,
            timeout=30,
        )
        if result.returncode != 0:
            return None, f"yosys error: {result.stderr}"

        if not os.path.exists(output_file):
            return None, "AIGER file not produced"

        return output_file, None
    except FileNotFoundError:
        return None, f"yosys not found at {yosys_bin}"
    except subprocess.TimeoutExpired:
        return None, "yosys timed out"
    finally:
        try:
            os.unlink(v_path)
        except Exception:
            pass


def run_abc_on_aiger(aiger_path, abc_bin="abc", commands=None, timeout=30):
    """Run ABC verification on an AIGER file.

    Args:
        aiger_path: Path to AIGER file
        abc_bin: ABC binary path
        commands: List of ABC commands (default: PDR + BMC)
        timeout: Timeout in seconds

    Returns:
        (result_dict, output_string)
    """
    if commands is None:
        commands = [
            f"read_aiger {aiger_path}",
            "&mfs",     # PDR/IC3 with multiple frames
            "print_stats",
        ]

    abc_script = "; ".join(commands)
    try:
        result = subprocess.run(
            [abc_bin, "-f", abc_script] if abc_bin != "abc" else
            ["abc", "-c", abc_script],
            capture_output=True,
            text=True,
            timeout=timeout,
        )

        output = result.stdout + "\n" + result.stderr
        if "UNSAT" in result.stdout or "Property proved" in result.stdout:
            return {"result": "proved", "engine": "abc"}, output
        elif "SAT" in result.stdout or "Counterexample" in result.stdout:
            return {"result": "fail", "engine": "abc"}, output
        else:
            return {"result": "unknown", "engine": "abc"}, output

    except FileNotFoundError:
        return {"result": "unknown", "engine": "abc", "error": "abc not found"}, ""
    except subprocess.TimeoutExpired:
        return {"result": "unknown", "engine": "abc", "error": "timeout"}, ""
