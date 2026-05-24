import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from fml.parser.rtl_parser import RTLParser
from fml.engine.bmc import bmc_incremental
from fml.engine.kind import check_kinduction
from fml.engine.ic3 import IC3
from fml.engine.orchestrator import EngineOrchestrator, format_orchestrator_results
from fml.engine.simulation import simulation_falsify
from fml.engine.fan_in import compute_fanin_cone, summarize_cone
from fml.engine.aiger import ts_verify_via_abc

import z3


def main():
    import argparse

    parser = argparse.ArgumentParser(description="FML - Formal Verification Engine")
    parser.add_argument("file", nargs="?", help="SystemVerilog design file")
    parser.add_argument("--bmc", type=int, default=0, help="Run BMC up to bound K")
    parser.add_argument("--kind", type=int, default=0, help="Run k-induction with bound K")
    parser.add_argument("--ic3", action="store_true", help="Run IC3/PDR algorithm")
    parser.add_argument("--auto", action="store_true", help="Auto mode: orchestrator selects best strategy")
    parser.add_argument("--parallel", action="store_true", help="Run engines in parallel (auto mode)")
    parser.add_argument("--sim", action="store_true", help="Run random simulation only")
    parser.add_argument("--abc", action="store_true", help="Run ABC PDR (yosys + ABC pipeline) only")
    parser.add_argument("--fanin", action="store_true", help="Show fan-in cone analysis")
    parser.add_argument("--text", "-t", help="Inline SystemVerilog text")
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose output")
    parser.add_argument("--max-bmc", type=int, default=100, help="Max BMC bound")
    parser.add_argument("--max-kind", type=int, default=10, help="Max k-induction bound")

    args = parser.parse_args()

    if not args.file and not args.text:
        text = """module counter(input logic clk, rst_n, output logic [7:0] count);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            count <= 8'd0;
        else
            count <= count + 8'd1;
    end
    assert property (@(posedge clk) rst_n |=> count != 8'd0);
endmodule
"""
        sys = _run_on_text(text, args)
    elif args.text:
        sys = _run_on_text(args.text, args)
    else:
        sys = _run_on_file(args.file, args)

    if not sys:
        print("No designs found!")
        return

    print(f"\n{'=' * 60}")
    print(f"Design: {sys.name}")
    print(f"{'=' * 60}")

    if args.fanin:
        for pname, p_expr in sys.properties:
            print(f"\nProperty: {pname}")
            print(summarize_cone(sys, p_expr))
        for pname, p_expr in sys.trans_properties:
            print(f"\nTrans Property: {pname}")
            print(summarize_cone(sys, p_expr))
        return

    if args.sim:
        print("\n>>> Random Simulation (quick falsification)...")
        result = simulation_falsify(sys, max_cycles=500, trials=5, verbose=args.verbose)
        if result:
            _print_result(result)
        else:
            print("  No counterexample found in simulation.")
        return

    if args.abc:
        print("\n>>> Running ABC PDR (yosys + ABC pipeline)...")
        result = ts_verify_via_abc(sys)
        _print_result(result)
        return

    if args.auto:
        print("\n>>> Auto mode: orchestrating engines...")
        orch = EngineOrchestrator(sys, verbose=args.verbose)
        results = orch.verify_all(
            timeout_per_engine=60000,
            max_bmc=args.max_bmc,
            max_kind=args.max_kind,
            parallel=args.parallel,
        )
        print()
        print(format_orchestrator_results(results, verbose=args.verbose))
        return

    if args.bmc > 0:
        print(f"\n>>> Running BMC (bound={args.bmc})...")
        result = bmc_incremental(sys, args.bmc, verbose=args.verbose)
        _print_result(result)

    if args.kind > 0:
        print(f"\n>>> Running k-induction (k={args.kind})...")
        result = check_kinduction(sys, args.kind, verbose=args.verbose)
        _print_result(result)

    if args.ic3:
        print(f"\n>>> Running IC3/PDR...")
        ic3 = IC3(sys)
        result = ic3.prove(verbose=args.verbose)
        _print_result(result)

    if args.bmc == 0 and args.kind == 0 and not args.ic3 and not args.auto and not args.abc:
        print(sys.summarize())


def _run_on_text(text: str, args) -> object:
    parser = RTLParser()
    try:
        return parser.parse_text_to_ts(text)
    except Exception as e:
        print(f"Parse error: {e}")
        return None


def _run_on_file(filepath: str, args) -> object:
    parser = RTLParser()
    try:
        return parser.parse_to_ts(filepath)
    except Exception as e:
        print(f"Parse error: {e}")
        return None


def _print_result(result: dict):
    res = result.get("result", "unknown")
    if res == "fail":
        print(f"  ✗ {result.get('property', '?')}: FAILED")
        print(f"    Counterexample at bound {result.get('bound', '?')}")
        trace = result.get("trace", "")
        if trace:
            print(trace)
    elif res == "proved":
        print(f"  ✓ {result.get('property', '?')}: PROVED")
    elif res == "pass":
        print(f"  ✓ All properties: PASS up to bound {result.get('bound', '?')}")
    else:
        print(f"  ? {result.get('property', '?')}: {result.get('reason', 'unknown')}")


if __name__ == "__main__":
    main()
