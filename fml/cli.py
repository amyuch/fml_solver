import sys
import os

from fml.parser.rtl_parser import RTLParser
from fml.engine.bmc import bmc_incremental
from fml.engine.kind import check_kinduction
from fml.engine.ic3 import IC3
from fml.engine.orchestrator import EngineOrchestrator, format_orchestrator_results
from fml.engine.simulation import simulation_falsify
from fml.engine.analysis.fan_in import compute_fanin_cone, summarize_cone
from fml.engine.analysis.metrics import MetricsReport
from fml.engine.solver.abc_bridge import ts_verify_via_abc
from fml.engine.cover import cover_bmc

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
    parser.add_argument("--cover", action="store_true", help="Run cover property analysis")
    parser.add_argument("--fanin", action="store_true", help="Show fan-in cone analysis")
    parser.add_argument("--metrics", action="store_true", help="Show property metrics")
    parser.add_argument("--dashboard", action="store_true", help="Show assertion quality dashboard (metrics + proof core + mutation)")
    parser.add_argument("--mutation", action="store_true", help="Run mutation testing on properties")
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

    if args.metrics:
        print(f"\n>>> Property Metrics...")
        metrics = MetricsReport(sys)
        for pname, p_expr in sys.properties:
            print(f"\n{'─' * 50}")
            print(f"  Property: {pname}")
            print(f"{'─' * 50}")
            m = metrics.compute(p_expr)
            _print_metrics(pname, m)
        for pname, p_expr in sys.trans_properties:
            print(f"\n{'─' * 50}")
            print(f"  Trans Property: {pname}")
            print(f"{'─' * 50}")
            m = metrics.compute(p_expr)
            _print_metrics(pname, m)
        return

    if args.dashboard:
        print(f"\n>>> Computing Assertion Quality Dashboard...", flush=True)
        _run_dashboard(sys, args.verbose, do_mutation=args.mutation)
        return

    if args.mutation:
        print(f"\n>>> Mutation Testing...")
        _run_mutation_tests(sys, verbose=args.verbose)
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

    if args.cover:
        print("\n>>> Running cover property analysis...")
        results = cover_bmc(sys, max_cycles=500, verbose=args.verbose)
        if results:
            for r in results:
                if r.get("result") == "reachable":
                    print(f"  R {r['property']}: REACHABLE at depth {r.get('bound', '?')}")
                    print(r.get("trace", ""))
                else:
                    print(f"  ? {r['property']}: {r.get('reason', 'unreachable')}")
        else:
            print("  No cover properties found.")
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

        if args.dashboard or args.verbose:
            _run_dashboard(sys, verbose=False, do_mutation=False)
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

    if args.bmc == 0 and args.kind == 0 and not args.ic3 and not args.auto and not args.abc and not args.cover:
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
        print(f"  X {result.get('property', '?')}: FAILED")
        print(f"    Counterexample at bound {result.get('bound', '?')}")
        trace = result.get("trace", "")
        if trace:
            print(trace)
    elif res == "proved":
        print(f"  V {result.get('property', '?')}: PROVED")
    elif res == "pass":
        print(f"  V All properties: PASS up to bound {result.get('bound', '?')}")
    else:
        print(f"  ? {result.get('property', '?')}: {result.get('reason', 'unknown')}")


def _print_metrics(pname, m):
    coi = m.get("coi", {})
    vac = m.get("vacuity", {})
    cov = m.get("coverage", {})
    cpx = m.get("complexity", {})

    print(f"    COI: {coi.get('n_state_vars', '?')}/{coi.get('n_state_total', '?')} state vars"
          f" ({coi.get('state_pruned_pct', 0):.0f}% pruned),"
          f" {coi.get('n_inputs', '?')}/{coi.get('n_input_total', '?')} inputs"
          f" ({coi.get('input_pruned_pct', 0):.0f}% pruned)")
    print(f"    Total signal bits in cone: {coi.get('total_signal_bits', '?')}")
    if coi.get("direct_state_vars"):
        print(f"    Direct state refs: {', '.join(coi['direct_state_vars'][:6])}"
              f"{'...' if len(coi['direct_state_vars']) > 6 else ''}")
    if coi.get("direct_inputs"):
        print(f"    Direct input refs: {', '.join(coi['direct_inputs'][:6])}"
              f"{'...' if len(coi['direct_inputs']) > 6 else ''}")

    vac_str = vac.get("reason", "?")
    if vac.get("vacuous") is True:
        vac_str = f"VACUOUS ({vac_str})"
    elif vac.get("vacuous") is False:
        vac_str = f"non-vacuous"
    print(f"    Vacuity: {vac_str}")

    print(f"    Coverage: {cov.get('coverage_pct', 0):.0f}% ({cov.get('exercised', 0)}/{cov.get('trials', 0)} trials)")
    print(f"    Complexity: depth={cpx.get('ast_depth', '?')}, "
          f"nodes={cpx.get('node_count', '?')}, "
          f"ops={', '.join(cpx.get('operators', [])[:8])}")


def _run_mutation_tests(ts, verbose=False):
    from fml.engine.analysis.metrics import MetricsReport
    metrics = MetricsReport(ts)
    for pname, p_expr in ts.properties:
        print(f"\n  {pname}: running mutation tests...")
        mr = metrics.mutation_test(p_expr, pname, max_mutations=12)
        if mr.get("mutation_score") is not None:
            print(f"    Mutation score: {mr['mutation_score']:.1%}"
                  f" ({mr['mutations_caught']}/{mr['mutations_total']} caught)")
            for m in mr.get("details", [])[:5]:
                print(f"      - {m['signal']}: {m['type']} {'caught' if m['caught'] else 'missed'}"
                      f"{' (equivalent)' if m.get('equivalent') else ''}")
        else:
            print(f"    {mr.get('reason', 'no result')}")


def _run_dashboard(ts, verbose=False, do_mutation=False):
    from fml.engine.analysis.metrics import MetricsReport, format_dashboard
    
    metrics = MetricsReport(ts)
    metrics_dict = {}
    mutation_results = {}
    proof_core_result = None
    
    for pname, p_expr in ts.properties:
        m = metrics.compute(p_expr, include_proof_core=False)
        metrics_dict[pname] = m
    
    for pname, p_expr in ts.trans_properties:
        m = metrics.compute(p_expr, include_proof_core=False)
        metrics_dict[pname] = m
    
    if do_mutation:
        for pname, p_expr in ts.properties:
            mr = metrics.mutation_test(p_expr, pname, max_mutations=10)
            mutation_results[pname] = mr
    
    if ts.assumptions:
        all_props = list(ts.properties) + list(ts.trans_properties)
        pc = metrics.extract_proof_core(all_props)
        proof_core_result = pc
    
    print(format_dashboard(ts, metrics_dict, mutation_results, proof_core_result, verbose=verbose))


if __name__ == "__main__":
    main()
