# fml_solver — Formal Verification Solver for SystemVerilog RTL

A formal verification engine that parses real SystemVerilog (SV2017) RTL designs and checks assertions using Z3 and PySAT with multi-engine orchestration.

## Features

- **Parser**: SV2017 RTL to Z3 transition system using pyslang. Handles `always_ff`, `always_comb`, `assign`, system functions (`$rose`/`$fell`/`$stable`/`$past`), multi-module flattening, generate blocks, and `assert`/`assume`/`cover` directives.
- **BMC (Bounded Model Checking)**: Incremental BMC with per-property binary search for minimum counterexample depth.
- **k-Induction**: Proves safety properties that hold for all depths.
- **IC3/PDR (Property Directed Reachability)**: With CTI priority queue, unsat-core generalization, clause subsumption, CTI deduplication, and BMC fallback.
- **Random Simulation**: Quick shallow-bug falsification with random stimulus.
- **Fan-in Cone Analysis**: Computes relevant state variables and inputs for each property via transitive closure over Z3 dependency graphs.
- **Engine Orchestrator**: Per-property strategy synthesis (deep_state/datapath/control/mixed) based on fan-in size and operator mix. Sequential or parallel engine dispatch.
- **SAT Bridge (PySAT)**: Z3 bit-blast + Tseitin CNF → PySAT (Glucose4/MiniSat/Lingeling/CaDiCaL). 2-8x faster than pure Z3 on bit-precise formulas.
- **CNF Pre-blaster**: Pre-bit-blasts transition relation to CNF for faster inductive checking.
- **ABC PDR Backend**: Verilog-95 export → yosys synth → BLIF → yosys-abc `strash; pdr` pipeline. Proves/unbounded verification via ABC's PDR engine.
- **Parallel Execution**: Multi-engine dispatch with `ThreadPoolExecutor` and per-engine time budgets.
- **AIGER Export**: Verilog → yosys → `.aig` generation (experimental, limited by yosys 0.9 cell support).

## Project Structure

```
fml/
  parser/        — RTL-to-TransitionSystem parser (pyslang)
  ir/            — TransitionSystem IR (state vars, inputs, properties, assumptions)
  engine/        — BMC, k-induction, IC3, simulation, orchestrator, fan-in, SAT bridge,
                   CNF context, AIGER/ABC bridge
examples/        — Test RTL designs
tests/           — Additional test cases
test_suite.py    — Unified test runner
main.py          — CLI entry point
```

## Usage

```bash
# Single engine
python main.py --bmc 100 design.sv
python main.py --ic3 design.sv
python main.py --kind 20 design.sv

# Auto mode (orchestrator — simulation → sequential/parallel engines)
python main.py --auto design.sv
python main.py --auto --parallel design.sv

# Quick falsification
python main.py --sim design.sv

# Additional options
python main.py --text 'module ...' --bmc 50
python main.py --auto --fanin --max-bmc 100 --max-kind 10 design.sv
```

## Installation

```bash
pip install -r requirements.txt
```

## Requirements

- Python 3.12+
- z3-solver >= 4.16
- pyslang >= 11.0
- python-sat (PySAT) >= 1.9.dev3
- yosys + yosys-abc (for ABC PDR backend)
