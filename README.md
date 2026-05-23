# fml_solver — Formal Verification Solver for SystemVerilog RTL

A formal verification engine that parses real SystemVerilog (SV2017) RTL designs and checks assertions using Z3-based SAT solvers with modern algorithms.

## Features

- **Parser**: SV2017 RTL to Z3 transition system using pyslang. Handles `always_ff`, `always_comb`, `assign`, system functions (`$rose`/`$fell`/`$stable`/`$past`), multi-module flattening, and `assume`/`cover`/`assert property` directives.

- **BMC (Bounded Model Checking)**: Incremental BMC with per-property binary search for minimum counterexample depth.

- **k-Induction**: Proves safety properties that hold for all depths.

- **IC3/PDR (Property Directed Reachability)**: With CTI priority queue, unsat-core generalization, clause subsumption, CTI deduplication (spinning detection), and BMC fallback.

## Project Structure

```
fml/
  parser/        — RTL-to-TransitionSystem parser (pyslang)
  ir/            — TransitionSystem IR (state vars, inputs, properties, assumptions)
  engine/        — BMC, k-induction, IC3 solvers
examples/        — Test RTL designs
tests/           — Additional test cases
test_suite.py    — Unified test runner
main.py          — CLI entry point
```

## Usage

```bash
python main.py --solver bmc <file.sv> [--max-depth 100]
python main.py --solver ic3 <file.sv> [--max-frames 50]
python main.py --solver kind <file.sv> [--max-depth 20]
```

## Requirements

- Python 3.12+
- z3-solver >= 4.16
- pyslang >= 11.0
