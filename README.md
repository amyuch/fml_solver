# FML Solver — Formal Verification for SystemVerilog RTL

A formal verification engine that parses real SystemVerilog (SV2017) RTL designs and checks assertions using Z3 and PySAT with multi-engine orchestration. Targets OpenTitan hardware IP.

## Features

| Category | Feature | Description |
|----------|---------|-------------|
| **Parsing** | SV2017 to Z3 | Real RTL parsing via pyslang (always_ff, always_comb, assign, generate, system functions) |
| | Multi-module flattening | Resolves cross-module hierarchy references |
| | OpenTitan preprocessing | Expands `ASSERT_*` macros to standard SVA, strips `ifdef FPV_ON` |
| | Struct port flattening | Replaces packed-struct ports with flat logic ports |
| **Engines** | BMC | Incremental bounded model checking with binary search for minimum CEX depth |
| | k-Induction | Proves safety properties that hold for all depths |
| | IC3/PDR | Z3-solver-based property directed reachability with CTI priority queue, unsat-core generalization, clause subsumption, BMC fallback |
| | SAT-accelerated IC3 | SATIC3 — Z3 bit-blast → Tseitin CNF → PySAT (Glucose4). BMC fallback when max_blocking exhausted |
| | ABC PDR | Verilog-95 export → yosys → yosys-abc `strash; pdr` pipeline |
| | Cover | BMC-based cover property engine |
| | Random Simulation | Quick shallow-bug falsification with random stimulus |
| **Analysis** | Fan-in Cone | Computes relevant state vars/inputs per property via Z3 dependency graph traversal |
| | Orchestrator | Per-property strategy (deep_state/datapath/control/mixed) + sequential/parallel dispatch with SATIC3 as primary engine |
| **Metrics** | Bit-level COI | Backward BFS on bit-sliced signal dependency graph |
| | BMC Vacuity | Checks antecedent activation per property at bounded depth |
| | Bounded Coverage | Model enumeration via independent solver per depth |
| | AIG Proxy Complexity | Bit-op count, depth, dry-run solve time |
| | MUS Proof Core | Which assumptions are essential/redundant per property |
| | COI Mutation | Bit-flip faults in COI, filtered by equivalence check |
| **Dashboard** | Quality Table | Per-property row: source label, COI%, vacuity, coverage, complexity, mutation score |
| | Proof Core Footer | Assumption essentiality breakdown |
| | Mutation Footer | Equivalent/redundant logic summary |
| **Solvers** | Z3 | Primary SMT solver for all engines |
| | PySAT (Glucose4) | SAT back-end via DIMACS export for SATIC3 |
| | ABC (yosys) | External PDR backend via Verilog export |

## Architecture

```
fml/
├── cli.py                  — CLI entry point
├── parser/
│   ├── rtl_parser.py       — SV2017 → TransitionSystem (pyslang)
│   ├── ot_preproc.py       — OpenTitan ASSERT→SVA preprocessor
│   └── flatten.py          — Multi-module hierarchy flattener
├── ir/
│   └── transition_system.py— Core IR (state vars, inputs, properties, assumptions, source tracking)
├── engine/
│   ├── base.py             — Abstract engine base class
│   ├── bmc.py              — Bounded model checking
│   ├── ic3.py              — Z3 IC3/PDR
│   ├── sat_ic3.py          — SAT-accelerated IC3
│   ├── kind.py             — k-induction
│   ├── cover.py            — Cover property engine
│   ├── simulation.py       — Random simulation
│   ├── orchestrator.py     — Multi-engine dispatch (SATIC3→IC3→BMC)
│   ├── solver/             — Low-level solver backends
│   │   ├── sat_solver.py   — Z3→DIMACS→PySAT bridge
│   │   └── abc_bridge.py   — Verilog→yosys→ABC PDR pipeline
│   └── analysis/           — Pre-analysis and metrics
│       ├── fan_in.py       — Fan-in cone computation
│       └── metrics.py      — Quality metrics: COI, vacuity, coverage, complexity, proof core, mutation, dashboard
├── utils/
│   └── helpers.py          — Shared utilities
└── __main__.py             — `python -m fml` support

examples/              — Test RTL designs
tests/                 — Test suite
benchmarks/            — Benchmark scripts
```

## Installation

```bash
git clone ...
cd fml_solver
pip install -r requirements.txt
```

Requires Python 3.12+, z3-solver, pyslang, python-sat (PySAT). Optional: yosys + yosys-abc for ABC PDR backend.

## Usage

```bash
# Single engine
python -m fml --bmc 100 design.sv
python -m fml --ic3 design.sv
python -m fml --kind 20 design.sv

# Orchestrator (auto-select strategy)
python -m fml --auto design.sv
python -m fml --auto --parallel design.sv

# Quality Dashboard
python -m fml design.sv --dashboard              # COI, vacuity, coverage, complexity
python -m fml design.sv --dashboard --mutation    # + mutation testing
python -m fml design.sv --auto -v                # verify + dashboard
python -m fml design.sv --metrics                # machine-readable metrics JSON

# Quick simulation
python -m fml --sim design.sv

# ABC PDR backend (requires yosys)
python -m fml --abc design.sv

# Multi-engine with analysis
python -m fml --auto --max-bmc 100 --max-kind 10 design.sv

# Parse inline RTL
python -m fml --text 'module top(input clk, ...); ... endmodule' --bmc 50

# OpenTitan designs (preprocess with ot_preproc.py first)
python -c "from fml.parser.ot_preproc import preprocess_file; open('out.sv','w').write(preprocess_file('design.sv'))"
python -m fml out.sv --auto --dashboard
```

## Project Structure

```
.
├── fml/               — Main package
├── examples/          — Example RTL designs
├── tests/             — Test suite
├── benchmarks/        — Benchmark scripts
├── pyproject.toml
└── requirements.txt
```
