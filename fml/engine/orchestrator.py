import time
import z3
from concurrent.futures import ThreadPoolExecutor, as_completed
from ..ir.transition_system import TransitionSystem
from .bmc import bmc_incremental
from .kind import check_kinduction
from .ic3 import IC3
from .sat_ic3 import SATIC3
from .simulation import simulation_falsify, simulation_cover
from .analysis.fan_in import compute_fanin_cone, summarize_cone
from .analysis.metrics import MetricsReport
from .solver.abc_bridge import ts_verify_via_abc
from .cover import cover_bmc


class VerificationResult:
    def __init__(self, property_name, property_type="state"):
        self.property_name = property_name
        self.property_type = property_type
        self.result = "unknown"  # "proved", "fail", "unknown"
        self.engine = None
        self.bound = None
        self.counterexample = None
        self.trace = None
        self.reason = None
        self.time_taken = 0.0
        self.engines_tried = []
        self.metrics = None

    def to_dict(self):
        d = {
            "result": self.result,
            "property": self.property_name,
            "engine": self.engine,
            "bound": self.bound,
            "time": self.time_taken,
            "engines_tried": self.engines_tried,
        }
        if self.trace:
            d["trace"] = self.trace
        if self.counterexample:
            d["counterexample"] = self.counterexample
        if self.reason:
            d["reason"] = self.reason
        if self.metrics:
            d["metrics"] = self.metrics
        return d


class EngineOrchestrator:
    def __init__(self, ts, verbose=False):
        self.ts = ts
        self.verbose = verbose
        self._clause_cache = {}  # property_name -> list of inductive clauses

    def verify_all(self, timeout_per_engine=60000, max_bmc=100, max_kind=10,
                   parallel=False):
        """Verify all properties across all types.

        If parallel=True, engines run concurrently within each property.
        """
        results = {}

        for ptype in ["properties", "trans_properties", "cover_properties"]:
            prop_list = getattr(self.ts, ptype, [])
            for pname, p_expr in prop_list:
                res = self._verify_one(pname, p_expr, ptype,
                                       timeout_per_engine, max_bmc, max_kind,
                                       parallel=parallel)
                results[pname] = res

        return results

    def _verify_one(self, pname, p_expr, ptype, timeout, max_bmc, max_kind, parallel=False):
        res = VerificationResult(pname, ptype)

        if ptype == "cover_properties":
            return self._handle_cover(pname, p_expr, res)

        if ptype == "trans_properties":
            return self._verify_trans_property(pname, p_expr, res, max_kind)

        # Phase 0: Fan-in cone analysis
        fanin_state, fanin_inputs = compute_fanin_cone(self.ts, p_expr)
        if self.verbose:
            print(summarize_cone(self.ts, p_expr))

        # Phase 1: Quick falsification via random simulation (optional)
        start = time.time()
        if self.verbose:
            print(f"  [{pname}] Phase 1: Random simulation...")
        cex = simulation_falsify(self.ts, max_cycles=200, trials=2, verbose=self.verbose)
        res.engines_tried.append("simulation")
        if cex:
            elapsed = time.time() - start
            res.result = "fail"
            res.engine = "simulation"
            res.bound = cex.get("bound")
            res.counterexample = cex.get("counterexample")
            res.trace = cex.get("trace")
            res.time_taken = elapsed
            if self.verbose:
                print(f"  [{pname}] Simulation found CEX at depth {res.bound}")
            return res

        # Phase 2: Run formal engines
        if parallel:
            return self._verify_parallel(pname, p_expr, ptype, timeout,
                                          max_bmc, max_kind, res, start,
                                          fanin_state)

        res = self._verify_sequential(pname, p_expr, ptype, timeout,
                                       max_bmc, max_kind, res, start,
                                       fanin_state)

        # Phase 3: Metrics (always collected, appended to result)
        metrics = MetricsReport(self.ts)
        res.metrics = metrics.compute(p_expr)
        return res

    def _verify_sequential(self, pname, p_expr, ptype, timeout,
                            max_bmc, max_kind, res, start, fanin_state):
        prop_type_analysis = self._analyze_property(p_expr, fanin_state)
        strategy = self._select_strategy(prop_type_analysis)

        if self.verbose:
            print(f"  [{pname}] Property type: {prop_type_analysis}")
            print(f"  [{pname}] Strategy: {strategy}")

        for engine_name in strategy:
            engine_res = self._run_single_engine(engine_name, pname, timeout,
                                                  max_bmc, max_kind, res, start)
            if engine_res:
                return engine_res

        res.time_taken = time.time() - start
        return res

    def _verify_parallel(self, pname, p_expr, ptype, timeout,
                          max_bmc, max_kind, res, start, fanin_state):
        prop_type_analysis = self._analyze_property(p_expr, fanin_state)
        strategy = self._select_strategy(prop_type_analysis)

        if self.verbose:
            print(f"  [{pname}] Property type: {prop_type_analysis}")
            print(f"  [{pname}] Parallel strategy: {strategy}")

        per_engine_timeout = max(5, timeout // len(strategy))

        def run_engine(name):
            local_res = VerificationResult(pname, ptype)
            local_res.engines_tried = list(res.engines_tried)
            return self._run_single_engine(name, pname, per_engine_timeout,
                                            max_bmc, max_kind, local_res, time.time())

        with ThreadPoolExecutor(max_workers=len(strategy)) as executor:
            future_map = {
                executor.submit(run_engine, name): name
                for name in strategy
            }
            for future in as_completed(future_map):
                engine_res = future.result()
                if engine_res is not None:
                    res.result = engine_res.result
                    res.engine = engine_res.engine
                    res.bound = engine_res.bound
                    res.counterexample = engine_res.counterexample
                    res.trace = engine_res.trace
                    res.engines_tried = engine_res.engines_tried
                    res.time_taken = time.time() - start
                    return res

        res.time_taken = time.time() - start
        return res

    def _run_bmc_single(self, pname, p_expr, max_bmc):
        from .bmc import _bmc_check_one
        is_trans = False
        for pn, _ in self.ts.trans_properties:
            if pn == pname:
                is_trans = True
                break
        for k in range(max_bmc + 1):
            r = _bmc_check_one(self.ts, pname, p_expr, k, is_trans=is_trans)
            if r is not None:
                return r
        return {"result": "pass", "bound": max_bmc}

    def _select_strategy(self, prop_type):
        if prop_type == "deep_state":
            return ["sat_ic3", "ic3", "bmc"]
        elif prop_type == "datapath":
            return ["sat_ic3", "bmc", "ic3"]
        elif prop_type == "control":
            return ["sat_ic3", "ic3", "bmc"]
        else:
            return ["sat_ic3", "ic3", "bmc"]

    def _run_single_engine(self, engine_name, pname, timeout,
                            max_bmc, max_kind, res, start):
        elapsed_budget = (timeout - (time.time() - start)) / 1000
        if elapsed_budget <= 0:
            return None

        if self.verbose:
            print(f"  [{pname}] Engine: {engine_name}...")

        res.engines_tried.append(engine_name)

        ts = self.ts
        p_expr = None
        for plist_name in ["properties", "trans_properties", "cover_properties"]:
            plist = getattr(ts, plist_name, [])
            for pn, pe in plist:
                if pn == pname:
                    p_expr = pe
                    break

        if engine_name == "bmc":
            engine_res = self._run_bmc_single(pname, p_expr, max_bmc)
        elif engine_name == "ic3":
            ic3 = IC3(ts)
            engine_res = ic3._prove_property(p_expr, pname, verbose=self.verbose)
        elif engine_name == "sat_ic3":
            sat = SATIC3(ts)
            engine_res = sat._prove_property(p_expr, pname, verbose=self.verbose)
        elif engine_name == "abc":
            engine_res = ts_verify_via_abc(ts, timeout=int(elapsed_budget))
        else:
            return None

        if engine_res.get("result") == "fail":
            res.result = "fail"
            res.engine = engine_name
            res.bound = engine_res.get("bound") or engine_res.get("frame")
            res.counterexample = engine_res.get("counterexample")
            res.trace = engine_res.get("trace")
            res.time_taken = time.time() - start
            if self.verbose:
                print(f"  [{pname}] {engine_name} found CEX at depth {res.bound}")
            return res

        if engine_res.get("result") == "proved":
            res.result = "proved"
            res.engine = engine_name
            res.time_taken = time.time() - start
            if self.verbose:
                print(f"  [{pname}] {engine_name} proved property")
            return res

        if self.verbose:
            print(f"  [{pname}] {engine_name}: inconclusive")
        return None

    def verify_with_strategies(self, strategies, parallel=False):
        """Run multiple strategies, possibly in parallel. Return first conclusive result."""
        if not parallel:
            for strategy in strategies:
                res = self._run_strategy(strategy)
                if res.result in ("proved", "fail"):
                    return res
            return res

        with ThreadPoolExecutor(max_workers=len(strategies)) as executor:
            futures = {executor.submit(self._run_strategy, s): s for s in strategies}
            for future in as_completed(futures):
                res = future.result()
                if res.result in ("proved", "fail"):
                    for f in futures:
                        f.cancel()
                    return res
        return res

    def _run_strategy(self, strategy):
        """Run a strategy represented as a dict. Returns first conclusive result."""
        for step in strategy.get("steps", []):
            engine = step.get("engine")
            params = step.get("params", {})
            if engine == "simulation":
                res = simulation_falsify(self.ts, **params)
                if res:
                    return self._to_result(res, "simulation")
            elif engine == "bmc":
                res = bmc_incremental(self.ts, **params)
                if res.get("result") in ("fail", "proved", "pass"):
                    return self._to_result(res, "bmc")
            elif engine == "kind":
                res = check_kinduction(self.ts, **params)
                if res.get("result") in ("fail", "proved", "pass"):
                    return self._to_result(res, "kind")
            elif engine == "ic3":
                ic3 = IC3(self.ts)
                res = ic3.prove(**params)
                if res.get("result") in ("fail", "proved", "pass"):
                    return self._to_result(res, "ic3")
            elif engine == "abc":
                res = ts_verify_via_abc(self.ts, **params)
                if res.get("result") in ("fail", "proved", "pass"):
                    r = self._to_result(res, "abc")
                    if res.get("frame"):
                        r.bound = res.get("frame")
                    return r

        return VerificationResult("all")

    def _analyze_property(self, p_expr, fanin_vars):
        """Analyze a property to determine its type.

        Returns one of: 'deep_state', 'datapath', 'control', 'mixed'
        """
        n_state = len(fanin_vars)
        eq_count = 0
        cmp_count = 0
        total_ops = 0

        def walk(e):
            nonlocal eq_count, cmp_count, total_ops
            if e is None:
                return
            total_ops += 1
            try:
                decl = e.decl()
            except Exception:
                decl = None
            if decl is not None:
                decl_name = decl.name()
                if "eq" in decl_name.lower() or "=" in decl_name:
                    eq_count += 1
                if "lt" in decl_name.lower() or "gt" in decl_name.lower():
                    cmp_count += 1
            for child in e.children():
                walk(child)

        walk(p_expr)

        if n_state <= 10 and total_ops > 0 and eq_count / total_ops > 0.3:
            return "control"
        if cmp_count > 2 or n_state > 20:
            return "datapath"
        if n_state <= 5:
            return "deep_state"
        return "mixed"

    def _verify_trans_property(self, pname, p_expr, res, max_kind):
        from .kind import kind_check_one
        start = time.time()
        res.engines_tried.append("kinduction")
        kind_res = kind_check_one(self.ts, pname, p_expr, max_kind, is_trans=True,
                                   timeout=self.ts.timeout)
        elapsed = time.time() - start

        if kind_res.get("result") == "proved":
            res.result = "proved"
            res.engine = "kinduction"
            res.bound = kind_res.get("bound")
            res.time_taken = elapsed
            return res

        if kind_res.get("result") == "fail":
            res.result = "fail"
            res.engine = "kinduction"
            res.bound = kind_res.get("bound")
            res.time_taken = elapsed
            return res

        res.result = "unknown"
        res.engine = "kinduction"
        res.reason = "k-induction incomplete"
        res.time_taken = elapsed
        return res

    def _handle_cover(self, pname, p_expr, res):
        start = time.time()

        # Phase 1: Random simulation (fast)
        cres = simulation_cover(self.ts, max_cycles=200, trials=3, verbose=self.verbose)
        if cres:
            for r in cres:
                if r.get("result") == "reachable" and r.get("property") == pname:
                    res.result = "reachable"
                    res.engine = "simulation"
                    res.bound = r.get("bound")
                    res.counterexample = r.get("counterexample")
                    res.trace = r.get("trace")
                    res.time_taken = time.time() - start
                    return res

        # Phase 2: BMC-based cover (exhaustive)
        if self.verbose:
            print(f"  [{pname}] Simulation missed cover, trying BMC cover...")
        bres = cover_bmc(self.ts, max_cycles=500, verbose=self.verbose)
        if bres:
            for r in bres:
                if r.get("result") == "reachable" and r.get("property") == pname:
                    res.result = "reachable"
                    res.engine = "cover_bmc"
                    res.bound = r.get("bound")
                    res.counterexample = r.get("counterexample")
                    res.trace = r.get("trace")
                    res.time_taken = time.time() - start
                    return res

        res.time_taken = time.time() - start
        res.result = "unknown"
        res.engine = "cover_bmc"
        res.reason = "cover_target not reached"
        return res

    def _to_result(self, raw, engine_name):
        r = VerificationResult(raw.get("property", "unknown"))
        r.result = raw.get("result", "unknown")
        r.engine = engine_name
        r.bound = raw.get("bound")
        r.counterexample = raw.get("counterexample")
        r.trace = raw.get("trace")
        r.reason = raw.get("reason")
        return r


def format_orchestrator_results(results, verbose=False):
    lines = []
    for pname, res in sorted(results.items()):
        if res.result == "proved":
            icon = "  \u2713"
        elif res.result == "fail":
            icon = "  \u2717"
        elif res.result == "reachable":
            icon = "  R"
        else:
            icon = "  ?"
        lines.append(f"{icon} {pname:40s} {res.result:10s} [{res.engine:12s}] {res.time_taken:.2f}s")
        if verbose and res.engines_tried:
            lines.append(f"     engines tried: {', '.join(res.engines_tried)}")
        if verbose and res.bound is not None:
            lines.append(f"     bound: {res.bound}")
        if verbose and res.metrics:
            m = res.metrics
            coi = m.get("coi", {})
            lines.append(f"     COI: {coi.get('n_state_vars', '?')} state vars, {coi.get('n_inputs', '?')} inputs")
            vac = m.get("vacuity", {})
            if vac.get("vacuous"):
                lines.append(f"     VACUOUS: {vac.get('reason', '')}")
            cov = m.get("coverage", {})
            lines.append(f"     Coverage: {cov.get('coverage_pct', 0):.0f}%")
    return "\n".join(lines)
