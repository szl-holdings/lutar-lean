#!/usr/bin/env python3
"""Conjecture Factory — difficulty grader (step 5 of the pipeline).

Runs a REAL solver ENSEMBLE against a candidate's machine-checkable predicate and
records, per solver, whether it resolved the problem and how long it took. The
grade is derived honestly from what the run actually produced — never fabricated.

A candidate's predicate (declared at intake) must expose, in a plain Python
module:
    def domain():            # -> iterable of test points (may be finite/infinite)
    def holds(x) -> bool     # the property the conjecture asserts for ALL x
    FINITE = True | False    # whether domain() is finite & fully enumerable
(optional)
    def sample(rng):         # -> a single random test point (for the sampler solver)

The conjecture is "for all x in domain(): holds(x)". Each solver searches for a
COUNTEREXAMPLE (an x with holds(x) False):

  Solvers (a real ensemble, deterministic given seed + budget):
    * exhaustive : iterate domain() in order up to the budget.
    * sampler    : draw random points (sample() if provided, else random index
                   into a materialised finite domain) up to the budget.

  Per-solver outcome:
    REFUTED         — found a counterexample (carries the witness).
    VERIFIED-FINITE — exhausted a FINITE domain with no counterexample.
    OPEN            — budget exhausted before the domain was (searched-to-N).
    UNREACHABLE     — no executable predicate / predicate import failed.

Aggregate result (honest, conservative):
    REFUTED         if ANY solver found a counterexample (witness recorded).
    VERIFIED-FINITE if a solver exhausted a finite domain clean (and none refuted).
    OPEN            otherwise (predicate ran but neither refuted nor exhausted).
    UNREACHABLE     if no solver could run.

`success_rate` = fraction of reachable solvers that RESOLVED the problem (REFUTED
or VERIFIED-FINITE). `difficulty` is a label derived from the result + how much of
the search budget was consumed — NOT a guess about true hardness:
    refuted-quickly / refuted / finite-verified / open-resistant / ungraded.

Doctrine v11: OPEN means "searched to N with no counterexample", NOT "true". A
VERIFIED-FINITE result certifies only the finite enumerated domain, not the
conjecture in general. The candidate stays OPEN.

stdlib only. `--self-test` runs offline fixtures (inline predicate modules).
"""
from __future__ import annotations

import argparse
import datetime as _dt
import importlib.util
import json
import os
import random
import sys
import time

SCHEMA = "szl.conjecture.grade/v1"
DEFAULT_BUDGET = 100_000
DEFAULT_SEED = 1729


def _utcnow() -> str:
    return _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _load_predicate_module(path: str):
    if not path or not os.path.isfile(path):
        raise FileNotFoundError(path)
    spec = importlib.util.spec_from_file_location("cf_predicate", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)  # type: ignore[union-attr]
    if not hasattr(mod, "domain") or not hasattr(mod, "holds"):
        raise AttributeError("predicate module must define domain() and holds(x)")
    return mod


def _jsonable(x):
    try:
        json.dumps(x)
        return x
    except (TypeError, ValueError):
        return repr(x)


def solver_exhaustive(mod, budget: int) -> dict:
    t0 = time.perf_counter()
    checked = 0
    finite = bool(getattr(mod, "FINITE", False))
    exhausted = True
    witness = None
    for x in mod.domain():
        if checked >= budget:
            exhausted = False
            break
        checked += 1
        try:
            ok = bool(mod.holds(x))
        except Exception as exc:  # a predicate that throws is a real signal
            witness = {"point": _jsonable(x), "error": str(exc)}
            return _solver_result("exhaustive", "REFUTED", checked, budget,
                                  t0, witness, note="holds() raised")
        if not ok:  # a clean False is a found counterexample, not a skip
            witness = {"point": _jsonable(x)}
            return _solver_result("exhaustive", "REFUTED", checked, budget,
                                  t0, witness, note="holds() returned False")
    if witness is not None:
        return _solver_result("exhaustive", "REFUTED", checked, budget, t0, witness)
    if finite and exhausted:
        return _solver_result("exhaustive", "VERIFIED-FINITE", checked, budget, t0, None)
    return _solver_result("exhaustive", "OPEN", checked, budget, t0, None,
                          note=("finite domain not fully enumerable within budget"
                                if finite else "infinite/streaming domain"))


def solver_sampler(mod, budget: int, seed: int) -> dict:
    t0 = time.perf_counter()
    rng = random.Random(seed)
    checked = 0
    materialised = None
    has_sample = hasattr(mod, "sample")
    if not has_sample:
        if not bool(getattr(mod, "FINITE", False)):
            return _solver_result("sampler", "UNREACHABLE", 0, budget, t0, None,
                                  note="no sample() and domain is not finite")
        materialised = list(mod.domain())
        if not materialised:
            return _solver_result("sampler", "OPEN", 0, budget, t0, None,
                                  note="empty domain")
    n = budget if has_sample else min(budget, len(materialised) * 4 + 1)
    for _ in range(n):
        checked += 1
        x = mod.sample(rng) if has_sample else materialised[rng.randrange(len(materialised))]
        try:
            ok = bool(mod.holds(x))
        except Exception as exc:
            return _solver_result("sampler", "REFUTED", checked, budget, t0,
                                  {"point": _jsonable(x), "error": str(exc)},
                                  note="holds() raised")
        if not ok:
            return _solver_result("sampler", "REFUTED", checked, budget, t0,
                                  {"point": _jsonable(x)})
    # Sampling never certifies absence; best non-refuting outcome is OPEN.
    return _solver_result("sampler", "OPEN", checked, budget, t0, None,
                          note="random sampling found no counterexample (not a proof)")


def _solver_result(name, result, checked, budget, t0, witness, note=""):
    return {
        "solver": name,
        "result": result,
        "checked": checked,
        "budget": budget,
        "elapsed_sec": round(time.perf_counter() - t0, 6),
        "witness": witness,
        "resolved": result in ("REFUTED", "VERIFIED-FINITE"),
        "note": note,
    }


def _difficulty(result: str, solvers: list[dict], budget: int) -> str:
    if result == "REFUTED":
        ref = next((s for s in solvers if s["result"] == "REFUTED"), None)
        if ref and ref["checked"] <= max(1, budget // 100):
            return "refuted-quickly"
        return "refuted"
    if result == "VERIFIED-FINITE":
        return "finite-verified"
    if result == "OPEN":
        return "open-resistant"
    return "ungraded"


def grade(candidate: dict, *, budget: int, seed: int,
          predicate_path: str | None = None, module=None) -> dict:
    predicate = candidate.get("predicate") or {"kind": "none"}
    solvers: list[dict] = []
    reachable = True
    unreachable_reason = ""

    if module is None:
        if predicate.get("kind") != "python-callable":
            reachable = False
            unreachable_reason = f"no executable predicate (kind={predicate.get('kind')})"
        else:
            path = predicate_path or predicate.get("module")
            try:
                module = _load_predicate_module(path)
            except Exception as exc:
                reachable = False
                unreachable_reason = f"predicate import failed: {exc}"

    if not reachable:
        return {
            "schema": SCHEMA,
            "candidate_id": candidate.get("id", ""),
            "graded_utc": _utcnow(),
            "solver_ensemble": [{"solver": "n/a", "result": "UNREACHABLE",
                                 "resolved": False, "note": unreachable_reason}],
            "result": "UNREACHABLE",
            "witness": None,
            "success_rate": 0.0,
            "difficulty": "ungraded",
            "budget": budget,
            "seed": seed,
            "honesty": (
                "No reachable solver: the candidate has no executable predicate, so "
                "it could not be graded. UNREACHABLE is reported honestly — it is "
                "NOT evidence the conjecture is true or hard. Candidate stays OPEN."
            ),
        }

    solvers.append(solver_exhaustive(module, budget))
    solvers.append(solver_sampler(module, budget, seed))

    refuted = next((s for s in solvers if s["result"] == "REFUTED"), None)
    if refuted is not None:
        result = "REFUTED"
        witness = refuted["witness"]
    elif any(s["result"] == "VERIFIED-FINITE" for s in solvers):
        result = "VERIFIED-FINITE"
        witness = None
    elif any(s["result"] == "OPEN" for s in solvers):
        result = "OPEN"
        witness = None
    else:
        result = "UNREACHABLE"
        witness = None

    reachable_solvers = [s for s in solvers if s["result"] != "UNREACHABLE"]
    resolved = [s for s in reachable_solvers if s["resolved"]]
    success_rate = round(len(resolved) / len(reachable_solvers), 4) if reachable_solvers else 0.0

    return {
        "schema": SCHEMA,
        "candidate_id": candidate.get("id", ""),
        "graded_utc": _utcnow(),
        "solver_ensemble": solvers,
        "result": result,
        "witness": witness,
        "success_rate": success_rate,
        "difficulty": _difficulty(result, solvers, budget),
        "budget": budget,
        "seed": seed,
        "honesty": (
            "Grade from a REAL ensemble run. REFUTED carries a concrete witness. "
            "VERIFIED-FINITE certifies only the finite enumerated domain, not the "
            "conjecture in general. OPEN means searched-to-budget with no "
            "counterexample — NOT a proof of truth. The candidate stays OPEN "
            "(doctrine v11)."
        ),
    }


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Difficulty-grade a conjecture candidate.")
    ap.add_argument("--candidate", help="normalised candidate JSON")
    ap.add_argument("--predicate", help="override predicate module path")
    ap.add_argument("--budget", type=int, default=DEFAULT_BUDGET)
    ap.add_argument("--seed", type=int, default=DEFAULT_SEED)
    ap.add_argument("--out", help="write grade JSON here")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args(argv)

    if args.self_test:
        return _self_test()

    if not args.candidate:
        ap.error("--candidate is required (or use --self-test)")
    with open(args.candidate, "r", encoding="utf-8") as fh:
        candidate = json.load(fh)
    result = grade(candidate, budget=args.budget, seed=args.seed,
                   predicate_path=args.predicate)
    out = json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    if args.out:
        with open(args.out, "w", encoding="utf-8") as fh:
            fh.write(out)
        print(f"grade OK: result={result['result']} "
              f"difficulty={result['difficulty']} "
              f"success_rate={result['success_rate']} -> {args.out}")
    else:
        sys.stdout.write(out)
    return 0


class _Mod:
    """A tiny stand-in predicate module for self-test (duck-typed)."""
    def __init__(self, domain_fn, holds_fn, finite, sample_fn=None):
        self.domain = domain_fn
        self.holds = holds_fn
        self.FINITE = finite
        if sample_fn is not None:
            self.sample = sample_fn


def _self_test() -> int:
    cand = {"id": "cf-test", "predicate": {"kind": "python-callable"}}

    # 1. Finite TRUE predicate -> VERIFIED-FINITE, success_rate accounts only for
    #    the solver that can certify (exhaustive); sampler stays OPEN.
    m_true = _Mod(lambda: range(100), lambda x: x >= 0, True)
    g1 = grade(cand, budget=1000, seed=1, module=m_true)
    assert g1["result"] == "VERIFIED-FINITE", g1["result"]
    assert g1["difficulty"] == "finite-verified"
    assert any(s["result"] == "VERIFIED-FINITE" for s in g1["solver_ensemble"])

    # 2. A real counterexample -> REFUTED with witness.
    m_false = _Mod(lambda: range(100), lambda x: x != 42, True)
    g2 = grade(cand, budget=1000, seed=1, module=m_false)
    assert g2["result"] == "REFUTED", g2["result"]
    assert g2["witness"] and g2["witness"]["point"] == 42, g2["witness"]
    assert g2["difficulty"] in ("refuted-quickly", "refuted")

    # 3. Infinite domain, no counterexample within budget -> OPEN.
    def _nat():
        i = 0
        while True:
            yield i
            i += 1
    m_open = _Mod(_nat, lambda x: True, False)
    g3 = grade(cand, budget=500, seed=1, module=m_open)
    assert g3["result"] == "OPEN", g3["result"]
    assert g3["difficulty"] == "open-resistant"
    ex = next(s for s in g3["solver_ensemble"] if s["solver"] == "exhaustive")
    assert ex["checked"] == 500 and ex["result"] == "OPEN"

    # 4. Predicate that raises -> treated as REFUTED (real failure signal).
    def _boom(x):
        if x == 7:
            raise ValueError("predicate blew up")
        return True
    m_boom = _Mod(lambda: range(100), _boom, True)
    g4 = grade(cand, budget=1000, seed=1, module=m_boom)
    assert g4["result"] == "REFUTED", g4["result"]
    assert g4["witness"]["point"] == 7

    # 5. No executable predicate -> UNREACHABLE, never faked.
    g5 = grade({"id": "x", "predicate": {"kind": "none"}}, budget=10, seed=1)
    assert g5["result"] == "UNREACHABLE" and g5["success_rate"] == 0.0
    assert g5["difficulty"] == "ungraded"

    # 6. Sampler finds a sparse counterexample via sample().
    m_samp = _Mod(_nat, lambda x: x != 13, False, sample_fn=lambda rng: 13)
    g6 = grade(cand, budget=50, seed=1, module=m_samp)
    assert g6["result"] == "REFUTED", g6["result"]
    samp = next(s for s in g6["solver_ensemble"] if s["solver"] == "sampler")
    assert samp["result"] == "REFUTED" and samp["witness"]["point"] == 13

    print("conjecture_grader self-test OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
