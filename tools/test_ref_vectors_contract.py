#!/usr/bin/env python3
"""Exercise the compiled RefVectors checker with positive and negative corpora.

CI: python3 tools/test_ref_vectors_contract.py -- .lake/build/bin/ref_vectors
An explicit command can also use the pinned interpreter:
  python tools/test_ref_vectors_contract.py -- lean --run MainRef.lean
The caller must make the compiled RefVectors module available on LEAN_PATH.
No network calls, model evaluation, or theorem/proof claims are made here.
"""
from __future__ import annotations

import argparse
import copy
import json
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def fixture_cases():
    canonical = json.loads((ROOT / "reference-vectors.json").read_text(encoding="utf-8"))

    def top(**fields):
        value = copy.deepcopy(canonical)
        value.update(fields)
        return value

    def first(**fields):
        value = copy.deepcopy(canonical)
        value["vectors"][0].update(fields)
        return value

    def single(axes, expected, **fields):
        value = top(**fields)
        value["vectors"] = [{"id": "contract-control", "axes": axes, "lambda": expected}]
        return value

    def overflow(value):
        # Valid JSON whose numeric magnitude overflows Float; not the invalid NaN/Infinity tokens.
        return json.dumps(value, allow_nan=False).replace('"__overflow__"', "1e400")

    positive = [
        ("canonical-ten-vectors", canonical),
        ("nine-real-zero-axes", single([0] * 9, 0)),
        ("finite-nonnegative-above-one", single([2] * 9, 2)),
        ("tighter-zero-tolerance", single([1] * 9, 1, toleranceAbs=0, toleranceRel=0)),
    ]
    negative = [
        ("empty-corpus", top(vectors=[]), "reference vectors must be nonempty"),
        ("unknown-schema", top(schema="unsupported"), "unsupported reference-vector schema"),
        ("wrong-formula", top(formula="arithmetic mean"), "unsupported reference-vector formula"),
        ("zero-dimension", top(k=0), "reference-vector k must be 9"),
        ("wrong-dimension", top(k=8), "reference-vector k must be 9"),
        ("fractional-dimension", top(k=9.5), "Natural number expected"),
        ("float-dimension", top(k=9.0), "Natural number expected"),
        ("negative-dimension", top(k=-1), "Natural number expected"),
        ("boolean-dimension", top(k=True), "Natural number expected"),
        ("oversized-dimension", top(k=10**30), "reference-vector k must be 9"),
        ("short-axes", first(axes=[0.9] * 8), "expected 9 axes, got 8"),
        ("long-axes", first(axes=[0.9] * 10), "expected 9 axes, got 10"),
        ("empty-axes", single([], 0), "expected 9 axes, got 0"),
        # A zero used to short-circuit lambdaFloat before an invalid second axis was examined.
        ("negative-axis-with-zero", single([0, -1] + [1] * 7, 0), "axes must be nonnegative"),
        ("negative-expected-result", first(**{"lambda": -1}), "lambda must be nonnegative"),
        ("overflow-axis-with-zero", overflow(single([0, "__overflow__"] + [1] * 7, 0)),
         "expected a finite number"),
        ("overflow-expected-result", overflow(first(**{"lambda": "__overflow__"})),
         "expected a finite number"),
        ("overflow-absolute-tolerance", overflow(top(toleranceAbs="__overflow__")),
         "expected a finite number"),
        ("overflow-relative-tolerance", overflow(top(toleranceRel="__overflow__")),
         "expected a finite number"),
        ("negative-absolute-tolerance", top(toleranceAbs=-1), "toleranceAbs must be between"),
        ("negative-relative-tolerance", top(toleranceRel=-1), "toleranceRel must be between"),
        ("looser-absolute-tolerance", top(toleranceAbs=2e-12), "toleranceAbs must be between"),
        ("looser-relative-tolerance", top(toleranceRel=2e-9), "toleranceRel must be between"),
        ("wrong-answer-hidden-by-large-tolerance", single([1] * 9, 100, toleranceAbs=1e100),
         "toleranceAbs must be between"),
        # Valid contract, false parity: the numerical comparison must still reject it.
        ("wrong-answer-with-valid-contract", single([1] * 9, 0.5), "FAIL"),
    ]
    return positive, negative


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checker", nargs=argparse.REMAINDER,
                        help="checker command after -- (default: lake exe ref_vectors)")
    args = parser.parse_args(argv)
    checker = args.checker
    if checker[:1] == ["--"]:
        checker = checker[1:]
    checker = checker or ["lake", "exe", "ref_vectors"]
    positive, negative = fixture_cases()
    failures = []
    with tempfile.TemporaryDirectory(prefix="szl-ref-vectors-") as directory:
        for name, value, expected_code, expected_text in (
            [(name, value, 0, "PASS") for name, value in positive]
            + [(name, value, 1, needle) for name, value, needle in negative]
        ):
            path = Path(directory) / f"{name}.json"
            raw = value if isinstance(value, str) else json.dumps(value, ensure_ascii=False, allow_nan=False)
            path.write_text(raw, encoding="utf-8")
            result = subprocess.run([*checker, str(path)], cwd=ROOT, capture_output=True,
                                    text=True, encoding="utf-8", errors="replace", timeout=120)
            output = result.stdout + result.stderr
            ok = (result.returncode == expected_code and expected_text in output
                  and (expected_code == 0 or "PASS" not in output))
            print(f"{'OK' if ok else 'FAILED'} {name} exit={result.returncode}", flush=True)
            if not ok:
                failures.append(name)
                print(output)
    if failures:
        print("REF_VECTORS_CONTRACT_FAILED " + ", ".join(failures))
        return 1
    print(f"REF_VECTORS_CONTRACT_OK {len(positive)} positive {len(negative)} negative")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
