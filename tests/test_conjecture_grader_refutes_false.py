#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Regression: the exhaustive solver must REFUTED a clean False from holds().

The 2026-08-31 fix closed a soundness hole where a False return from holds(x)
was silently skipped, allowing a counterexample to pass with VERIFIED-FINITE.
The sampler (lines ~132) had this right; the exhaustive loop did not.
"""

from __future__ import annotations

import importlib.util
import pathlib

SCRIPT = pathlib.Path(__file__).resolve().parents[1] / ".github" / "scripts" / "conjecture_grader.py"

def _load():
    spec = importlib.util.spec_from_file_location("conjecture_grader", SCRIPT)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod

def test_exhaustive_refutes_clean_false():
    cg = _load()

    class ConjectureWithCounterexample:
        FINITE = True
        @staticmethod
        def domain():
            return [1, 2, 3]
        @staticmethod
        def holds(x):
            return x != 2  # x=2 is the counterexample

    result = cg.solver_exhaustive(ConjectureWithCounterexample, budget=10)
    assert result["result"] == "REFUTED", result
    assert result["witness"] == {"point": 2}, result

def test_exhaustive_verifies_clean_finite():
    cg = _load()

    class FullyTrueConjecture:
        FINITE = True
        @staticmethod
        def domain():
            return [1, 2, 3]
        @staticmethod
        def holds(x):
            return True

    result = cg.solver_exhaustive(FullyTrueConjecture, budget=10)
    assert result["result"] == "VERIFIED-FINITE", result
    assert result["witness"] is None

if __name__ == "__main__":
    test_exhaustive_refutes_clean_false()
    test_exhaustive_verifies_clean_finite()
    print("conjecture_grader exhaustive refutation tests: PASS")
