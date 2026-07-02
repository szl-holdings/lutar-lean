#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Source-of-truth guard test: PROVEN_FORMULAS ↔ real Lean declarations.

This is the SOURCE-side mirror of a11oy's served-formula registry guard. It
FAILS if any formula the showcase (`PROVEN_FORMULAS.md`) labels **PROVEN** does
not resolve to an actual Lean theorem/lemma DECLARATION in the repo's `.lean`
files (an unbacked overclaim), and it FAILS if anything ever tags Λ-uniqueness
as proven — Λ stays **Conjecture 1**, never a theorem.

Runnable both under pytest (`pytest tests/test_proven_formulas_guard.py`) and
directly (`python3 tests/test_proven_formulas_guard.py`).
"""

from __future__ import annotations

import importlib.util
import os
import sys

_TEST_DIR = os.path.dirname(os.path.abspath(__file__))
REPO_ROOT = os.path.dirname(_TEST_DIR)
_GUARD_PATH = os.path.join(
    REPO_ROOT, ".github", "scripts", "check_proven_formulas.py"
)


def _load_guard():
    spec = importlib.util.spec_from_file_location("check_proven_formulas", _GUARD_PATH)
    assert spec and spec.loader, f"cannot load guard from {_GUARD_PATH}"
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


guard = _load_guard()
RESULT = guard.evaluate(REPO_ROOT)


def test_guard_self_test_passes():
    """The checker trusts itself only after its negative fixtures pass."""
    assert guard._self_test() == 0


def test_no_unbacked_proven_formulas():
    """Every PROVEN entry must resolve to a real Lean declaration."""
    unbacked = RESULT["unbacked"]
    assert not unbacked, (
        "Unbacked PROVEN_FORMULAS overclaim(s) — named theorem absent in .lean:\n"
        + "\n".join(
            f"  {r['formula_id']} {r['name']} (status={r['status']})"
            for r in unbacked
        )
    )


def test_locked_proven_set_is_exactly_eight():
    """The locked-proven set stays exactly {F1,F4,F7,F11,F12,F18,F19,F22}."""
    assert not RESULT["locked_id_violations"], RESULT["locked_id_violations"]
    verified_ids = {
        r["formula_id"] for r in RESULT["registry"] if r["status"] == "verified"
    }
    assert guard.LOCKED_PROVEN_IDS <= verified_ids, (
        f"expected {sorted(guard.LOCKED_PROVEN_IDS)} verified, "
        f"got {sorted(verified_ids)}"
    )


def test_lambda_stays_conjecture_one():
    """Λ-uniqueness is NEVER a theorem — the conjecture stays open + false."""
    assert not RESULT["lambda_violations"], (
        "Λ honesty violation(s):\n"
        + "\n".join(f"  {v}" for v in RESULT["lambda_violations"])
    )


def test_registry_reports_all_three_statuses_are_valid():
    """Every entry carries an honest status from the allowed vocabulary."""
    allowed = {"verified", "unbacked", "experimental"}
    assert RESULT["registry"], "registry is empty — parsing regressed"
    for r in RESULT["registry"]:
        assert r["status"] in allowed, r
        assert isinstance(r["lean_decl_exists"], bool), r
    # Experimental entries must never be reported as proven.
    for r in RESULT["registry"]:
        if r["claimed_maturity"] == "experimental":
            assert r["status"] == "experimental", r


def test_overall_verdict_ok():
    assert RESULT["ok"], RESULT


if __name__ == "__main__":
    failures = 0
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            try:
                fn()
                print(f"PASS {name}")
            except AssertionError as exc:
                failures += 1
                print(f"FAIL {name}: {exc}")
    c = RESULT["counts"]
    print(
        f"\nregistry: {c['verified']} verified · {c['unbacked']} unbacked · "
        f"{c['experimental']} experimental"
    )
    sys.exit(1 if failures else 0)
