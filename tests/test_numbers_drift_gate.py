#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Coverage for the Lean numbers drift gate.

``.github/scripts/check_numbers_drift.py`` compares the counts measured by
``lean_numbers.py`` with the committed baseline in
``.github/data/lean_numbers.json``. Until this test existed the script had no
caller: ``lake-build.yml`` promised a drift failure in its header but never ran
the script, so a changed count or a new axiom name could land unnoticed.

These tests pin three things:

1. the script exits 0 on a match and 1 on any guarded drift (counts, added
   axiom names, removed axiom names);
2. ``lake-build.yml`` actually invokes the script against the committed
   baseline and the freshly measured file;
3. the committed baseline matches what ``lean_numbers.py`` measures on the
   checked-out tree, so the gate is green on the commit that carries it.

Runnable under pytest or directly (``python3 tests/test_numbers_drift_gate.py``).
"""

from __future__ import annotations

import copy
import json
import os
import subprocess
import sys
import tempfile

_TEST_DIR = os.path.dirname(os.path.abspath(__file__))
REPO_ROOT = os.path.dirname(_TEST_DIR)
GATE = os.path.join(REPO_ROOT, ".github", "scripts", "check_numbers_drift.py")
COUNTER = os.path.join(REPO_ROOT, ".github", "scripts", "lean_numbers.py")
BASELINE = os.path.join(REPO_ROOT, ".github", "data", "lean_numbers.json")
WORKFLOW = os.path.join(REPO_ROOT, ".github", "workflows", "lake-build.yml")


def _doc(**numbers) -> dict:
    base = {
        "declarations": 10,
        "axioms_raw": 3,
        "axioms_unique": 2,
        "axiom_names": ["a", "b"],
        "sorries_raw": 5,
        "sorries_noncomment": 4,
    }
    base.update(numbers)
    return {"schema": "szl.lean_numbers/v1", "numbers": base}


def _run_gate(baseline: dict, measured: dict) -> subprocess.CompletedProcess:
    with tempfile.TemporaryDirectory() as tmp:
        bpath = os.path.join(tmp, "baseline.json")
        mpath = os.path.join(tmp, "measured.json")
        with open(bpath, "w", encoding="utf-8") as fh:
            json.dump(baseline, fh)
        with open(mpath, "w", encoding="utf-8") as fh:
            json.dump(measured, fh)
        return subprocess.run(
            [sys.executable, GATE, "--baseline", bpath, "--measured", mpath],
            capture_output=True,
            text=True,
            encoding="utf-8",
        )


def test_match_passes():
    r = _run_gate(_doc(), _doc())
    assert r.returncode == 0, r.stdout + r.stderr
    assert "OK" in r.stdout


def test_unguarded_key_change_passes():
    # sorries_noncomment is reported but not part of the guarded claim set.
    r = _run_gate(_doc(), _doc(sorries_noncomment=99))
    assert r.returncode == 0, r.stdout + r.stderr


def test_count_drift_fails():
    for key in ("declarations", "axioms_raw", "axioms_unique", "sorries_raw"):
        base = _doc()
        drifted = copy.deepcopy(base)
        drifted["numbers"][key] += 1
        r = _run_gate(base, drifted)
        assert r.returncode == 1, f"{key}: {r.stdout}{r.stderr}"
        assert key in r.stdout


def test_new_axiom_name_fails():
    r = _run_gate(_doc(), _doc(axiom_names=["a", "b", "c"]))
    assert r.returncode == 1, r.stdout + r.stderr
    assert "NEW AXIOMS" in r.stdout and "'c'" in r.stdout


def test_removed_axiom_name_fails():
    r = _run_gate(_doc(), _doc(axiom_names=["a"]))
    assert r.returncode == 1, r.stdout + r.stderr
    assert "REMOVED AXIOMS" in r.stdout and "'b'" in r.stdout


def test_lake_build_workflow_runs_the_gate():
    with open(WORKFLOW, "r", encoding="utf-8") as fh:
        text = fh.read()
    assert "python3 .github/scripts/check_numbers_drift.py" in text
    assert "--baseline .github/data/lean_numbers.json" in text
    assert "--measured lean_numbers.measured.json" in text
    # The gate must run after the numbers are measured.
    assert text.index("--out lean_numbers.measured.json") < text.index(
        "check_numbers_drift.py"
    )


def test_committed_baseline_matches_the_tree():
    with tempfile.TemporaryDirectory() as tmp:
        out = os.path.join(tmp, "measured.json")
        r = subprocess.run(
            [sys.executable, COUNTER, "--repo-path", REPO_ROOT, "--ref", "test", "--out", out],
            capture_output=True,
            text=True,
            encoding="utf-8",
        )
        assert r.returncode == 0, r.stdout + r.stderr
        g = subprocess.run(
            [sys.executable, GATE, "--baseline", BASELINE, "--measured", out],
            capture_output=True,
            text=True,
            encoding="utf-8",
        )
        assert g.returncode == 0, g.stdout + g.stderr


if __name__ == "__main__":
    failures = 0
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            try:
                fn()
                print(f"PASS {name}")
            except AssertionError as exc:  # pragma: no cover - direct-run path
                failures += 1
                print(f"FAIL {name}: {exc}")
    sys.exit(1 if failures else 0)
