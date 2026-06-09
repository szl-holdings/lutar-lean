#!/usr/bin/env python3
"""Guard: keep the machine-checked VERIFIED_THEOREMS surface wired into CI.

lake-build.yml regenerates and drift-gates the honest "solved theorems" list on
every push/PR to main, in three invocations:

  1. sorry_gate.py                    -- no `sorry` on the governed surface
  2. gen_verified_theorems.py         -- regenerate the list from THIS build
  3. check_verified_theorems_drift.py -- fail if the committed list drifts

If any of those three is ever removed from the workflow, the published list
would silently stop being regenerated + kernel-gated, with no signal. This guard
fails loudly the moment that happens. It is a pure-stdlib text check (no Lean
toolchain) and self-tests its own checker against negative fixtures first.
"""
from __future__ import annotations

import argparse
import sys

REQUIRED = [
    ".github/scripts/sorry_gate.py",
    ".github/scripts/gen_verified_theorems.py",
    ".github/scripts/check_verified_theorems_drift.py",
]


def _non_comment_lines(text):
    """Drop YAML comment lines so a mention in a comment never counts as wiring."""
    return [ln for ln in text.splitlines() if not ln.lstrip().startswith("#")]


def check(text):
    """Return the list of required script invocations missing from `text`.

    A script counts as wired in only when it appears on a non-comment line that
    also runs it via `python3` (an actual `run:` invocation, not prose).
    """
    lines = _non_comment_lines(text)
    missing = []
    for script in REQUIRED:
        wired = any(("python3" in ln) and (script in ln) for ln in lines)
        if not wired:
            missing.append(script)
    return missing


def _self_test():
    good = (
        "      - name: Sorry gate\n"
        "        run: python3 .github/scripts/sorry_gate.py --repo-path . --dir Lutar/Uniqueness\n"
        "      - name: Generate\n"
        "        run: |\n"
        "          python3 .github/scripts/gen_verified_theorems.py --repo-path . --out g.md\n"
        "      - name: Drift\n"
        "        run: |\n"
        "          python3 .github/scripts/check_verified_theorems_drift.py --committed VERIFIED_THEOREMS.md --generated g.md\n"
    )
    assert check(good) == [], "self-test: the fully-wired fixture must pass"

    # A bare comment mention must NOT satisfy the guard.
    comment_only = good.replace(
        "          python3 .github/scripts/check_verified_theorems_drift.py --committed VERIFIED_THEOREMS.md --generated g.md\n",
        "          # see .github/scripts/check_verified_theorems_drift.py for the drift gate\n",
    )
    assert check(comment_only) == [".github/scripts/check_verified_theorems_drift.py"], (
        "self-test: a commented-out reference must not count as an invocation"
    )

    # Removing each invocation entirely must be detected, one at a time.
    for script in REQUIRED:
        broken = "\n".join(ln for ln in good.splitlines() if script not in ln) + "\n"
        assert check(broken) == [script], f"self-test: removing {script} must fail the guard"

    print("self-test OK: guard passes the wired fixture and fails every un-wired fixture")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--workflow", default=".github/workflows/lake-build.yml")
    ap.add_argument("--self-test", action="store_true", help="run the negative-fixture self-test and exit")
    args = ap.parse_args()

    if args.self_test:
        _self_test()
        return 0

    try:
        with open(args.workflow, "r", encoding="utf-8") as fh:
            text = fh.read()
    except FileNotFoundError:
        print(f"::error::{args.workflow} not found — the verified-theorems gate lives there")
        return 1

    missing = check(text)
    if missing:
        for m in missing:
            print(f"::error::{args.workflow} no longer invokes {m} — the verified-theorems gate is not wired in")
        print(
            "FAIL: the machine-checked VERIFIED_THEOREMS machinery is not fully wired into "
            f"{args.workflow}. Restore the sorry gate, generator, and drift gate steps."
        )
        return 1

    print(
        f"OK: {args.workflow} invokes sorry_gate.py + gen_verified_theorems.py + "
        "check_verified_theorems_drift.py — verified-theorems surface is gated on every build"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
