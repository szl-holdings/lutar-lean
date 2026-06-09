#!/usr/bin/env python3
"""Drift gate for VERIFIED_THEOREMS.md (mirrors check_numbers_drift.py).

CI regenerates VERIFIED_THEOREMS.md from the real build with
`gen_verified_theorems.py`; this gate fails if the committed file is out of date
versus that freshly generated one, so the published "solved theorems" list can
never drift from what the Lean kernel actually verifies.

Bootstrap-tolerant: if the committed file does not exist yet, the gate passes
with a notice (the generated file is uploaded as a CI artifact to be committed).

Exit codes: 0 = in sync (or bootstrap), 1 = drift, 2 = usage error.
"""
from __future__ import annotations

import argparse
import difflib
import os
import sys


def read(path: str) -> str:
    with open(path, "r", encoding="utf-8") as fh:
        return fh.read()


def main() -> int:
    ap = argparse.ArgumentParser(description="Fail if VERIFIED_THEOREMS.md drifted.")
    ap.add_argument("--committed", default="VERIFIED_THEOREMS.md",
                    help="Committed file under version control.")
    ap.add_argument("--generated", required=True,
                    help="Freshly generated file from this build.")
    args = ap.parse_args()

    if not os.path.isfile(args.generated):
        print(f"error: generated file not found: {args.generated}", file=sys.stderr)
        return 2

    if not os.path.isfile(args.committed):
        print("::notice::BOOTSTRAP — no committed %s yet; skipping drift gate. "
              "Commit the generated artifact to enable enforcement." % args.committed)
        return 0

    committed = read(args.committed)
    generated = read(args.generated)
    if committed == generated:
        print(f"OK: {args.committed} matches the freshly generated file.")
        return 0

    print(f"::error::DRIFT — {args.committed} is out of date versus the build.")
    print("Regenerate with:")
    print("  python3 .github/scripts/gen_verified_theorems.py --repo-path . "
          f"--out {args.committed}")
    print("----- unified diff (committed -> generated) -----")
    diff = difflib.unified_diff(
        committed.splitlines(keepends=True),
        generated.splitlines(keepends=True),
        fromfile=args.committed,
        tofile="generated",
    )
    sys.stdout.writelines(diff)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
