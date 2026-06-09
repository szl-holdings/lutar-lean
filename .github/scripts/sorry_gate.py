#!/usr/bin/env python3
"""Sorry gate for the governance-surface directories.

Fails CI if a non-comment `sorry` appears under any governed directory (default
`Lutar/Uniqueness/` — the Theorem U / identifiability kernel surface). That
directory must stay 100%% sorry-free by construction.

This gate deliberately targets DIRECTORIES, not the legacy file
`Lutar/Uniqueness.lean`, which retains tagged open obligations by design
(Conjecture 1 stays open per honesty doctrine v11 — gating the file would falsely
red main). A governed directory that does not exist yet is a vacuous PASS, so the
gate auto-enforces the moment the Theorem U directory lands.

Detection mirrors lean_numbers.py: `\\bsorry\\b` on lines that are not
whole-line `--` comments. Exit codes: 0 = clean, 1 = sorry found, 2 = usage.
"""
from __future__ import annotations

import argparse
import os
import re
import sys

SORRY_RE = re.compile(r"\bsorry\b")
COMMENT_LINE_RE = re.compile(r"^\s*--")

DEFAULT_DIRS = (os.path.join("Lutar", "Uniqueness"),)


def scan_dir(base: str) -> list[tuple[str, int, str]]:
    hits: list[tuple[str, int, str]] = []
    for dirpath, _dirs, files in os.walk(base):
        for fn in sorted(files):
            if not fn.endswith(".lean"):
                continue
            full = os.path.join(dirpath, fn)
            with open(full, "r", encoding="utf-8", errors="replace") as fh:
                for n, line in enumerate(fh, 1):
                    if COMMENT_LINE_RE.match(line):
                        continue
                    if SORRY_RE.search(line):
                        hits.append((full, n, line.rstrip("\n")))
    return hits


def main() -> int:
    ap = argparse.ArgumentParser(description="Fail on `sorry` under governed dirs.")
    ap.add_argument("--repo-path", default=".", help="lutar-lean checkout root.")
    ap.add_argument("--dir", action="append", dest="dirs",
                    help="Governed directory (repo-relative). Repeatable. "
                         "Default: Lutar/Uniqueness")
    args = ap.parse_args()

    dirs = args.dirs if args.dirs else list(DEFAULT_DIRS)
    total = 0
    for rel in dirs:
        base = os.path.join(args.repo_path, rel)
        if not os.path.isdir(base):
            print(f"OK (vacuous): governed dir {rel}/ does not exist yet.")
            continue
        hits = scan_dir(base)
        if hits:
            total += len(hits)
            print(f"::error::{len(hits)} `sorry` occurrence(s) under {rel}/ "
                  "(governance surface must be sorry-free):")
            for path, n, text in hits:
                print(f"  {path}:{n}: {text.strip()}")
        else:
            print(f"OK: no `sorry` under {rel}/.")

    if total:
        print(f"::error::sorry gate FAILED ({total} occurrence(s)).")
        return 1
    print("sorry gate: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
