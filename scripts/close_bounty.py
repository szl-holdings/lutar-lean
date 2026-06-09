#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Flip a bounty board entry to CLOSED when its proof is accepted.

This is the deterministic edit half of the auto-close pipeline: the proof arbiter
(verify-proof CI in szl-holdings/lambda-bounty for Conjecture 1, the lake-build /
kernel check in lutar-lean for Conjecture 2) only ever fires this on a *green,
accepted* proof. The edit is text-based (not a PyYAML round-trip) so the public
board keeps its comments, block scalars and ordering; the result is then handed to
``check_bounties.py`` which is the no-bypass gate that refuses a half-filled CLOSED
bounty.

Idempotent: re-running with the same inputs leaves the file in the same state.

Usage:
    close_bounty.py --bounty-id <id> --solver <handle> --proof-commit <sha> \
        [--proof-repo szl-holdings/<repo>] [--verify-run <url>] \
        [--accepted-at <iso8601>] [--status CLOSED|AWARDED] [--bounties-dir DIR]
"""
from __future__ import annotations

import argparse
import datetime
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
DEFAULT_BOUNTIES = ROOT / "bounties"

# A top-level YAML key starts in column 0 (no leading whitespace) and is not a
# comment / document marker.
TOP_KEY_RE = re.compile(r"^[A-Za-z0-9_]+\s*:")
STATUS_RE = re.compile(r"^status\s*:.*$", re.M)


def _yaml_str(value: str) -> str:
    """Quote a scalar so it is safe in a YAML double-quoted context."""
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


def strip_existing_solved(text: str) -> str:
    """Remove any existing top-level ``solved:`` block (for idempotency)."""
    lines = text.splitlines(keepends=True)
    out: list[str] = []
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        if re.match(r"^solved\s*:", line):
            i += 1
            # consume the block body (indented lines / blanks) until the next
            # top-level key or EOF.
            while i < n:
                nxt = lines[i]
                if nxt.strip() == "" or nxt[:1] in (" ", "\t"):
                    i += 1
                    continue
                break
            continue
        out.append(line)
        i += 1
    return "".join(out)


def build_solved_block(
    solver: str,
    proof_commit: str,
    proof_repo: str | None,
    verify_run: str | None,
    accepted_at: str,
) -> str:
    parts = [
        "solved:",
        f"  solver: {_yaml_str(solver)}",
        f"  proof_commit: {_yaml_str(proof_commit)}",
    ]
    if proof_repo:
        parts.append(f"  proof_repo: {_yaml_str(proof_repo)}")
    if verify_run:
        parts.append(f"  verify_run: {_yaml_str(verify_run)}")
    parts.append(f"  accepted_at: {_yaml_str(accepted_at)}")
    parts.append(
        "  note: >"
    )
    parts.append(
        "    Auto-closed by the proof arbiter: the accepted proof discharged the open"
    )
    parts.append(
        "    obligation (lake build green, zero sorry, axioms allowlisted)."
    )
    return "\n".join(parts) + "\n"


def close_bounty(
    path: pathlib.Path,
    solver: str,
    proof_commit: str,
    proof_repo: str | None,
    verify_run: str | None,
    accepted_at: str,
    status: str,
) -> bool:
    """Edit ``path`` in place. Returns True if the file content changed."""
    original = path.read_text(encoding="utf-8")
    text = original

    # 1. Flip the status line.
    if not STATUS_RE.search(text):
        raise SystemExit(f"FATAL: no 'status:' line found in {path.name}")
    text = STATUS_RE.sub(f"status: {status}", text, count=1)

    # 2. Reflect the close in the title marker, if present (honesty: a CLOSED
    #    bounty should not still read "(OPEN)" in its title).
    text = re.sub(r"\(OPEN\)", f"({status})", text, count=1)

    # 3. Replace any existing solved block, then append the fresh one.
    text = strip_existing_solved(text)
    if not text.endswith("\n"):
        text += "\n"
    block = build_solved_block(solver, proof_commit, proof_repo, verify_run, accepted_at)
    text = text.rstrip("\n") + "\n\n" + block

    if text != original:
        path.write_text(text, encoding="utf-8")
        return True
    return False


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Close a bounty board entry on an accepted proof.")
    ap.add_argument("--bounty-id", required=True, help="bounty id (== YAML filename stem)")
    ap.add_argument("--solver", required=True, help="GitHub handle / name of the solver")
    ap.add_argument("--proof-commit", required=True, help="accepted proof commit SHA")
    ap.add_argument("--proof-repo", default=None, help="szl-holdings/<repo> the proof landed in")
    ap.add_argument("--verify-run", default=None, help="URL of the green arbiter CI run")
    ap.add_argument("--accepted-at", default=None, help="ISO-8601 timestamp (default: now, UTC)")
    ap.add_argument("--status", default="CLOSED", choices=["CLOSED", "AWARDED"])
    ap.add_argument("--bounties-dir", default=str(DEFAULT_BOUNTIES))
    args = ap.parse_args(argv)

    accepted_at = args.accepted_at or datetime.datetime.now(datetime.timezone.utc).strftime(
        "%Y-%m-%dT%H:%M:%SZ"
    )

    bounties_dir = pathlib.Path(args.bounties_dir)
    path = bounties_dir / f"{args.bounty_id}.yaml"
    if not path.exists():
        alt = bounties_dir / f"{args.bounty_id}.yml"
        if alt.exists():
            path = alt
        else:
            print(f"FATAL: bounty '{args.bounty_id}' not found in {bounties_dir}", file=sys.stderr)
            return 2

    changed = close_bounty(
        path,
        solver=args.solver,
        proof_commit=args.proof_commit,
        proof_repo=args.proof_repo,
        verify_run=args.verify_run,
        accepted_at=accepted_at,
        status=args.status,
    )
    if changed:
        print(f"Closed bounty '{args.bounty_id}' (status={args.status}, solver={args.solver}).")
    else:
        print(f"Bounty '{args.bounty_id}' already up to date — no change.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
