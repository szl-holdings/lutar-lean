#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Schema + honesty lint for the open-problem bounty board (bounties/*.yaml).

Enforces, as a no-bypass CI gate, that every bounty is a well-formed, machine-readable
OPEN problem under the SZL honesty doctrine (v11):
  - required fields present and well-typed
  - file stem == id, ids unique
  - status in the allowed enum
  - doctrine == "v11"
  - reward.amount is founder-set, never an invented figure
  - acceptance criteria are non-empty and id'd
  - an OPEN conjecture is never represented as proved
  - a CLOSED/AWARDED (solved) bounty records a real solver + proof_commit and is
    never left half-filled (and an unsolved bounty never carries a `solved` block)
"""
from __future__ import annotations

import pathlib
import re
import sys

try:
    import yaml
except ImportError:  # pragma: no cover
    print("FATAL: PyYAML not installed (pip install pyyaml)", file=sys.stderr)
    sys.exit(2)

ROOT = pathlib.Path(__file__).resolve().parent.parent
BOUNTIES = ROOT / "bounties"

ALLOWED_STATUS = {"OPEN", "CLAIMED", "AWARDED", "CLOSED"}
# Statuses that assert the problem has actually been solved: they MUST carry a
# fully-filled `solved` block (solver + proof_commit) so the public board can never
# show a "solved" bounty with no provenance.
SOLVED_STATUS = {"AWARDED", "CLOSED"}
AXIOM_ALLOWLIST = "[propext, Quot.sound, Classical.choice]"
# A git commit SHA: 7-40 lowercase hex chars (short or full).
SHA_RE = re.compile(r"^[0-9a-f]{7,40}$")
REQUIRED = [
    "id",
    "title",
    "status",
    "doctrine",
    "summary",
    "problem_statement",
    "acceptance_criteria",
    "verification",
    "reward",
    "submission",
    "references",
    "honesty",
]
# Phrases that would represent an OPEN conjecture as already settled.
FORBIDDEN_OVERCLAIM = [
    re.compile(r"\bproven\s+unique\b", re.I),
    re.compile(r"\bis\s+(?:now\s+)?a\s+theorem\b", re.I),
    re.compile(r"\b(?:conjecture\s+1|conjecture\s+2)\s+is\s+(?:proved|proven|closed|settled)\b", re.I),
]
# A literal currency/number figure in reward.amount (honesty: never invent a figure).
MONEY = re.compile(r"\d")


def fail(errors: list[str], path: pathlib.Path, msg: str) -> None:
    errors.append(f"{path.name}: {msg}")


def check_solved_block(path: pathlib.Path, data: dict, status: str, errors: list[str]) -> None:
    """Validate the `solved` provenance block against the bounty status.

    SOLVED_STATUS bounties MUST have a complete `solved` mapping (a non-empty solver
    and a commit-SHA-shaped proof_commit); every other status MUST NOT carry one (so
    an OPEN problem can never silently ship solver provenance for a proof it lacks).
    """
    solved = data.get("solved")

    if status not in SOLVED_STATUS:
        if solved not in (None, "", {}, []):
            fail(
                errors,
                path,
                f"status '{status}' must not carry a 'solved' block "
                "(only AWARDED/CLOSED bounties record a solver)",
            )
        return

    # status is AWARDED or CLOSED → require a complete solved block.
    if not isinstance(solved, dict) or not solved:
        fail(
            errors,
            path,
            f"status '{status}' requires a non-empty 'solved' mapping with "
            "'solver' and 'proof_commit' (a solved bounty must record who solved it)",
        )
        return

    solver = solved.get("solver")
    if not isinstance(solver, str) or not solver.strip():
        fail(errors, path, "solved.solver must be a non-empty string for a solved bounty")

    commit = solved.get("proof_commit")
    if not isinstance(commit, str) or not commit.strip():
        fail(errors, path, "solved.proof_commit must be a non-empty string for a solved bounty")
    elif not SHA_RE.match(commit.strip()):
        fail(
            errors,
            path,
            f"solved.proof_commit '{commit}' must be a git commit SHA (7-40 hex chars)",
        )

    # proof_repo is optional, but if present it must be an szl-holdings repo.
    repo = solved.get("proof_repo")
    if repo is not None and "szl-holdings/" not in str(repo):
        fail(errors, path, "solved.proof_repo must be a 'szl-holdings/<repo>' reference")


def check_file(path: pathlib.Path, seen_ids: dict[str, str], errors: list[str]) -> None:
    try:
        data = yaml.safe_load(path.read_text(encoding="utf-8"))
    except yaml.YAMLError as exc:  # pragma: no cover
        fail(errors, path, f"invalid YAML: {exc}")
        return
    if not isinstance(data, dict):
        fail(errors, path, "top-level YAML must be a mapping")
        return

    for key in REQUIRED:
        if key not in data or data[key] in (None, "", [], {}):
            fail(errors, path, f"missing/empty required field '{key}'")

    bid = data.get("id")
    if isinstance(bid, str):
        if bid != path.stem:
            fail(errors, path, f"id '{bid}' must equal filename stem '{path.stem}'")
        if bid in seen_ids:
            fail(errors, path, f"duplicate id '{bid}' (also in {seen_ids[bid]})")
        else:
            seen_ids[bid] = path.name

    status = data.get("status")
    if status not in ALLOWED_STATUS:
        fail(errors, path, f"status '{status}' not in {sorted(ALLOWED_STATUS)}")

    if data.get("doctrine") != "v11":
        fail(errors, path, "doctrine must be 'v11'")

    # acceptance criteria: non-empty list of {id, check}, ids unique within file
    ac = data.get("acceptance_criteria")
    if isinstance(ac, list) and ac:
        ac_ids: set[str] = set()
        for i, item in enumerate(ac):
            if not isinstance(item, dict) or "id" not in item or "check" not in item:
                fail(errors, path, f"acceptance_criteria[{i}] needs 'id' and 'check'")
                continue
            if item["id"] in ac_ids:
                fail(errors, path, f"duplicate acceptance_criteria id '{item['id']}'")
            ac_ids.add(item["id"])
    elif "acceptance_criteria" in data:
        fail(errors, path, "acceptance_criteria must be a non-empty list")

    # verification.must_become_real must be true (a submission must become REAL)
    ver = data.get("verification")
    if isinstance(ver, dict):
        if ver.get("must_become_real") is not True:
            fail(errors, path, "verification.must_become_real must be true")
        if not ver.get("arbiter"):
            fail(errors, path, "verification.arbiter is required")

    # reward.amount must be founder-set, never an invented figure
    reward = data.get("reward")
    if isinstance(reward, dict):
        amount = reward.get("amount")
        if not isinstance(amount, str) or MONEY.search(amount):
            fail(
                errors,
                path,
                "reward.amount must be a founder-set string with no numeric figure "
                "(the board never invents an amount)",
            )

    # submission must point at an szl-holdings intake repo
    sub = data.get("submission")
    if isinstance(sub, dict):
        intake = str(sub.get("intake_repo", ""))
        if "github.com/szl-holdings/" not in intake:
            fail(errors, path, "submission.intake_repo must be a github.com/szl-holdings/* URL")

    # solved-state provenance: a CLOSED/AWARDED bounty must record its solver.
    if isinstance(status, str):
        check_solved_block(path, data, status, errors)

    # honesty: OPEN bounties must not be represented as proved
    blob = yaml.safe_dump(data)
    if status == "OPEN":
        for pat in FORBIDDEN_OVERCLAIM:
            if pat.search(blob):
                fail(errors, path, f"OPEN bounty contains overclaim matching /{pat.pattern}/")
        honesty = str(data.get("honesty", ""))
        if "not a theorem" not in honesty.lower():
            fail(errors, path, "OPEN bounty honesty note must state it is 'NOT a theorem'")

    # Λ / Conjecture 1 specific: must name Conjecture 1
    if data.get("conjecture") == 1 and "conjecture 1" not in blob.lower():
        fail(errors, path, "Λ bounty must explicitly name 'Conjecture 1'")


def main() -> int:
    if not BOUNTIES.is_dir():
        print(f"FATAL: {BOUNTIES} not found", file=sys.stderr)
        return 2
    files = sorted(p for p in BOUNTIES.iterdir() if p.suffix in (".yaml", ".yml"))
    if not files:
        print("FATAL: no bounty YAML files found", file=sys.stderr)
        return 2

    errors: list[str] = []
    seen_ids: dict[str, str] = {}
    for path in files:
        check_file(path, seen_ids, errors)

    if errors:
        print("Bounty board check FAILED:")
        for e in errors:
            print(f"  - {e}")
        return 1

    print(f"Bounty board OK — {len(files)} bount{'y' if len(files) == 1 else 'ies'} validated:")
    for path in files:
        print(f"  - {path.name}")
    print(f"Axiom allowlist enforced by the proof arbiter: {AXIOM_ALLOWLIST}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
