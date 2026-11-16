#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# © 2026 Lutar, Stephen P. — SZL Holdings · ORCID 0009-0001-0110-4173
"""Guard: assert a green main lake-build actually PUBLISHED a usable Theorem-U snapshot.

Every green `main` run of "Lake build (gate + numbers)" (lake-build.yml) builds a
deterministic `theorem_u_snapshot.json` (via `.github/scripts/build_proof_snapshot.py`)
and uploads it as the artifact `theorem-u-snapshot-<sha>`. That snapshot is the
*subject* the szl-lake anchor workflow later cosign-signs and records, and the
public proof state reads its honesty block from it.

The emission is currently best-effort: if `build_proof_snapshot.py` regresses,
or the upload step in lake-build.yml is renamed / dropped / bumped to an
artifact-excluding action, the snapshot could quietly stop being produced (or be
produced empty / malformed) on an otherwise green build, with nothing failing.
This mirrors the regression already guarded for receipts by a11oy's
`release-receipt-summary-guard.yml` + `check_release_receipt_summary.py`.

This validator is the content half of that guard. Given the DOWNLOADED snapshot
artifact (a directory, or an explicit file), it FAILS unless the artifact is
non-empty, parses, and — critically — keeps the honesty block intact:

  * schema == "szl.proof.snapshot/v1" and kind == "theorem-u"
  * milestone.status == "REAL-conditional" and milestone.kernel_only is True
  * milestone.headline_decls is a non-empty list (the Theorem-U headline pack)
  * honesty.locked_set matches the canonical claim map and revision-bound evidence
  * the evidence covers every locked carrier and stays inside the kernel trust base
  * honesty.theorem_u states REAL-conditional (never "proven")
  * honesty.conjecture_1 states OPEN / machine-checked FALSE (never closed)

If any of those flip, the guard fails loudly — a silently-disappearing snapshot,
or one whose honesty was quietly loosened to overclaim, can never pass green.

Exit codes:
  0  the snapshot artifact is present, non-empty, well-formed and honest
  1  the snapshot artifact is missing, empty, malformed, or its honesty flipped
  2  usage / environment error
"""
from __future__ import annotations

import argparse
import json
import tempfile
from pathlib import Path

from build_locked_formula_evidence import load_json, sha256_file
from locked_snapshot_contract import (
    CLAIM_MAP_PATH, INPUT_PATHS, REPO_ROOT, SCHEMA as LOCKED_EVIDENCE_SCHEMA,
    evidence_digest, validate_snapshot_locked_binding,
)

EXPECTED_SCHEMA = "szl.proof.snapshot/v1"
EXPECTED_KIND = "theorem-u"
# Theorem U is kernel-verified but CONDITIONAL on its checkable hypotheses; it is
# NOT part of the locked-proven baseline. The status must never silently flip to
# "PROVEN" (that would overclaim).
EXPECTED_STATUS = "REAL-conditional"
# Locked IDs are read from claims/locked-formulas.v1.json through the shared contract.


def _find_snapshots(directory: Path) -> list[Path]:
    """Return every *.json file under ``directory``.

    The real artifact holds a single `theorem_u_snapshot.json`, but we glob
    defensively so a future rename inside the artifact is still audited.
    """
    return sorted(
        p for p in directory.rglob("*") if p.is_file() and p.name.endswith(".json")
    )


def _contains_all(text: object, needles: tuple[str, ...]) -> bool:
    if not isinstance(text, str):
        return False
    low = text.lower()
    return all(n.lower() in low for n in needles)


def validate_snapshot_file(path: Path, expected_commit: str | None = None,
                           *, source_root: Path | None = None) -> list[str]:
    """Validate one snapshot JSON file. Returns a list of problems ([] == valid)."""
    try:
        raw = path.read_text(encoding="utf-8")
    except Exception as exc:  # noqa: BLE001 - an unreadable snapshot is a failure
        return [f"could not read {path}: {exc}"]
    if not raw.strip():
        return [f"{path.name} is empty"]
    try:
        data = json.loads(raw)
    except Exception as exc:  # noqa: BLE001 - non-parsing snapshot is a failure
        return [f"{path.name} is not valid JSON: {exc}"]
    if not isinstance(data, dict):
        return [f"{path.name} top-level JSON is not an object"]

    problems: list[str] = []

    # --- top-level identity ------------------------------------------------- #
    if data.get("schema") != EXPECTED_SCHEMA:
        problems.append(
            f"schema is '{data.get('schema')}', expected '{EXPECTED_SCHEMA}'"
        )
    if data.get("kind") != EXPECTED_KIND:
        problems.append(f"kind is '{data.get('kind')}', expected '{EXPECTED_KIND}'")

    if expected_commit is not None and data.get("kernel_commit") != expected_commit:
        problems.append("snapshot kernel_commit differs from the source workflow run")

    # --- milestone: kernel-verified, conditional, headline present ---------- #
    milestone = data.get("milestone")
    if not isinstance(milestone, dict):
        problems.append("missing/invalid 'milestone' object")
    else:
        if milestone.get("status") != EXPECTED_STATUS:
            problems.append(
                f"milestone.status is '{milestone.get('status')}', "
                f"expected '{EXPECTED_STATUS}' (Theorem U must stay conditional, not overclaim)"
            )
        if milestone.get("kernel_only") is not True:
            problems.append(
                f"milestone.kernel_only is {milestone.get('kernel_only')!r}, "
                "expected True (snapshot must come from a kernel-clean build)"
            )
        headline = milestone.get("headline_decls")
        if not isinstance(headline, list) or not headline:
            problems.append(
                "milestone.headline_decls is missing or empty "
                "(the Theorem-U headline pack must be present)"
            )

    # --- honesty block: must stay intact, never loosen --------------------- #
    honesty = data.get("honesty")
    if not isinstance(honesty, dict):
        problems.append("missing/invalid 'honesty' object")
    else:
        # Theorem U: REAL-conditional, never "proven".
        if not _contains_all(honesty.get("theorem_u"), ("REAL-conditional",)):
            problems.append(
                "honesty.theorem_u must state 'REAL-conditional' "
                f"(got: {honesty.get('theorem_u')!r})"
            )
        # Conjecture 1: OPEN / machine-checked FALSE, never closed.
        if not _contains_all(honesty.get("conjecture_1"), ("OPEN", "FALSE")):
            problems.append(
                "honesty.conjecture_1 must state it is OPEN and machine-checked FALSE "
                f"(got: {honesty.get('conjecture_1')!r})"
            )

    problems.extend(validate_snapshot_locked_binding(data, source_root=source_root))
    return problems


def check_dir(directory: Path, expected_commit: str | None = None,
              *, source_root: Path | None = None) -> int:
    """Audit a downloaded artifact directory. Returns a process exit code."""
    if not directory.exists():
        print(
            f"::error::artifact directory '{directory}' does not exist — the "
            "theorem-u-snapshot artifact was not produced (total_count 0). A green "
            "main lake-build must always publish theorem-u-snapshot-<sha>."
        )
        return 1
    snapshots = _find_snapshots(directory)
    if not snapshots:
        print(
            f"::error::no JSON snapshot found under '{directory}' — the "
            "theorem-u-snapshot artifact is empty or lost its snapshot file "
            "(most likely the upload step was dropped/renamed, or upload-artifact "
            "was bumped to a version that re-excludes the file)."
        )
        return 1

    ok = True
    for path in snapshots:
        problems = validate_snapshot_file(path, expected_commit, source_root=source_root)
        if problems:
            ok = False
            for problem in problems:
                print(f"::error::{path.name}: {problem}")
        else:
            data = json.loads(path.read_text(encoding="utf-8"))
            m = data.get("milestone", {})
            print(
                f"[theorem-u-snapshot-guard] OK: {path.name} "
                f"kind={data.get('kind')} status={m.get('status')} "
                f"kernel_only={m.get('kernel_only')} "
                f"locked_set={data.get('honesty', {}).get('locked_set')}"
            )
    return 0 if ok else 1


def _selftest_locked_evidence(commit: str) -> dict:
    """Synthetic offline carrier records for tests; this is not kernel evidence."""
    claims = load_json(REPO_ROOT / CLAIM_MAP_PATH)
    evidence = {
        "schema": LOCKED_EVIDENCE_SCHEMA,
        "repository": claims["repository"],
        "source_commit": commit,
        "source_tree": "0" * 40,
        "input_files_match_head": True,
        "lean_toolchain": claims["lean_toolchain"],
        "locked_ids": claims["locked_ids"],
        "carrier_theorem_count": claims["carrier_theorem_count"],
        "trust_base": claims["trust_base"],
        "kernel_query_tool": "Lean.collectAxioms",
        "inputs": {path.as_posix(): sha256_file(REPO_ROOT / path) for path in INPUT_PATHS},
        "claims": [
            {
                "claim_id": claim["claim_id"],
                "carriers": [
                    {"theorem": "Puriq.Formula.Proved." + name, "axioms": [], "allowed": True}
                    for name in claim["theorem_declarations"]
                ],
            }
            for claim in claims["claims"]
        ],
        "limitations": ["Synthetic fixture only; does not attest a Lean build."],
    }
    evidence["evidence_digest"] = evidence_digest(evidence)
    return evidence


def _selftest() -> int:
    """Prove the validator passes a good snapshot and rejects broken/dishonest ones."""
    failures: list[str] = []

    locked_evidence = _selftest_locked_evidence("0" * 40)
    good = {
        "schema": EXPECTED_SCHEMA,
        "kind": EXPECTED_KIND,
        "repo": "szl-holdings/lutar-lean",
        "kernel_commit": "0" * 40,
        "branch": "main",
        "milestone": {
            "id": "theorem-u",
            "title": "Theorem U -- Lambda uniqueness (conditional)",
            "module": "Lutar.Uniqueness",
            "status": EXPECTED_STATUS,
            "headline_decls": ["TheoremU_LambdaUnique"],
            "kernel_only": True,
        },
        "honesty": {
            "doctrine": "v11",
            "theorem_u": (
                "REAL-conditional: kernel-verified but CONDITIONAL on its stated "
                "hypotheses; NOT part of the locked-proven baseline."
            ),
            "conjecture_1": (
                "OPEN: unconditional Lambda uniqueness is Conjecture 1 and is "
                "machine-checked FALSE as stated."
            ),
            "locked_set": list(locked_evidence["locked_ids"]),
        },
    }

    good["locked_formula_evidence"] = locked_evidence

    def mutate(**patch_paths) -> dict:
        """Deep-copy `good` then apply dotted-path overrides."""
        d = json.loads(json.dumps(good))
        for dotted, value in patch_paths.items():
            keys = dotted.split(".")
            ref = d
            for k in keys[:-1]:
                ref = ref[k]
            if value is _DELETE:
                ref.pop(keys[-1], None)
            else:
                ref[keys[-1]] = value
        return d

    def write(dirpath: Path, content: str, name: str = "theorem_u_snapshot.json") -> None:
        (dirpath / name).write_text(content, encoding="utf-8")

    cases: list[tuple[str, object, int]] = [
        ("good", lambda d: write(d, json.dumps(good)), 0),
        ("missing-artifact(empty-dir)", lambda d: None, 1),
        ("empty-file", lambda d: write(d, ""), 1),
        ("not-json", lambda d: write(d, "not json {"), 1),
        ("not-object", lambda d: write(d, json.dumps([1, 2, 3])), 1),
        ("wrong-schema", lambda d: write(d, json.dumps(mutate(schema="szl.bogus/v9"))), 1),
        ("wrong-kind", lambda d: write(d, json.dumps(mutate(kind="conjecture-2"))), 1),
        ("status-overclaim", lambda d: write(d, json.dumps(mutate(**{"milestone.status": "PROVEN"}))), 1),
        ("kernel-not-clean", lambda d: write(d, json.dumps(mutate(**{"milestone.kernel_only": False}))), 1),
        ("empty-headline", lambda d: write(d, json.dumps(mutate(**{"milestone.headline_decls": []}))), 1),
        ("missing-milestone", lambda d: write(d, json.dumps(mutate(milestone=_DELETE))), 1),
        ("retired-locked-five-flag", lambda d: write(d, json.dumps(mutate(**{"honesty.locked_five_unchanged": True}))), 1),
        ("missing-locked-evidence", lambda d: write(d, json.dumps(mutate(locked_formula_evidence=_DELETE))), 1),
        ("wrong-evidence-commit", lambda d: write(d, json.dumps(mutate(**{"locked_formula_evidence.source_commit": "1" * 40}))), 1),
        ("five-set-regression", lambda d: write(d, json.dumps(mutate(**{"honesty.locked_set": ["F1", "F11", "F12", "F18", "F19"]}))), 1),
        ("missing-locked-set", lambda d: write(d, json.dumps(mutate(**{"honesty.locked_set": _DELETE}))), 1),
        ("locked-set-shrunk", lambda d: write(d, json.dumps(mutate(**{"honesty.locked_set": ["F1", "F11", "F12", "F18"]}))), 1),
        ("locked-set-grown", lambda d: write(d, json.dumps(mutate(**{"honesty.locked_set": ["F1", "F11", "F12", "F18", "F19", "F20"]}))), 1),
        ("theorem-u-overclaim", lambda d: write(d, json.dumps(mutate(**{"honesty.theorem_u": "PROVEN unconditionally."}))), 1),
        ("conjecture1-closed", lambda d: write(d, json.dumps(mutate(**{"honesty.conjecture_1": "CLOSED: Lambda uniqueness is now proven."}))), 1),
        ("missing-honesty", lambda d: write(d, json.dumps(mutate(honesty=_DELETE))), 1),
    ]

    for name, setup, expected in cases:
        with tempfile.TemporaryDirectory() as tmp:
            dirpath = Path(tmp)
            setup(dirpath)  # type: ignore[operator]
            rc = check_dir(dirpath)
            if rc != expected:
                failures.append(f"{name}: expected rc={expected}, got rc={rc}")

    # A directory path that does not exist at all.
    rc = check_dir(Path(tempfile.gettempdir()) / "theorem-u-snapshot-does-not-exist-404")
    if rc != 1:
        failures.append(f"nonexistent-dir: expected rc=1, got rc={rc}")

    if failures:
        print("::error::self-test FAILED — the snapshot validator is not trustworthy:")
        for f in failures:
            print(f"  - {f}")
        return 1
    print(
        "[theorem-u-snapshot-guard] self-test passed: validator accepts the honest "
        "snapshot and rejects missing / empty / malformed / dishonest ones "
        "(status overclaim, locked-set drift, Conjecture-1 closed, etc.)."
    )
    return 0


class _Delete:
    """Sentinel for self-test mutation: remove the key entirely."""


_DELETE = _Delete()


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--dir", help="directory holding the downloaded snapshot artifact")
    ap.add_argument("--snapshot", help="explicit path to the snapshot JSON file")
    ap.add_argument("--expected-commit", help="full source workflow HEAD SHA")
    ap.add_argument("--source-root", type=Path, help="read-only checkout of that source revision")
    ap.add_argument(
        "--selftest",
        action="store_true",
        help="run built-in positive/negative fixtures and exit (no real artifact needed)",
    )
    args = ap.parse_args(argv)

    if args.selftest:
        return _selftest()
    if args.snapshot:
        path = Path(args.snapshot)
        if not path.exists():
            print(f"::error::snapshot file '{path}' does not exist (artifact not produced).")
            return 1
        problems = validate_snapshot_file(path, args.expected_commit, source_root=args.source_root)
        if problems:
            for problem in problems:
                print(f"::error::{path.name}: {problem}")
            return 1
        print(f"[theorem-u-snapshot-guard] OK: {path.name} is non-empty, well-formed and honest.")
        return 0
    if args.dir:
        return check_dir(Path(args.dir), args.expected_commit, source_root=args.source_root)
    ap.error("one of --dir, --snapshot or --selftest is required")
    return 2  # unreachable; argparse.error exits 2


if __name__ == "__main__":
    raise SystemExit(main())
