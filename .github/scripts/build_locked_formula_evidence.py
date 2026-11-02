#!/usr/bin/env python3
"""Build a revision-bound locked-formula evidence manifest from Lean output.

``tools/lean/LockedGuard.lean`` asks the Lean kernel for the axiom footprint of
each locked carrier and emits one ``GEH_GUARD`` JSON record per theorem.  This
script turns that transient log into a deterministic manifest that binds:

* the eight stable formula IDs;
* their exact fully-qualified carrier declarations;
* the kernel-emitted axiom set for every carrier;
* the pinned Lean toolchain and human-owned trust base; and
* the Git revision plus byte digests of every evidence input.

It fails closed on missing, duplicate, unexpected, disallowed, or malformed
records.  It does not replay or approximate Lean's kernel result.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path
from typing import Any


SCHEMA = "szl.lutar.locked-formula-evidence/v1"
BUILDER_PATH = Path(".github/scripts/build_locked_formula_evidence.py")
CLAIM_MAP_PATH = Path("claims/locked-formulas.v1.json")
COMPILED_PATH = Path("Lutar/Puriq/Formulas/ProvedFormulas.lean")
GUARD_PATH = Path("tools/lean/LockedGuard.lean")
TOOLCHAIN_PATH = Path("lean-toolchain")
GUARD_MARKER = "GEH_GUARD "


class EvidenceError(ValueError):
    """The supplied kernel evidence does not satisfy the locked contract."""


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise EvidenceError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=_unique_object)
    except (OSError, json.JSONDecodeError) as exc:
        raise EvidenceError(f"cannot read {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise EvidenceError(f"{path} root must be an object")
    return value


def sha256_file(path: Path) -> str:
    try:
        payload = path.read_bytes()
    except OSError as exc:
        raise EvidenceError(f"cannot hash {path}: {exc}") from exc
    return "sha256:" + hashlib.sha256(payload).hexdigest()


def parse_guard_output(text: str) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    seen: set[str] = set()
    for line_number, raw in enumerate(text.splitlines(), start=1):
        marker_at = raw.find(GUARD_MARKER)
        if marker_at < 0:
            continue
        encoded = raw[marker_at + len(GUARD_MARKER):].strip()
        try:
            record = json.loads(encoded, object_pairs_hook=_unique_object)
        except (json.JSONDecodeError, EvidenceError) as exc:
            raise EvidenceError(f"malformed guard JSON on line {line_number}: {exc}") from exc
        if not isinstance(record, dict):
            raise EvidenceError(f"guard record on line {line_number} must be an object")
        theorem = record.get("theorem")
        if not isinstance(theorem, str) or not theorem:
            raise EvidenceError(f"guard record on line {line_number} has no theorem")
        if theorem in seen:
            raise EvidenceError(f"duplicate guard theorem {theorem}")
        seen.add(theorem)
        if record.get("tool") != "lean.query_axioms":
            raise EvidenceError(f"{theorem}: unexpected tool {record.get('tool')!r}")
        if record.get("allowed") is not True:
            raise EvidenceError(f"{theorem}: kernel axiom result is not allowed")
        axioms = record.get("axioms")
        trust_base = record.get("trust_base")
        if not isinstance(axioms, list) or not all(isinstance(item, str) for item in axioms):
            raise EvidenceError(f"{theorem}: axioms must be a string list")
        if not isinstance(trust_base, list) or not all(isinstance(item, str) for item in trust_base):
            raise EvidenceError(f"{theorem}: trust_base must be a string list")
        if len(axioms) != len(set(axioms)):
            raise EvidenceError(f"{theorem}: duplicate axiom name")
        if len(trust_base) != len(set(trust_base)):
            raise EvidenceError(f"{theorem}: duplicate trust-base name")
        if not set(axioms).issubset(trust_base):
            raise EvidenceError(f"{theorem}: axiom set is outside its emitted trust base")
        records.append(record)
    if not records:
        raise EvidenceError("no GEH_GUARD records found")
    return records


def git_value(repo_root: Path, *args: str) -> str:
    completed = subprocess.run(
        ["git", "-C", str(repo_root), *args],
        capture_output=True,
        text=True,
        check=False,
        timeout=30,
    )
    if completed.returncode:
        raise EvidenceError(completed.stderr.strip() or f"git {' '.join(args)} failed")
    return completed.stdout.strip()


def _claim_rows(claim_map: dict[str, Any]) -> list[dict[str, Any]]:
    claims = claim_map.get("claims")
    locked_ids = claim_map.get("locked_ids")
    if not isinstance(claims, list) or not isinstance(locked_ids, list):
        raise EvidenceError("claim map must contain list-valued claims and locked_ids")
    if [row.get("claim_id") for row in claims if isinstance(row, dict)] != locked_ids:
        raise EvidenceError("claim rows must exactly match locked_ids in order")
    if len(locked_ids) != len(set(locked_ids)):
        raise EvidenceError("locked_ids contains duplicates")
    return claims


def inputs_match_head(repo_root: Path, paths: tuple[Path, ...]) -> bool:
    completed = subprocess.run(
        [
            "git", "-C", str(repo_root), "diff", "--quiet", "HEAD", "--",
            *(path.as_posix() for path in paths),
        ],
        capture_output=True,
        text=True,
        check=False,
        timeout=30,
    )
    if completed.returncode == 0:
        return True
    if completed.returncode == 1:
        return False
    raise EvidenceError(completed.stderr.strip() or "cannot compare evidence inputs to HEAD")


def build_manifest(
    repo_root: Path,
    guard_text: str,
    *,
    allow_dirty_inputs: bool = False,
) -> dict[str, Any]:
    repo_root = repo_root.resolve()
    claim_path = repo_root / CLAIM_MAP_PATH
    compiled_path = repo_root / COMPILED_PATH
    guard_path = repo_root / GUARD_PATH
    toolchain_path = repo_root / TOOLCHAIN_PATH
    claim_map = load_json(claim_path)
    claims = _claim_rows(claim_map)
    records = parse_guard_output(guard_text)

    if claim_map.get("schema") != "szl.lutar.locked-formula-claims/v1":
        raise EvidenceError("unexpected claim-map schema")
    if claim_map.get("compiled_path") != COMPILED_PATH.as_posix():
        raise EvidenceError("claim-map compiled_path does not match the evidence input")
    if claim_map.get("guard_path") != GUARD_PATH.as_posix():
        raise EvidenceError("claim-map guard_path does not match the evidence input")
    try:
        toolchain = toolchain_path.read_text(encoding="utf-8").strip()
    except OSError as exc:
        raise EvidenceError(f"cannot read {TOOLCHAIN_PATH}: {exc}") from exc
    if not toolchain or claim_map.get("lean_toolchain") != toolchain:
        raise EvidenceError("claim-map lean_toolchain does not match lean-toolchain")

    expected_count = claim_map.get("carrier_theorem_count")
    if not isinstance(expected_count, int) or expected_count <= 0:
        raise EvidenceError("carrier_theorem_count must be a positive integer")
    if len(records) != expected_count:
        raise EvidenceError(f"expected {expected_count} guard records, found {len(records)}")

    expected_trust_base = claim_map.get("trust_base")
    if not isinstance(expected_trust_base, list) or not all(
        isinstance(item, str) for item in expected_trust_base
    ):
        raise EvidenceError("claim-map trust_base must be a string list")
    if len(expected_trust_base) != len(set(expected_trust_base)):
        raise EvidenceError("claim-map trust_base contains duplicates")

    by_bare: dict[str, dict[str, Any]] = {}
    for record in records:
        theorem = record["theorem"]
        prefix = "Puriq.Formula.Proved."
        if not theorem.startswith(prefix) or theorem == prefix:
            raise EvidenceError(f"unexpected locked theorem namespace: {theorem}")
        bare = theorem[len(prefix):]
        if bare in by_bare:
            raise EvidenceError(f"duplicate bare carrier name {bare}")
        if record["trust_base"] != expected_trust_base:
            raise EvidenceError(
                f"{theorem}: emitted trust base {record['trust_base']} does not "
                f"match claim-map trust base {expected_trust_base}"
            )
        by_bare[bare] = record

    evidence_claims: list[dict[str, Any]] = []
    expected_bare: list[str] = []
    for claim in claims:
        if not isinstance(claim, dict):
            raise EvidenceError("claim row must be an object")
        claim_id = claim.get("claim_id")
        declarations = claim.get("theorem_declarations")
        if not isinstance(claim_id, str) or not isinstance(declarations, list) or not declarations:
            raise EvidenceError(f"{claim_id!r}: theorem_declarations must be a non-empty list")
        carriers: list[dict[str, Any]] = []
        for bare in declarations:
            if not isinstance(bare, str) or not bare:
                raise EvidenceError(f"{claim_id}: invalid carrier name {bare!r}")
            if bare in expected_bare:
                raise EvidenceError(f"carrier {bare} is assigned to more than one claim")
            expected_bare.append(bare)
            record = by_bare.get(bare)
            if record is None:
                raise EvidenceError(f"{claim_id}: no kernel evidence for carrier {bare}")
            carriers.append({
                "theorem": record["theorem"],
                "axioms": record["axioms"],
                "allowed": True,
            })
        evidence_claims.append({"claim_id": claim_id, "carriers": carriers})

    unexpected = sorted(set(by_bare) - set(expected_bare))
    if unexpected:
        raise EvidenceError(f"unexpected kernel evidence carriers: {unexpected}")
    if len(expected_bare) != expected_count:
        raise EvidenceError(
            f"claim map assigns {len(expected_bare)} carriers; expected {expected_count}"
        )

    input_paths = (
        BUILDER_PATH,
        CLAIM_MAP_PATH,
        COMPILED_PATH,
        GUARD_PATH,
        TOOLCHAIN_PATH,
    )
    for relative in input_paths:
        if not (repo_root / relative).is_file():
            raise EvidenceError(f"evidence input is missing: {relative}")
    matches_head = inputs_match_head(repo_root, input_paths)
    if not matches_head and not allow_dirty_inputs:
        raise EvidenceError(
            "evidence inputs differ from HEAD; commit them or use "
            "--allow-dirty-inputs for a local non-release receipt"
        )
    source_commit = git_value(repo_root, "rev-parse", "HEAD")
    source_tree = git_value(repo_root, "rev-parse", "HEAD^{tree}")
    manifest: dict[str, Any] = {
        "schema": SCHEMA,
        "repository": claim_map.get("repository"),
        "source_commit": source_commit,
        "source_tree": source_tree,
        "input_files_match_head": matches_head,
        "lean_toolchain": toolchain,
        "locked_ids": claim_map["locked_ids"],
        "carrier_theorem_count": expected_count,
        "trust_base": expected_trust_base,
        "kernel_query_tool": "Lean.collectAxioms",
        "inputs": {
            BUILDER_PATH.as_posix(): sha256_file(repo_root / BUILDER_PATH),
            CLAIM_MAP_PATH.as_posix(): sha256_file(claim_path),
            COMPILED_PATH.as_posix(): sha256_file(compiled_path),
            GUARD_PATH.as_posix(): sha256_file(guard_path),
            TOOLCHAIN_PATH.as_posix(): sha256_file(toolchain_path),
        },
        "claims": evidence_claims,
        "limitations": [
            "This manifest records Lean kernel axiom dependencies for the named declarations.",
            "It does not establish runtime refinement, empirical validity, deployment, or authorization.",
        ],
    }
    canonical = json.dumps(manifest, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    manifest["evidence_digest"] = "sha256:" + hashlib.sha256(canonical.encode("utf-8")).hexdigest()
    return manifest


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-path", type=Path, default=Path("."))
    parser.add_argument("--guard-output", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument(
        "--allow-dirty-inputs",
        action="store_true",
        help="permit a local manifest whose evidence inputs differ from HEAD",
    )
    args = parser.parse_args(argv)
    try:
        guard_text = args.guard_output.read_text(encoding="utf-8")
        manifest = build_manifest(
            args.repo_path,
            guard_text,
            allow_dirty_inputs=args.allow_dirty_inputs,
        )
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(
            json.dumps(manifest, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )
    except (OSError, EvidenceError) as exc:
        print(f"locked-formula evidence: FAIL: {exc}", file=sys.stderr)
        return 1
    print(
        "locked-formula evidence: OK: "
        f"{manifest['carrier_theorem_count']} carriers / "
        f"{len(manifest['locked_ids'])} claims / {manifest['evidence_digest']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
