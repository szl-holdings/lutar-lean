#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 SZL Holdings
"""Bind snapshot locked IDs to the canonical claim map and recorded kernel evidence.

This validates identity and the recorded axiom footprints. It does not run Lean;
the build workflow supplies the revision-bound evidence after its kernel guard.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re

from build_locked_formula_evidence import (
    BUILDER_PATH, CLAIM_MAP_PATH, COMPILED_PATH, GUARD_PATH, TOOLCHAIN_PATH,
    EvidenceError, SCHEMA, load_json, sha256_file,
)

REPO_ROOT = Path(__file__).resolve().parents[2]
INPUT_PATHS = (BUILDER_PATH, CLAIM_MAP_PATH, COMPILED_PATH, GUARD_PATH, TOOLCHAIN_PATH)


def evidence_digest(evidence: dict) -> str:
    payload = {key: value for key, value in evidence.items() if key != "evidence_digest"}
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return "sha256:" + hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def validate_locked_evidence(evidence: object, commit: object, repository: object) -> list[str]:
    """Validate against the checked-out canonical inputs; missing data fails closed."""
    problems: list[str] = []
    try:
        claims = load_json(REPO_ROOT / CLAIM_MAP_PATH)
        expected_inputs = {
            path.as_posix(): sha256_file(REPO_ROOT / path) for path in INPUT_PATHS
        }
    except (EvidenceError, OSError) as exc:
        return [f"canonical locked evidence inputs are unavailable: {exc}"]
    if not isinstance(evidence, dict):
        return ["missing/invalid locked_formula_evidence object"]
    if evidence.get("schema") != SCHEMA:
        problems.append("locked evidence schema is invalid")
    if not isinstance(commit, str) or not re.fullmatch(r"[0-9a-f]{40}", commit):
        problems.append("snapshot kernel_commit must be a full Git SHA")
    if evidence.get("source_commit") != commit:
        problems.append("locked evidence source_commit differs from snapshot kernel_commit")
    if evidence.get("repository") != repository or repository != claims.get("repository"):
        problems.append("locked evidence repository differs from the canonical claim map")
    if evidence.get("input_files_match_head") is not True:
        problems.append("locked evidence inputs must match the recorded HEAD")
    if evidence.get("inputs") != expected_inputs:
        problems.append("locked evidence input digests differ from canonical source files")
    if evidence.get("evidence_digest") != evidence_digest(evidence):
        problems.append("locked evidence digest is invalid")
    if evidence.get("kernel_query_tool") != "Lean.collectAxioms":
        problems.append("locked evidence must record Lean.collectAxioms")
    if evidence.get("lean_toolchain") != claims.get("lean_toolchain"):
        problems.append("locked evidence toolchain differs from the canonical claim map")

    locked = claims.get("locked_ids")
    rows = claims.get("claims")
    if (
        not isinstance(locked, list) or not locked
        or not all(isinstance(item, str) for item in locked)
        or len(locked) != len(set(locked))
        or not isinstance(rows, list)
        or any(not isinstance(row, dict) for row in rows)
        or [row.get("claim_id") for row in rows] != locked
    ):
        return problems + ["canonical locked claim map is malformed"]
    if evidence.get("locked_ids") != locked:
        problems.append("locked evidence IDs differ from canonical locked_ids")
    trust_base = claims.get("trust_base")
    if evidence.get("trust_base") != trust_base or not isinstance(trust_base, list):
        return problems + ["locked evidence trust base differs from canonical policy"]
    expected_count = claims.get("carrier_theorem_count")
    if evidence.get("carrier_theorem_count") != expected_count:
        problems.append("locked evidence carrier count differs from canonical policy")
    observed = evidence.get("claims")
    if not isinstance(observed, list) or len(observed) != len(rows):
        return problems + ["locked evidence must cover every canonical claim"]
    total = 0
    seen: set[str] = set()
    for expected, actual in zip(rows, observed):
        if not isinstance(actual, dict) or actual.get("claim_id") != expected["claim_id"]:
            problems.append("locked evidence claim order/identity differs from canonical policy")
            continue
        names = expected.get("theorem_declarations")
        carriers = actual.get("carriers")
        if not isinstance(names, list) or not isinstance(carriers, list) or len(carriers) != len(names):
            problems.append(f"{expected['claim_id']}: missing or unexpected carrier evidence")
            continue
        for name, carrier in zip(names, carriers):
            total += 1
            fqn = "Puriq.Formula.Proved." + name
            if not isinstance(carrier, dict) or carrier.get("theorem") != fqn or fqn in seen:
                problems.append(f"{expected['claim_id']}: carrier identity is invalid or duplicated")
                continue
            seen.add(fqn)
            axioms = carrier.get("axioms")
            if (
                carrier.get("allowed") is not True or not isinstance(axioms, list)
                or not all(isinstance(axiom, str) and axiom in trust_base for axiom in axioms)
            ):
                problems.append(f"{fqn}: axiom evidence escapes canonical policy")
    if total != expected_count:
        problems.append("locked evidence does not cover the canonical carrier count")
    return problems


def validate_snapshot_locked_binding(snapshot: dict) -> list[str]:
    evidence = snapshot.get("locked_formula_evidence")
    problems = validate_locked_evidence(
        evidence, snapshot.get("kernel_commit"), snapshot.get("repo")
    )
    honesty = snapshot.get("honesty")
    if not isinstance(honesty, dict):
        return problems + ["missing/invalid honesty object"]
    if "locked_five_unchanged" in honesty:
        problems.append("retired locked_five_unchanged assertion is not current evidence")
    if not isinstance(evidence, dict) or honesty.get("locked_set") != evidence.get("locked_ids"):
        problems.append("honesty.locked_set must exactly match the bound locked evidence")
    return problems
