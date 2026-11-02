#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Negative and positive tests for the locked-formula evidence builder."""

from __future__ import annotations

import importlib.util
import json
import os
import sys
from copy import deepcopy
from unittest import mock


TEST_DIR = os.path.dirname(os.path.abspath(__file__))
REPO_ROOT = os.path.dirname(TEST_DIR)
BUILDER_PATH = os.path.join(
    REPO_ROOT, ".github", "scripts", "build_locked_formula_evidence.py"
)
CLAIM_PATH = os.path.join(REPO_ROOT, "claims", "locked-formulas.v1.json")


def _load_builder():
    spec = importlib.util.spec_from_file_location("build_locked_formula_evidence", BUILDER_PATH)
    assert spec and spec.loader, f"cannot load builder from {BUILDER_PATH}"
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


builder = _load_builder()
with open(CLAIM_PATH, encoding="utf-8") as handle:
    CLAIM_MAP = json.load(handle)


def _records():
    trust_base = CLAIM_MAP["trust_base"]
    result = []
    for claim in CLAIM_MAP["claims"]:
        for bare in claim["theorem_declarations"]:
            result.append({
                "tool": "lean.query_axioms",
                "theorem": "Puriq.Formula.Proved." + bare,
                "axioms": [],
                "allowed": True,
                "trust_base": trust_base,
            })
    return result


def _text(records):
    return "\n".join(
        "trace prefix: GEH_GUARD " + json.dumps(row, separators=(",", ":"))
        for row in records
    )


def _expect_failure(records, needle: str):
    try:
        builder.build_manifest(
            builder.Path(REPO_ROOT),
            _text(records),
            allow_dirty_inputs=True,
        )
    except builder.EvidenceError as exc:
        assert needle in str(exc), exc
    else:
        raise AssertionError(f"expected EvidenceError containing {needle!r}")


def test_valid_manifest_binds_every_claim_and_carrier():
    manifest = builder.build_manifest(
        builder.Path(REPO_ROOT),
        _text(_records()),
        allow_dirty_inputs=True,
    )
    assert manifest["schema"] == builder.SCHEMA
    assert manifest["locked_ids"] == CLAIM_MAP["locked_ids"]
    assert manifest["carrier_theorem_count"] == 24
    assert len(manifest["claims"]) == 8
    carriers = [
        carrier
        for claim in manifest["claims"]
        for carrier in claim["carriers"]
    ]
    assert len(carriers) == 24
    assert len({carrier["theorem"] for carrier in carriers}) == 24
    assert all(carrier["allowed"] is True for carrier in carriers)
    assert manifest["evidence_digest"].startswith("sha256:")
    assert len(manifest["inputs"]) == 5
    assert builder.BUILDER_PATH.as_posix() in manifest["inputs"]
    assert isinstance(manifest["input_files_match_head"], bool)


def test_dirty_evidence_inputs_require_explicit_local_override():
    with mock.patch.object(builder, "inputs_match_head", return_value=False):
        try:
            builder.build_manifest(builder.Path(REPO_ROOT), _text(_records()))
        except builder.EvidenceError as exc:
            assert "evidence inputs differ from HEAD" in str(exc), exc
        else:
            raise AssertionError("dirty evidence inputs must fail without an override")


def test_missing_kernel_record_fails_closed():
    _expect_failure(_records()[:-1], "expected 24 guard records")


def test_duplicate_kernel_record_fails_closed():
    rows = _records()
    rows[-1] = deepcopy(rows[0])
    _expect_failure(rows, "duplicate guard theorem")


def test_disallowed_axiom_result_fails_closed():
    rows = _records()
    rows[0]["allowed"] = False
    rows[0]["axioms"] = ["sorryAx"]
    _expect_failure(rows, "kernel axiom result is not allowed")


def test_emitted_trust_base_must_match_claim_map():
    rows = _records()
    rows[0]["trust_base"] = ["propext", "sorryAx"]
    _expect_failure(rows, "does not match claim-map trust base")


def test_unexpected_namespace_fails_closed():
    rows = _records()
    rows[0]["theorem"] = "Other.Namespace.f1_replay_hash_determinism"
    _expect_failure(rows, "unexpected locked theorem namespace")


if __name__ == "__main__":
    failures = 0
    for name, function in sorted(globals().items()):
        if name.startswith("test_") and callable(function):
            try:
                function()
                print(f"PASS {name}")
            except AssertionError as exc:
                failures += 1
                print(f"FAIL {name}: {exc}")
    sys.exit(1 if failures else 0)
