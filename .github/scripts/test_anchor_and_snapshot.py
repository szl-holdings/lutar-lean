#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# © 2026 Lutar, Stephen P. — SZL Holdings · ORCID 0009-0001-0110-4173
"""Self-test: the proof-snapshot build + szl-lake anchor invariants never regress.

The snapshot/anchor pipeline (`build_proof_snapshot.py` -> `anchor_szl_lake.py`)
was generalized from a Theorem-U-only path to an any-milestone path. Three
contracts are easy to break in a future edit and nothing else in CI guards them:

  (1) BACK-COMPAT — running `build_proof_snapshot.py` with DEFAULT inputs
      (`--kind theorem-u`) must still reproduce the original Theorem-U snapshot
      SHAPE: schema `szl.proof.snapshot/v1`, kind `theorem-u`, the full Theorem-U
      headline-decl pack, milestone.status `REAL-conditional` + kernel_only True,
      and the intact honesty block (locked_set {F1,F11,F12,F18,F19}, Theorem U
      conditional, Conjecture 1 OPEN / machine-checked FALSE). This is the subject
      `lake-build.yml` uploads and the live szl-lake receipt #1 was minted from, so
      its shape must stay stable. We additionally feed the result through the
      existing `check_theorem_u_snapshot.py` validator so the two stay in lockstep.

  (2) HONESTY DOCTRINE — the build must REFUSE (exit non-zero) any `--kind` that
      has no per-snapshot honesty block. A milestone may never be anchored without
      stating its own truthful status; supplying an honesty block lets it proceed.

  (3) ANCHOR CHAIN MATH + IDEMPOTENCY — `anchor_szl_lake.py` must keep
      chain_index = len(existing)+1, prev_hash = the previous tail receipt_id
      (None at genesis), and treat (kind, kernel_commit, snapshot_sha) as the
      idempotency tuple that makes a re-anchor a no-op. canonical_hash must be
      order-independent (sorted-keys) so receipt ids are stable.

Pure stdlib; no network, no Lean toolchain, no signing. Exit 0 = all hold.
"""
from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent
BUILD = SCRIPTS_DIR / "build_proof_snapshot.py"

# Import the sibling scripts as modules for in-process assertions.
sys.path.insert(0, str(SCRIPTS_DIR))
import anchor_szl_lake as A  # noqa: E402
import check_theorem_u_snapshot as G  # noqa: E402

# The Theorem-U headline pack the default profile must always emit.
THEOREM_U_HEADLINE = sorted([
    "TheoremU_LambdaUnique",
    "TheoremU_LambdaUnique_eq",
    "CorollaryU1_LambdaUnique_Separable",
    "CorollaryU2_LambdaUnique_Factors",
    "identifiability_forces_lambda",
    "lambda_equiv_to_eq_of_anchored",
])
EXPECTED_LOCKED_SET = {"F1", "F11", "F12", "F18", "F19"}


def _write(path: Path, text: str) -> None:
    path.write_text(text, encoding="utf-8")


def _fixtures(tmp: Path):
    """Build kernel-clean inputs covering the Theorem-U headline pack."""
    decls = ["Lutar.Uniqueness." + s for s in THEOREM_U_HEADLINE]
    # #print axioms shape; only Lean/Mathlib trust-base axioms so kernel_only holds.
    lines = [f"'{d}' depends on axioms: [propext, Classical.choice]" for d in decls]
    ax = tmp / "axiomcheck.out"
    _write(ax, "\n".join(lines) + "\n")
    numbers = tmp / "lean_numbers.measured.json"
    _write(numbers, json.dumps({
        "schema": "szl.lean.numbers/v1",
        "numbers": {"declarations": 1234, "axioms_unique": 4, "sorries_noncomment": 0},
    }))
    refvec = tmp / "reference-vectors.json"
    _write(refvec, json.dumps({"vectors": []}))
    # Empty pack dir => decl_source_sha256 is deterministic + repo-layout-independent.
    packdir = tmp / "emptypack"
    packdir.mkdir()
    return ax, numbers, refvec, packdir


def _run_build(tmp: Path, extra_args: list[str]):
    ax, numbers, refvec, packdir = _fixtures(tmp)
    out = tmp / "snapshot.json"
    cmd = [
        sys.executable, str(BUILD),
        "--axiomcheck-out", str(ax),
        "--numbers", str(numbers),
        "--reference-vectors", str(refvec),
        "--pack-dir", str(packdir),
        "--out", str(out),
        "--commit", "0" * 40,
        "--branch", "main",
    ] + extra_args
    proc = subprocess.run(cmd, capture_output=True, text=True)
    return proc, out


# --------------------------------------------------------------------------- #
# (1) back-compat: default --kind theorem-u reproduces the canonical shape.
# --------------------------------------------------------------------------- #
def test_default_theorem_u_shape() -> None:
    with tempfile.TemporaryDirectory() as t:
        tmp = Path(t)
        proc, out = _run_build(tmp, [])  # default kind == theorem-u
        assert proc.returncode == 0, (
            f"default build must succeed; rc={proc.returncode}\n{proc.stderr}"
        )
        assert out.exists(), "default build produced no snapshot file"
        snap = json.loads(out.read_text(encoding="utf-8"))

        assert snap.get("schema") == "szl.proof.snapshot/v1", snap.get("schema")
        assert snap.get("kind") == "theorem-u", snap.get("kind")

        m = snap.get("milestone", {})
        assert m.get("status") == "REAL-conditional", m.get("status")
        assert m.get("kernel_only") is True, m.get("kernel_only")
        assert m.get("headline_decls") == THEOREM_U_HEADLINE, m.get("headline_decls")

        h = snap.get("honesty", {})
        assert h.get("locked_five_unchanged") is True, h.get("locked_five_unchanged")
        assert set(h.get("locked_set", [])) == EXPECTED_LOCKED_SET, h.get("locked_set")
        assert "REAL-conditional" in (h.get("theorem_u") or ""), h.get("theorem_u")
        conj = (h.get("conjecture_1") or "")
        assert "OPEN" in conj and "FALSE" in conj, conj

        # Lockstep with the published-snapshot guard: it must accept this build.
        problems = G.validate_snapshot_file(out)
        assert not problems, f"existing snapshot guard rejected the default build: {problems}"


# --------------------------------------------------------------------------- #
# (2) honesty doctrine: a kind with no honesty block is refused; with one, ok.
# --------------------------------------------------------------------------- #
def test_kind_without_honesty_is_refused() -> None:
    with tempfile.TemporaryDirectory() as t:
        tmp = Path(t)
        proc, out = _run_build(tmp, ["--kind", "conjecture-2-no-honesty"])
        assert proc.returncode != 0, (
            "build of a kind with NO honesty block must exit non-zero"
        )
        blob = (proc.stderr or "") + (proc.stdout or "")
        assert "honesty block" in blob, f"expected an honesty-block refusal, got:\n{blob}"
        assert not out.exists(), "refused build must not write a snapshot file"


def test_kind_with_honesty_is_allowed() -> None:
    """Proves the refusal is specifically about the honesty block, not the kind."""
    with tempfile.TemporaryDirectory() as t:
        tmp = Path(t)
        honesty = tmp / "honesty.json"
        _write(honesty, json.dumps({
            "doctrine": "v11",
            "status_note": "REAL-invariant: kernel-verified meta-theorem; not a formula proof.",
        }))
        proc, out = _run_build(tmp, [
            "--kind", "conjecture-2-demo",
            "--module", "Lutar.Demo",
            "--status", "REAL-invariant",
            "--honesty-file", str(honesty),
            "--no-require-headline",
        ])
        assert proc.returncode == 0, (
            f"a kind WITH an honesty block must build; rc={proc.returncode}\n{proc.stderr}"
        )
        snap = json.loads(out.read_text(encoding="utf-8"))
        assert snap.get("kind") == "conjecture-2-demo", snap.get("kind")
        assert snap.get("honesty", {}).get("doctrine") == "v11"


# --------------------------------------------------------------------------- #
# (3) anchor chain math + idempotency tuple.
# --------------------------------------------------------------------------- #
def test_chain_position_genesis_and_advance() -> None:
    assert A.chain_position([]) == (1, None), "genesis must be index 1, prev_hash None"
    existing = [
        {"receipt_id": "r1", "chain_index": 1},
        {"receipt_id": "r2", "chain_index": 2},
    ]
    assert A.chain_position(existing) == (3, "r2"), (
        "chain_index must be len+1 and prev_hash the tail receipt_id"
    )


def test_idempotency_tuple() -> None:
    recs = [{
        "kind": "theorem-u-anchor",
        "kernel_commit": "abc123",
        "subject": {"sha256": "deadbeef"},
        "chain_index": 1,
        "receipt_id": "r1",
    }]
    # Exact (kind, kernel_commit, snapshot_sha) match -> no-op record returned.
    assert A.find_existing_anchor(recs, "theorem-u-anchor", "abc123", "deadbeef") is recs[0]
    # Any single field differing -> not a match (must re-anchor).
    assert A.find_existing_anchor(recs, "theorem-u-anchor", "abc123", "other") is None
    assert A.find_existing_anchor(recs, "locked-baseline-anchor", "abc123", "deadbeef") is None
    assert A.find_existing_anchor(recs, "theorem-u-anchor", "xyz999", "deadbeef") is None
    assert A.find_existing_anchor([], "theorem-u-anchor", "abc123", "deadbeef") is None


def test_canonical_hash_order_independent() -> None:
    h1 = A.canonical_hash({"a": 1, "b": {"y": 2, "x": 1}})
    h2 = A.canonical_hash({"b": {"x": 1, "y": 2}, "a": 1})
    assert h1 == h2, "canonical_hash must be key-order independent"
    assert h1 != A.canonical_hash({"a": 1, "b": {"y": 2, "x": 2}}), (
        "canonical_hash must change when content changes"
    )


TESTS = [
    ("default theorem-u snapshot shape (back-compat)", test_default_theorem_u_shape),
    ("kind without honesty block is refused", test_kind_without_honesty_is_refused),
    ("kind with honesty block is allowed", test_kind_with_honesty_is_allowed),
    ("anchor chain_position genesis + advance", test_chain_position_genesis_and_advance),
    ("anchor idempotency tuple", test_idempotency_tuple),
    ("canonical_hash order independence", test_canonical_hash_order_independent),
]


def main() -> int:
    failures: list[str] = []
    for name, fn in TESTS:
        try:
            fn()
            print(f"[snapshot-anchor-selftest] PASS: {name}")
        except AssertionError as exc:
            failures.append(f"{name}: {exc}")
            print(f"[snapshot-anchor-selftest] FAIL: {name}: {exc}")
        except Exception as exc:  # noqa: BLE001 - any error is a guard failure
            failures.append(f"{name}: unexpected {type(exc).__name__}: {exc}")
            print(f"[snapshot-anchor-selftest] ERROR: {name}: {exc}")

    if failures:
        print("::error::snapshot/anchor self-test FAILED — the pipeline regressed:")
        for f in failures:
            print(f"  - {f}")
        return 1
    print(
        "[snapshot-anchor-selftest] all invariants hold: default build reproduces the "
        "Theorem-U snapshot shape, a kind with no honesty block is refused, and the "
        "anchor chain math + idempotency tuple are intact."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
