#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# © 2026 Lutar, Stephen P. — SZL Holdings · ORCID 0009-0001-0110-4173
"""Self-test: the proof-snapshot build + szl-lake anchor invariants never regress.

The snapshot/anchor pipeline (`build_proof_snapshot.py` -> `anchor_szl_lake.py`)
was generalized from a Theorem-U-only path to an any-milestone path. Three
contracts are easy to break in a future edit and nothing else in CI guards them:

  (1) DEFAULT CONTRACT — running `build_proof_snapshot.py` with DEFAULT inputs
      (`--kind theorem-u`) must still reproduce the original Theorem-U snapshot
      SHAPE: schema `szl.proof.snapshot/v1`, kind `theorem-u`, the full Theorem-U
      headline-decl pack, milestone.status `REAL-conditional` + kernel_only True,
      and the intact honesty block (locked_set from canonical revision-bound evidence, Theorem U
      conditional, Conjecture 1 OPEN / machine-checked FALSE). This is the subject
      `lake-build.yml` uploads and the live szl-lake receipt #1 was minted from, so
      its shape must stay stable. We additionally feed the result through the
      existing `check_theorem_u_snapshot.py` validator so the two stay in lockstep.

  (2) HONESTY DOCTRINE — the build must REFUSE (exit non-zero) any `--kind` that
      has no per-snapshot honesty block. A milestone may never be anchored without
      stating its own truthful status; supplying an honesty block lets it proceed.
      This is asserted both generically (an unregistered kind) and PER PRODUCTION
      KIND: for every milestone actually anchored to szl-lake we both pin its
      expected shape/status/headline/honesty AND prove that stripping its honesty
      block makes the build refuse — so a future edit can't quietly weaken or drop
      a different milestone's honesty label.

  (3) ANCHOR CHAIN MATH + IDEMPOTENCY — `anchor_szl_lake.py` must keep
      chain_index = len(existing)+1, prev_hash = the previous tail receipt_id
      (None at genesis), and treat (kind, kernel_commit, snapshot_sha) as the
      idempotency tuple that makes a re-anchor a no-op. canonical_hash must be
      order-independent (sorted-keys) so receipt ids are stable.

Pure stdlib; no network, no Lean toolchain, no signing. Exit 0 = all hold.
"""
from __future__ import annotations

import json
import os
import textwrap
import subprocess
import sys
import tempfile
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent
BUILD = SCRIPTS_DIR / "build_proof_snapshot.py"

# Import the sibling scripts as modules for in-process assertions.
sys.path.insert(0, str(SCRIPTS_DIR))
import anchor_szl_lake as A  # noqa: E402
import build_proof_snapshot as B  # noqa: E402
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
EXPECTED_LOCKED_SET = {"F1", "F4", "F7", "F11", "F12", "F18", "F19", "F22"}

# The locked-proven baseline (Doctrine v11) meta-invariant headline pack.
LOCKED_BASELINE_HEADLINE = sorted([
    "locked_count_eight",
    "theoremU_excluded_from_locked",
    "theoremU_axiom_sets_kernel_only",
    "conjecture1_still_open",
])
LOCKED_BASELINE_LOCKED_SET = {"F1", "F4", "F7", "F11", "F12", "F18", "F19", "F22"}


def _check_theorem_u_honesty(h: dict) -> None:
    """Pin the Theorem-U honesty block: conditional theorem, OPEN conjecture 1."""
    assert "locked_five_unchanged" not in h, h
    assert set(h.get("locked_set", [])) == EXPECTED_LOCKED_SET, h.get("locked_set")
    assert "REAL-conditional" in (h.get("theorem_u") or ""), h.get("theorem_u")
    conj = h.get("conjecture_1") or ""
    assert "OPEN" in conj and "FALSE" in conj, conj


def _check_locked_baseline_honesty(h: dict) -> None:
    """Pin the locked-baseline honesty block: invariant assertion, NOT a re-proof."""
    assert h.get("doctrine") == "v11", h.get("doctrine")
    assert set(h.get("locked_set", [])) == LOCKED_BASELINE_LOCKED_SET, h.get("locked_set")
    lb = h.get("locked_baseline") or ""
    assert "REAL-invariant" in lb, lb
    # The baseline asserts what is locked; it must NOT claim to re-prove the formulas.
    assert "do NOT" in lb or "do not" in lb, lb
    tu = h.get("theorem_u") or ""
    assert "EXCLUDED" in tu and "conditional" in tu, tu
    conj = h.get("conjecture_1") or ""
    assert "OPEN" in conj and "FALSE" in conj, conj


# Every milestone KIND actually anchored to szl-lake in production (each is built
# + uploaded as a snapshot artifact by lake-build.yml). For each we pin the
# expected status, headline-decl pack, and honesty block so a future edit can't
# silently change one milestone's shape or weaken its honesty label. Adding a new
# production-anchored kind without registering it here will leave it unguarded —
# add it to this table when you wire a new kind into lake-build.yml.
PRODUCTION_KINDS: dict[str, dict] = {
    "theorem-u": {
        "status": "REAL-conditional",
        "headline": THEOREM_U_HEADLINE,
        "check_honesty": _check_theorem_u_honesty,
        # theorem-u additionally has a standalone published-snapshot validator.
        "validator": G.validate_snapshot_file,
    },
    "locked-baseline": {
        "status": "REAL-invariant",
        "headline": LOCKED_BASELINE_HEADLINE,
        "check_honesty": _check_locked_baseline_honesty,
    },
}


def _write(path: Path, text: str) -> None:
    path.write_text(text, encoding="utf-8")


def _decls_for(kind: str) -> list[str]:
    """FQN decls for a production kind's headline pack (from its live profile)."""
    prof = B.PROFILES[kind]
    module = prof.get("module") or ""
    return [f"{module}.{s}" for s in prof["headline_suffixes"]]


def _fixtures(tmp: Path, decls: list[str] | None = None):
    """Build kernel-clean inputs covering a milestone's headline pack.

    Defaults to the Theorem-U pack so the existing back-compat tests are unchanged.
    """
    if decls is None:
        decls = ["Lutar.Uniqueness." + s for s in THEOREM_U_HEADLINE]
    # #print axioms shape; only Lean/Mathlib trust-base axioms so kernel_only holds.
    lines = [f"'{d}' depends on axioms: [propext, Classical.choice]" for d in decls]
    ax = tmp / "axiomcheck.out"
    _write(ax, "\n".join(lines) + "\n")
    numbers = tmp / "lean_numbers.measured.json"
    _write(numbers, json.dumps({
        "schema": "szl.lean_numbers/v1",
        "sha": "0" * 40,
        "numbers": {"declarations": 1234, "axioms_unique": 4, "sorries_noncomment": 0},
    }))
    refvec = tmp / "reference-vectors.json"
    _write(refvec, json.dumps({"vectors": []}))
    # Empty pack dir => decl_source_sha256 is deterministic + repo-layout-independent.
    packdir = tmp / "emptypack"
    packdir.mkdir()
    locked = tmp / "locked-formulas.evidence.json"
    _write(locked, json.dumps(G._selftest_locked_evidence("0" * 40)))
    return ax, numbers, refvec, packdir, locked


def _run_build(tmp: Path, extra_args: list[str], decls: list[str] | None = None,
               *, evidence_mutation=None, include_locked=True, reseal=True):
    ax, numbers, refvec, packdir, locked = _fixtures(tmp, decls)
    if evidence_mutation is not None:
        evidence = json.loads(locked.read_text(encoding="utf-8"))
        evidence_mutation(evidence)
        if reseal:
            evidence["evidence_digest"] = G.evidence_digest(evidence)
        _write(locked, json.dumps(evidence))
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
    ]
    if include_locked:
        cmd += ["--locked-evidence", str(locked)]
    cmd += extra_args
    proc = subprocess.run(cmd, capture_output=True, text=True)
    return proc, out


# --------------------------------------------------------------------------- #
# (1) default --kind theorem-u emits the canonical shape and evidence binding.
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
        assert "locked_five_unchanged" not in h, h
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
# (2b) per-production-kind: pinned shape + honesty, and honesty-required refusal.
#      Every milestone actually anchored to szl-lake gets its own assertion so a
#      future edit can't quietly change one kind's shape or weaken its honesty.
# --------------------------------------------------------------------------- #
def test_production_kind_shapes() -> None:
    for kind, exp in PRODUCTION_KINDS.items():
        with tempfile.TemporaryDirectory() as t:
            tmp = Path(t)
            proc, out = _run_build(tmp, ["--kind", kind], decls=_decls_for(kind))
            assert proc.returncode == 0, (
                f"{kind} build must succeed; rc={proc.returncode}\n{proc.stderr}"
            )
            assert out.exists(), f"{kind} build produced no snapshot file"
            snap = json.loads(out.read_text(encoding="utf-8"))

            assert snap.get("schema") == "szl.proof.snapshot/v1", (kind, snap.get("schema"))
            assert snap.get("kind") == kind, (kind, snap.get("kind"))

            m = snap.get("milestone", {})
            assert m.get("status") == exp["status"], (kind, m.get("status"))
            assert m.get("kernel_only") is True, (kind, m.get("kernel_only"))
            assert m.get("headline_decls") == exp["headline"], (kind, m.get("headline_decls"))

            h = snap.get("honesty", {})
            assert h, f"{kind} snapshot is missing its honesty block"
            exp["check_honesty"](h)

            validator = exp.get("validator")
            if validator is not None:
                problems = validator(out)
                assert not problems, f"{kind} snapshot guard rejected the build: {problems}"


def test_production_kind_without_honesty_is_refused() -> None:
    """Per kind: stripping the honesty block makes that kind's build refuse."""
    for kind in PRODUCTION_KINDS:
        with tempfile.TemporaryDirectory() as t:
            tmp = Path(t)
            # Override the built-in profile so the honesty block is removed; the
            # profile file is merged over the registered profile in _load_profile.
            strip = tmp / "strip_honesty.json"
            _write(strip, json.dumps({"honesty": None}))
            proc, out = _run_build(
                tmp, ["--kind", kind, "--profile", str(strip)], decls=_decls_for(kind)
            )
            assert proc.returncode != 0, (
                f"{kind} build with its honesty block stripped must exit non-zero"
            )
            blob = (proc.stderr or "") + (proc.stdout or "")
            assert "honesty block" in blob, (
                f"{kind}: expected an honesty-block refusal, got:\n{blob}"
            )
            assert not out.exists(), f"{kind} refused build must not write a snapshot file"


# --------------------------------------------------------------------------- #
# (3) anchor chain math + idempotency tuple.
# --------------------------------------------------------------------------- #

def test_locked_evidence_fail_closed() -> None:
    """Reject coherent-looking but stale, partial, missing, or disallowed evidence."""
    five = {"F1", "F11", "F12", "F18", "F19"}

    def old_five(evidence):
        evidence["locked_ids"] = [item for item in evidence["locked_ids"] if item in five]
        evidence["claims"] = [row for row in evidence["claims"] if row["claim_id"] in five]

    cases = [
        ("historical-five", old_five, True),
        ("wrong-revision", lambda e: e.update(source_commit="1" * 40), True),
        ("dirty-inputs", lambda e: e.update(input_files_match_head=False), True),
        ("source-digest-mismatch", lambda e: e["inputs"].update(
            {"claims/locked-formulas.v1.json": "sha256:" + "0" * 64}), True),
        ("missing-carrier", lambda e: e["claims"][0]["carriers"].pop(), True),
        ("disallowed-carrier", lambda e: e["claims"][0]["carriers"][0].update(allowed=False), True),
        ("custom-axiom", lambda e: e["claims"][0]["carriers"][0].update(axioms=["custom_axiom"]), True),
        ("sorry-axiom", lambda e: e["claims"][0]["carriers"][0].update(axioms=["sorryAx"]), True),
        ("invalid-digest", lambda e: e.update(evidence_digest="sha256:" + "0" * 64), False),
    ]
    for name, mutation, reseal in cases:
        with tempfile.TemporaryDirectory() as t:
            proc, out = _run_build(Path(t), [], evidence_mutation=mutation, reseal=reseal)
            assert proc.returncode != 0, f"{name}: malformed evidence was accepted"
            assert not out.exists(), f"{name}: refused build wrote a snapshot"
    for flags, include_locked in [([], False), (["--locked-evidence", "missing-evidence.json"], True)]:
        with tempfile.TemporaryDirectory() as t:
            proc, out = _run_build(Path(t), flags, include_locked=include_locked)
            assert proc.returncode != 0, "missing evidence was accepted"
            assert not out.exists(), "missing-evidence refusal wrote a snapshot"


def test_snapshot_binding_rejects_drift() -> None:
    with tempfile.TemporaryDirectory() as t:
        tmp = Path(t)
        proc, out = _run_build(tmp, [])
        assert proc.returncode == 0, proc.stderr
        good = json.loads(out.read_text(encoding="utf-8"))
        assert good["honesty"]["locked_set"] == good["locked_formula_evidence"]["locked_ids"]
        assert not G.validate_snapshot_file(out, "0" * 40), "canonical evidence binding was rejected"
        assert G.validate_snapshot_file(out, "1" * 40), "source workflow mismatch was accepted"
        mutations = [
            ("five-set", lambda s: s["honesty"].update(locked_set=["F1", "F11", "F12", "F18", "F19"])),
            ("missing-set", lambda s: s["honesty"].pop("locked_set")),
            ("missing-evidence", lambda s: s.pop("locked_formula_evidence")),
            ("wrong-commit", lambda s: s.update(kernel_commit="1" * 40)),
            ("legacy-boolean", lambda s: s["honesty"].update(locked_five_unchanged=True)),
            ("duplicate-id", lambda s: s["honesty"]["locked_set"].append("F1")),
        ]
        for name, mutate in mutations:
            changed = json.loads(json.dumps(good))
            mutate(changed)
            _write(out, json.dumps(changed))
            assert G.validate_snapshot_file(out), f"{name}: snapshot drift was accepted"


def test_profile_cannot_override_locked_evidence() -> None:
    for fields in [
        {"locked_set": ["F1", "F11", "F12", "F18", "F19"]},
        {"locked_five_unchanged": True},
    ]:
        with tempfile.TemporaryDirectory() as t:
            tmp = Path(t)
            override = tmp / "dishonest-profile.json"
            _write(override, json.dumps({"honesty": {"doctrine": "v11", **fields}}))
            proc, out = _run_build(tmp, ["--profile", str(override)])
            assert proc.returncode != 0, "profile overrode the canonical locked evidence"
            assert not out.exists(), "inconsistent profile wrote a snapshot"



def test_anchor_workflow_uses_bound_snapshot() -> None:
    """Execute the actual pre-signing assertion block with good and stale evidence."""
    workflow = (SCRIPTS_DIR.parent / "workflows/anchor-szl-lake.yml").read_text(encoding="utf-8")
    section = workflow.split("      - name: Assert snapshot is a kernel-only proof-milestone snapshot", 1)[1]
    code = textwrap.dedent(section.split("python3 - <<'PY'\n", 1)[1].split("\n          PY", 1)[0])
    with tempfile.TemporaryDirectory() as t:
        tmp = Path(t)
        proc, out = _run_build(tmp, [])
        assert proc.returncode == 0, proc.stderr
        good = json.loads(out.read_text(encoding="utf-8"))
        cases = [
            ("canonical", good, "0" * 40, 0),
            ("wrong-source-run", good, "1" * 40, 1),
        ]
        stale = json.loads(json.dumps(good))
        stale.pop("locked_formula_evidence")
        stale["honesty"]["locked_set"] = ["F1", "F11", "F12", "F18", "F19"]
        stale["honesty"]["locked_five_unchanged"] = True
        cases.append(("historical-five", stale, "0" * 40, 1))
        for name, snapshot, expected, exit_code in cases:
            _write(out, json.dumps(snapshot))
            env = dict(os.environ, SNAPSHOT_FILE=str(out), KIND="theorem-u",
                       EXPECTED_KERNEL_COMMIT=expected)
            checked = subprocess.run([sys.executable, "-c", code], cwd=SCRIPTS_DIR.parents[1],
                                     env=env, capture_output=True, text=True)
            assert checked.returncode == exit_code, (
                f"{name}: anchor admission returned {checked.returncode}, expected {exit_code}: "
                + checked.stdout + checked.stderr
            )


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


# --------------------------------------------------------------------------- #
# (4) verify-anchor-receipts append-only floor: auto-bump, never lower.
# --------------------------------------------------------------------------- #
def test_baseline_floor_append_only() -> None:
    # A new anchor at chain_index N raises the floor to N (preserving other keys).
    up = A.bump_baseline_floor('{"_comment": "x", "min_receipts": 2}', 3)
    assert up is not None, "a higher chain_index must bump the floor"
    doc = json.loads(up)
    assert doc["min_receipts"] == 3, doc
    assert "_comment" in doc, "the _comment key must be preserved/refreshed"

    # APPEND-ONLY: a lower chain_index must NEVER lower the floor (no write).
    assert A.bump_baseline_floor('{"min_receipts": 5}', 3) is None, (
        "the floor must never be lowered (5 -> 3 is a no-op)"
    )
    # No-op when already at the floor (idempotent re-anchor).
    assert A.bump_baseline_floor('{"min_receipts": 3}', 3) is None, (
        "an equal chain_index must be a no-op"
    )
    # Absent / empty baseline -> create it at the new floor.
    created = A.bump_baseline_floor(None, 1)
    assert created is not None and json.loads(created)["min_receipts"] == 1, (
        "a missing baseline file must be created at the new floor"
    )
    assert json.loads(A.bump_baseline_floor("", 4))["min_receipts"] == 4, (
        "an empty baseline body must be treated as floor 0 and created"
    )
    # Malformed JSON -> treated as floor 0, then set (never silently keep junk).
    assert json.loads(A.bump_baseline_floor("not json", 4))["min_receipts"] == 4, (
        "a malformed baseline must be repaired up to the new floor"
    )
    # baseline_floor reader is robust to junk/missing.
    assert A.baseline_floor('{"min_receipts": 7}') == 7
    assert A.baseline_floor(None) == 0 and A.baseline_floor("nope") == 0


TESTS = [
    ("default theorem-u snapshot with canonical locked evidence", test_default_theorem_u_shape),
    ("kind without honesty block is refused", test_kind_without_honesty_is_refused),
    ("kind with honesty block is allowed", test_kind_with_honesty_is_allowed),
    ("production milestone kind shapes + honesty", test_production_kind_shapes),
    ("production milestone kind refused without honesty", test_production_kind_without_honesty_is_refused),
    ("locked evidence fails closed on missing/stale/disallowed records", test_locked_evidence_fail_closed),
    ("snapshot locked binding rejects drift", test_snapshot_binding_rejects_drift),
    ("profile cannot override locked evidence", test_profile_cannot_override_locked_evidence),
    ("anchor workflow enforces bound evidence before signing", test_anchor_workflow_uses_bound_snapshot),
    ("anchor chain_position genesis + advance", test_chain_position_genesis_and_advance),
    ("anchor idempotency tuple", test_idempotency_tuple),
    ("canonical_hash order independence", test_canonical_hash_order_independent),
    ("verify-anchor-receipts floor is append-only", test_baseline_floor_append_only),
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
        "Theorem-U snapshot shape, every production-anchored milestone kind keeps its "
        "pinned shape + honesty block (and is refused with it stripped), a kind with no "
        "honesty block is refused, and the anchor chain math + idempotency tuple are intact."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
