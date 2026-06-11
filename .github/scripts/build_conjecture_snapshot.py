#!/usr/bin/env python3
"""Conjecture Factory — disclosure snapshot builder (step 4 of the pipeline).

Assembles the single JSON document that gets cosign-signed and anchored into the
szl-lake DSSE Khipu ledger by the GENERIC `anchor_szl_lake.py`. It is the
cryptographic timestamp of a generated conjecture: it commits, at a point in
time, to the canonical statement hash, the novelty screen, and the difficulty
grade — WITHOUT claiming the conjecture is true.

The snapshot deliberately conforms to the shape `anchor_szl_lake.py` consumes:
  - kind                 : "conjecture-disclosure"  (anchor keys receipt_kind off this)
  - milestone{}          : status/title/headline_decls/...   (anchor: get_milestone)
  - honesty{}            : carries `doctrine` + per-field honesty, verbatim
  - kernel_commit / _short, branch
  - lean_numbers{}       : optional (kept absent: a conjecture is NOT kernel-built)

CRITICAL (honesty v11): milestone.status is "OPEN" and milestone.kernel_only is
false. This snapshot is NOT a kernel-verified theorem; it is an OPEN problem with
a timestamp. The anchor workflow for conjectures therefore MUST NOT apply the
Theorem-U kernel-only gate.

stdlib only. `--self-test` builds an in-memory snapshot from fixtures and
validates the contract.
"""
from __future__ import annotations

import argparse
import datetime as _dt
import json
import sys

SCHEMA = "szl.conjecture.disclosure/v1"
KIND = "conjecture-disclosure"
PREDICATE_TYPE = "https://szl-holdings/conjecture-disclosure/v1"
DOCTRINE = "v11"
VALID_STAGES = ("teaser", "statement", "solution")


def _utcnow() -> str:
    return _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def build(candidate: dict, novelty: dict, grade: dict, *,
          kernel_commit: str, branch: str, stage: str = "statement",
          repo: str = "szl-holdings/lutar-lean") -> dict:
    if candidate.get("schema") != "szl.conjecture.candidate/v1":
        raise SystemExit("::error::candidate is not szl.conjecture.candidate/v1")
    if candidate.get("taxonomy") != "OPEN":
        raise SystemExit("::error::candidate taxonomy must be OPEN at disclosure")
    if stage not in VALID_STAGES:
        raise SystemExit(f"::error::invalid release stage '{stage}'")

    # Cross-link integrity: novelty + grade must reference THIS candidate.
    cid = candidate.get("id", "")
    if novelty and novelty.get("candidate_id") not in ("", cid):
        raise SystemExit("::error::novelty.candidate_id does not match candidate.id")
    if grade and grade.get("candidate_id") not in ("", cid):
        raise SystemExit("::error::grade.candidate_id does not match candidate.id")

    grade_result = (grade or {}).get("result", "UNREACHABLE")
    # A disclosure NEVER releases a "solution" stage for an unresolved problem.
    if stage == "solution" and grade_result not in ("REFUTED", "VERIFIED-FINITE"):
        raise SystemExit(
            "::error::cannot build a 'solution'-stage disclosure for an OPEN/"
            "UNREACHABLE candidate — staged release forbids skipping to solution "
            "without a real resolution (doctrine v11)")

    novelty_verdict = (novelty or {}).get("verdict", "inconclusive")
    difficulty = (grade or {}).get("difficulty", "ungraded")

    milestone = {
        "id": cid,
        "title": candidate.get("title", cid),
        "status": "OPEN",
        "kernel_only": False,
        "headline_decls": [],
        "statement_hash": candidate.get("statement_hash", ""),
        "release_stage": stage,
        "novelty_verdict": novelty_verdict,
        "grade_result": grade_result,
        "difficulty": difficulty,
    }

    honesty = {
        "doctrine": DOCTRINE,
        "status": "OPEN",
        "conjecture": (
            "This is a GENERATED, OPEN conjecture — NOT a theorem and NOT machine-"
            "verified. It remains OPEN until a solution is independently verified."
        ),
        "novelty": (
            f"Novelty verdict '{novelty_verdict}' is an advisory screen, not a proof "
            "of originality; external prior-art sources are labelled "
            "live/cached/unreachable and an unreachable source never confirms novelty."
        ),
        "difficulty": (
            f"Difficulty '{difficulty}' / grade '{grade_result}' come from a REAL "
            "bounded solver run. OPEN means searched-to-budget, not proven true; "
            "VERIFIED-FINITE certifies only the finite enumerated domain; REFUTED "
            "carries a concrete witness. No score is fabricated."
        ),
        "kernel_only": False,
        "signing": (
            "Disclosure is cosign keyless-OIDC signed and anchored into the szl-lake "
            "DSSE Khipu ledger; the signature attests the timestamp + content, NOT the "
            "truth of the conjecture."
        ),
    }

    snapshot = {
        "schema": SCHEMA,
        "kind": KIND,
        "predicate_type": PREDICATE_TYPE,
        "repo": repo,
        "kernel_commit": kernel_commit,
        "kernel_commit_short": (kernel_commit or "")[:12],
        "branch": branch,
        "built_at_utc": _utcnow(),
        "milestone": milestone,
        "candidate": candidate,
        "novelty": novelty or {},
        "grade": grade or {},
        "honesty": honesty,
    }
    return snapshot


def _load(path: str) -> dict:
    with open(path, "r", encoding="utf-8") as fh:
        return json.load(fh)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Build a conjecture disclosure snapshot.")
    ap.add_argument("--candidate")
    ap.add_argument("--novelty")
    ap.add_argument("--grade")
    ap.add_argument("--kernel-commit", default="")
    ap.add_argument("--branch", default="main")
    ap.add_argument("--stage", default="statement", choices=VALID_STAGES)
    ap.add_argument("--repo", default="szl-holdings/lutar-lean")
    ap.add_argument("--out", help="write snapshot JSON here")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args(argv)

    if args.self_test:
        return _self_test()

    if not args.candidate:
        ap.error("--candidate is required (or use --self-test)")
    candidate = _load(args.candidate)
    novelty = _load(args.novelty) if args.novelty else {}
    grade = _load(args.grade) if args.grade else {}
    snap = build(candidate, novelty, grade, kernel_commit=args.kernel_commit,
                 branch=args.branch, stage=args.stage, repo=args.repo)
    out = json.dumps(snap, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    if args.out:
        with open(args.out, "w", encoding="utf-8") as fh:
            fh.write(out)
        print(f"snapshot OK: kind={snap['kind']} status={snap['milestone']['status']} "
              f"stage={snap['milestone']['release_stage']} -> {args.out}")
    else:
        sys.stdout.write(out)
    return 0


def _fixtures():
    candidate = {
        "schema": "szl.conjecture.candidate/v1",
        "id": "cf-abc123def456",
        "title": "Sample OPEN conjecture",
        "statement_hash": "sha256:deadbeef",
        "taxonomy": "OPEN",
        "doctrine": "v11",
    }
    novelty = {"schema": "szl.conjecture.novelty/v1", "candidate_id": "cf-abc123def456",
               "verdict": "novel-candidate"}
    grade = {"schema": "szl.conjecture.grade/v1", "candidate_id": "cf-abc123def456",
             "result": "OPEN", "difficulty": "open-resistant"}
    return candidate, novelty, grade


def _self_test() -> int:
    candidate, novelty, grade = _fixtures()
    snap = build(candidate, novelty, grade, kernel_commit="a" * 40, branch="main")
    assert snap["kind"] == KIND
    assert snap["milestone"]["status"] == "OPEN"
    assert snap["milestone"]["kernel_only"] is False
    assert snap["honesty"]["doctrine"] == "v11"
    assert snap["milestone"]["novelty_verdict"] == "novel-candidate"
    assert snap["milestone"]["grade_result"] == "OPEN"
    assert snap["kernel_commit_short"] == "a" * 12
    assert "lean_numbers" not in snap  # a conjecture is NOT kernel-built
    # anchor compatibility: get_milestone-style access + honesty.doctrine
    assert (snap.get("milestone") or {}).get("status") == "OPEN"
    assert snap.get("honesty", {}).get("doctrine", "v11") == "v11"

    # solution stage forbidden for OPEN grade
    try:
        build(candidate, novelty, grade, kernel_commit="a" * 40, branch="main",
              stage="solution")
        raise AssertionError("solution stage must be refused for an OPEN grade")
    except SystemExit:
        pass

    # solution stage allowed when the problem was actually resolved
    grade_res = {**grade, "result": "REFUTED", "difficulty": "refuted"}
    snap2 = build(candidate, novelty, grade_res, kernel_commit="b" * 40, branch="main",
                  stage="solution")
    assert snap2["milestone"]["release_stage"] == "solution"

    # mismatched candidate id is rejected
    try:
        build(candidate, {**novelty, "candidate_id": "cf-other"}, grade,
              kernel_commit="a" * 40, branch="main")
        raise AssertionError("mismatched novelty.candidate_id must be rejected")
    except SystemExit:
        pass

    # non-OPEN candidate is rejected
    try:
        build({**candidate, "taxonomy": "PROVEN"}, novelty, grade,
              kernel_commit="a" * 40, branch="main")
        raise AssertionError("non-OPEN candidate must be rejected")
    except SystemExit:
        pass

    print("build_conjecture_snapshot self-test OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
