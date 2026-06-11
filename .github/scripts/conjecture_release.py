#!/usr/bin/env python3
"""Conjecture Factory — staged-release gate (step 6 of the pipeline).

Enforces the staged disclosure policy: a generated conjecture is released in
ordered stages and CANNOT skip ahead. The single source of truth for what has
already been timestamped is the szl-lake DSSE Khipu ledger (the same NDJSON the
anchor appends to) — release state is DERIVED from the ledger, never asserted
independently.

Stages (ordered):
  0 teaser    — title + statement_hash only; no full statement. Always allowed
                (a teaser commits to nothing the ledger needs to gate).
  1 statement — the full problem statement. Allowed ONLY once a disclosure
                receipt for this candidate exists in the ledger, i.e. the
                statement has been cryptographically timestamped. This is what
                stops "publish first, timestamp later" priority disputes.
  2 solution  — the worked solution. Allowed ONLY when the candidate has been
                genuinely resolved (grade REFUTED / VERIFIED-FINITE, or an
                externally-verified proof receipt). An OPEN conjecture can never
                reach this stage — doctrine v11 forbids presenting an OPEN
                problem as solved.

The gate returns a release manifest and exit code 0 when the requested stage is
permitted, exits non-zero otherwise. stdlib only; `--ledger` may be a local
NDJSON file (offline) — the workflow points it at the freshly-read szl-lake copy.

`--self-test` runs offline fixtures.
"""
from __future__ import annotations

import argparse
import datetime as _dt
import json
import sys

STAGES = ["teaser", "statement", "solution"]
RESOLVED_GRADES = ("REFUTED", "VERIFIED-FINITE")


def _utcnow() -> str:
    return _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _read_ledger(path: str | None) -> list[dict]:
    if not path:
        return []
    recs = []
    with open(path, "r", encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if line:
                recs.append(json.loads(line))
    return recs


def disclosure_receipts_for(ledger: list[dict], candidate_id: str) -> list[dict]:
    """All conjecture-disclosure receipts whose embedded milestone id matches."""
    out = []
    for rec in ledger:
        if rec.get("kind") != "conjecture-disclosure-anchor":
            continue
        snap = (rec.get("subject") or {}).get("snapshot") or {}
        mid = (snap.get("milestone") or {}).get("id")
        if mid == candidate_id:
            out.append(rec)
    return out


def evaluate(candidate: dict, stage: str, ledger: list[dict],
             grade: dict | None = None) -> dict:
    if stage not in STAGES:
        raise SystemExit(f"::error::unknown stage '{stage}' (valid: {STAGES})")

    cid = candidate.get("id", "")
    receipts = disclosure_receipts_for(ledger, cid)
    timestamped = bool(receipts)
    grade_result = (grade or candidate.get("_grade") or {}).get("result")
    if grade_result is None:
        # fall back to the grade embedded in any disclosure receipt
        for rec in receipts:
            snap = (rec.get("subject") or {}).get("snapshot") or {}
            grade_result = (snap.get("grade") or {}).get("result")
            if grade_result:
                break
    resolved = grade_result in RESOLVED_GRADES

    allowed = True
    reason = ""
    if stage == "teaser":
        reason = "teaser is always permitted (commits to no gated content)"
    elif stage == "statement":
        if not timestamped:
            allowed = False
            reason = ("statement release BLOCKED: no conjecture-disclosure receipt for "
                      f"'{cid}' in the szl-lake ledger. The statement must be "
                      "cryptographically timestamped before it is published.")
        else:
            reason = (f"statement permitted: {len(receipts)} disclosure receipt(s) "
                      f"timestamp '{cid}' in the ledger")
    elif stage == "solution":
        if not timestamped:
            allowed = False
            reason = ("solution release BLOCKED: the statement was never timestamped "
                      "(no disclosure receipt) — cannot skip ahead to a solution")
        elif not resolved:
            allowed = False
            reason = (f"solution release BLOCKED: candidate is OPEN (grade="
                      f"{grade_result!r}); an OPEN conjecture may not be presented as "
                      "solved (doctrine v11)")
        else:
            reason = (f"solution permitted: candidate resolved (grade={grade_result}) "
                      "and timestamped")

    return {
        "schema": "szl.conjecture.release/v1",
        "candidate_id": cid,
        "title": candidate.get("title", ""),
        "requested_stage": stage,
        "allowed": allowed,
        "reason": reason,
        "timestamped": timestamped,
        "disclosure_receipts": [
            {"chain_index": r.get("chain_index"), "receipt_id": r.get("receipt_id"),
             "timestamp": r.get("timestamp")} for r in receipts
        ],
        "grade_result": grade_result,
        "resolved": resolved,
        "evaluated_utc": _utcnow(),
        "honesty": (
            "Release state is derived from the szl-lake ledger (single source of "
            "truth). Stages cannot be skipped; a 'solution' stage is impossible for an "
            "OPEN conjecture (doctrine v11)."
        ),
    }


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Staged-release gate for a conjecture.")
    ap.add_argument("--candidate")
    ap.add_argument("--stage", default="teaser", choices=STAGES)
    ap.add_argument("--ledger", help="szl-lake NDJSON (local copy); empty = none seen")
    ap.add_argument("--grade", help="grade JSON (optional; overrides ledger-embedded)")
    ap.add_argument("--out")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args(argv)

    if args.self_test:
        return _self_test()

    if not args.candidate:
        ap.error("--candidate is required (or use --self-test)")
    with open(args.candidate, "r", encoding="utf-8") as fh:
        candidate = json.load(fh)
    ledger = _read_ledger(args.ledger)
    grade = None
    if args.grade:
        with open(args.grade, "r", encoding="utf-8") as fh:
            grade = json.load(fh)
    res = evaluate(candidate, args.stage, ledger, grade=grade)
    out = json.dumps(res, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    if args.out:
        with open(args.out, "w", encoding="utf-8") as fh:
            fh.write(out)
    else:
        sys.stdout.write(out)
    if not res["allowed"]:
        print(f"::error::{res['reason']}")
        return 2
    print(f"release OK: stage={args.stage} candidate={res['candidate_id']}")
    return 0


def _mk_receipt(cid: str, idx: int, grade_result: str = "OPEN") -> dict:
    return {
        "kind": "conjecture-disclosure-anchor",
        "chain_index": idx,
        "receipt_id": f"rid{idx}",
        "timestamp": "2026-01-01T00:00:00Z",
        "subject": {"snapshot": {"milestone": {"id": cid},
                                 "grade": {"result": grade_result}}},
    }


def _self_test() -> int:
    cand = {"id": "cf-xyz", "title": "Sample"}

    # teaser: always allowed, even with no ledger.
    r = evaluate(cand, "teaser", [])
    assert r["allowed"] and not r["timestamped"]

    # statement: blocked without a disclosure receipt.
    r = evaluate(cand, "statement", [])
    assert not r["allowed"] and "BLOCKED" in r["reason"]

    # statement: allowed once timestamped.
    led = [_mk_receipt("cf-xyz", 2, "OPEN")]
    r = evaluate(cand, "statement", led)
    assert r["allowed"] and r["timestamped"]
    assert r["disclosure_receipts"][0]["chain_index"] == 2

    # solution: blocked while OPEN even though timestamped.
    r = evaluate(cand, "solution", led)
    assert not r["allowed"] and "OPEN" in r["reason"]

    # solution: blocked if never timestamped (cannot skip).
    r = evaluate(cand, "solution", [], grade={"result": "REFUTED"})
    assert not r["allowed"] and "never timestamped" in r["reason"]

    # solution: allowed when resolved AND timestamped.
    led2 = [_mk_receipt("cf-xyz", 2, "REFUTED")]
    r = evaluate(cand, "solution", led2)
    assert r["allowed"] and r["resolved"], r["reason"]

    # ledger entries for a DIFFERENT candidate don't unlock this one.
    led3 = [_mk_receipt("cf-other", 2, "REFUTED")]
    r = evaluate(cand, "statement", led3)
    assert not r["allowed"]

    # non-disclosure receipts are ignored.
    led4 = [{"kind": "theorem-u-anchor", "chain_index": 1,
             "subject": {"snapshot": {"milestone": {"id": "cf-xyz"}}}}]
    r = evaluate(cand, "statement", led4)
    assert not r["allowed"]

    print("conjecture_release self-test OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
