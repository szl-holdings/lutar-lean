#!/usr/bin/env python3
"""Conjecture Factory — generation intake (step 2 of the pipeline).

Normalises a raw conjecture candidate into the canonical schema
`szl.conjecture.candidate/v1` with a STABLE id derived from the canonical
statement, so re-running intake on the same statement is idempotent (same id,
same statement_hash).

A candidate is OPEN by construction: this script never asserts a candidate is
true, novel, or graded — those are separate, later pipeline steps. The only
claim made here is structural (the statement was normalised and hashed).

Honesty doctrine v11: a generated problem is OPEN until a solution is verified.
Intake therefore hard-sets `taxonomy: OPEN` and refuses any input that tries to
declare itself PROVEN/REAL/VERIFIED.

Input (JSON or YAML-subset) must contain at least:
  - title
  - statement
  - intended_solution_outline
Optional:
  - domain          (free-text math-area tag)
  - predicate       ({"kind": "python-callable", "module": "...", "entry": "..."}
                     or {"kind": "none"})  — a machine-checkable predicate the
                     grader can actually run; omit/none if not executable.
  - references      (list of strings)

No network, stdlib only. `--self-test` runs an offline round-trip.
"""
from __future__ import annotations

import argparse
import datetime as _dt
import hashlib
import json
import re
import sys

SCHEMA = "szl.conjecture.candidate/v1"
DOCTRINE = "v11"

# Labels a candidate is NEVER allowed to carry at intake (honesty v11).
_FORBIDDEN_TAXONOMY = {"PROVEN", "REAL", "VERIFIED", "CLOSED", "SOLVED"}

_WS_RE = re.compile(r"\s+")


def _utcnow() -> str:
    return _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _sha256(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def canonicalize_statement(statement: str) -> str:
    """Whitespace- and case-insensitive-trim normalisation of a statement.

    We collapse internal whitespace and strip, but PRESERVE case and symbols —
    a conjecture's meaning is symbol-sensitive. The canonical form is what the
    stable id and the szl-lake timestamp commit to.
    """
    return _WS_RE.sub(" ", statement.strip())


def stable_id(canonical_statement: str) -> str:
    return "cf-" + _sha256(canonical_statement.encode())[:12]


def _load_raw(path: str) -> dict:
    """Load JSON; fall back to a tiny YAML-subset parser for flat key: value."""
    with open(path, "r", encoding="utf-8") as fh:
        text = fh.read()
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        return _parse_flat_yaml(text)


def _parse_flat_yaml(text: str) -> dict:
    """Minimal YAML-subset: `key: value`, `key: |` block scalars, `- item` lists.

    Deliberately tiny (no external deps). Only supports the shapes the intake
    fixtures use; anything else should be provided as JSON.
    """
    out: dict = {}
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        raw = lines[i]
        if not raw.strip() or raw.lstrip().startswith("#"):
            i += 1
            continue
        m = re.match(r"^([A-Za-z0-9_]+):\s*(.*)$", raw)
        if not m:
            i += 1
            continue
        key, val = m.group(1), m.group(2).strip()
        if val in ("|", ">"):
            block, i = _read_block(lines, i + 1)
            out[key] = block if val == "|" else _WS_RE.sub(" ", block).strip()
            continue
        if val == "":
            items, ni = _read_list(lines, i + 1)
            if items is not None:
                out[key] = items
                i = ni
                continue
            mp, nj = _read_map(lines, i + 1)
            if mp is not None:
                out[key] = mp
                i = nj
                continue
            out[key] = ""
            i += 1
            continue
        out[key] = _scalar(val)
        i += 1
    return out


def _read_block(lines, start):
    body = []
    indent = None
    i = start
    while i < len(lines):
        ln = lines[i]
        if ln.strip() == "":
            body.append("")
            i += 1
            continue
        cur = len(ln) - len(ln.lstrip())
        if indent is None:
            indent = cur
        if cur < indent:
            break
        body.append(ln[indent:])
        i += 1
    return "\n".join(body).rstrip() + "\n", i


def _read_list(lines, start):
    items = []
    i = start
    saw = False
    while i < len(lines):
        ln = lines[i]
        if ln.strip() == "":
            i += 1
            continue
        if re.match(r"^\s*-\s+", ln):
            items.append(_scalar(re.sub(r"^\s*-\s+", "", ln).strip()))
            saw = True
            i += 1
            continue
        break
    return (items if saw else None), i


def _read_map(lines, start):
    """One level of nested `key: value` mapping (with `|`/`>` block scalars).

    Returns (dict, next_index) or (None, start) when the following block is not
    an indented mapping. Used for shapes like `predicate:` with sub-keys.
    """
    out: dict = {}
    i = start
    base = None
    while i < len(lines):
        ln = lines[i]
        if ln.strip() == "" or ln.lstrip().startswith("#"):
            i += 1
            continue
        cur = len(ln) - len(ln.lstrip())
        if base is None:
            base = cur
        if cur < base:
            break
        m = re.match(r"^\s*([A-Za-z0-9_]+):\s*(.*)$", ln)
        if not m:
            break
        k, v = m.group(1), m.group(2).strip()
        if v in ("|", ">"):
            block, i = _read_block(lines, i + 1)
            out[k] = block if v == "|" else _WS_RE.sub(" ", block).strip()
            continue
        out[k] = _scalar(v)
        i += 1
    return (out if out else None), i


def _scalar(v: str):
    v = v.strip().strip('"').strip("'")
    return v


def normalize(raw: dict, *, created_utc: str | None = None) -> dict:
    required = ["title", "statement", "intended_solution_outline"]
    missing = [k for k in required if not str(raw.get(k, "")).strip()]
    if missing:
        raise SystemExit(f"::error::candidate missing required field(s): {missing}")

    tax = str(raw.get("taxonomy", "OPEN")).strip().upper()
    if tax in _FORBIDDEN_TAXONOMY:
        raise SystemExit(
            f"::error::a candidate may not declare taxonomy '{tax}' at intake — "
            "generated problems are OPEN until verified (doctrine v11)")

    canonical = canonicalize_statement(str(raw["statement"]))
    cid = stable_id(canonical)
    statement_hash = "sha256:" + _sha256(canonical.encode())

    predicate = raw.get("predicate") or {"kind": "none"}
    if not isinstance(predicate, dict) or "kind" not in predicate:
        raise SystemExit("::error::predicate, if present, must be an object with a 'kind'")
    if predicate["kind"] not in ("python-callable", "none"):
        raise SystemExit(f"::error::unsupported predicate kind: {predicate['kind']}")

    refs = raw.get("references") or []
    if not isinstance(refs, list):
        raise SystemExit("::error::references must be a list")

    candidate = {
        "schema": SCHEMA,
        "id": cid,
        "title": str(raw["title"]).strip(),
        "domain": str(raw.get("domain", "")).strip(),
        "statement": str(raw["statement"]).strip(),
        "statement_canonical": canonical,
        "statement_hash": statement_hash,
        "intended_solution_outline": str(raw["intended_solution_outline"]).strip(),
        "predicate": predicate,
        "references": [str(r).strip() for r in refs],
        "taxonomy": "OPEN",
        "doctrine": DOCTRINE,
        "created_utc": created_utc or _utcnow(),
    }
    return candidate


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Normalise a conjecture candidate.")
    ap.add_argument("--in", dest="inp", help="raw candidate (JSON or flat-YAML)")
    ap.add_argument("--out", help="write normalised candidate JSON here")
    ap.add_argument("--self-test", action="store_true", help="offline round-trip test")
    args = ap.parse_args(argv)

    if args.self_test:
        return _self_test()

    if not args.inp:
        ap.error("--in is required (or use --self-test)")
    raw = _load_raw(args.inp)
    candidate = normalize(raw)
    out = json.dumps(candidate, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    if args.out:
        with open(args.out, "w", encoding="utf-8") as fh:
            fh.write(out)
        print(f"intake OK: id={candidate['id']} statement_hash={candidate['statement_hash']} "
              f"taxonomy={candidate['taxonomy']} -> {args.out}")
    else:
        sys.stdout.write(out)
    return 0


def _self_test() -> int:
    # 1. round-trip + stable id
    raw = {
        "title": "Test conjecture",
        "statement": "For all  n,  P(n)  holds.",
        "intended_solution_outline": "Induction on n.",
        "domain": "number-theory",
    }
    c1 = normalize(raw, created_utc="2026-01-01T00:00:00Z")
    c2 = normalize({**raw, "statement": "For all n, P(n) holds."},
                   created_utc="2026-02-02T00:00:00Z")
    assert c1["id"] == c2["id"], "id must be stable under whitespace normalisation"
    assert c1["statement_hash"] == c2["statement_hash"]
    assert c1["id"].startswith("cf-") and len(c1["id"]) == 15
    assert c1["taxonomy"] == "OPEN"

    # 2. forbidden taxonomy is rejected
    try:
        normalize({**raw, "taxonomy": "PROVEN"})
        raise AssertionError("PROVEN taxonomy should have been rejected")
    except SystemExit:
        pass

    # 3. missing required field is rejected
    try:
        normalize({"title": "x", "statement": "y"})
        raise AssertionError("missing intended_solution_outline should be rejected")
    except SystemExit:
        pass

    # 4. flat-YAML parse
    y = (
        "title: YAML conj\n"
        "domain: combinatorics\n"
        "statement: |\n"
        "  Every graph G has property Q.\n"
        "intended_solution_outline: |\n"
        "  Probabilistic method.\n"
        "references:\n"
        "  - https://example.org/a\n"
        "  - https://example.org/b\n"
    )
    parsed = _parse_flat_yaml(y)
    cy = normalize(parsed, created_utc="2026-01-01T00:00:00Z")
    assert cy["title"] == "YAML conj"
    assert cy["references"] == ["https://example.org/a", "https://example.org/b"]
    assert "Every graph G has property Q." in cy["statement_canonical"]

    print("conjecture_intake self-test OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
