#!/usr/bin/env python3
"""Build (or --check) the pinned estate Lean benchmark corpus.

szl.lutar.estate-lean-eval/v1 — the estate's own math, pinned VERBATIM as
immutable benchmark targets (the AxiomMath `weil_conjectures` lean-eval
pattern, applied to OUR kernel):

  benchmark/estate_pinned_v1.jsonl   one row per pinned statement
  benchmark/MANIFEST.json           counts + corpus commit + self-sha

What is pinned (statements only, NEVER proof claims):
  kind=locked8     the 24 carrier theorems of the locked-8 formulas
                   {F1,F4,F7,F11,F12,F18,F19,F22} — authority:
                   claims/locked-formulas.v1.json (COMPILED_LOCKED_SURFACE)
  kind=theorem_u   the 6 headline Theorem-U declarations — authority: the
                   szl-lake anchor receipt (REAL-conditional; Conjecture 1
                   OPEN, machine-checked FALSE unconditionally)
  kind=putnam      every declaration in Lutar/Putnam/P_[AB][0-9].lean —
                   status is MACHINE-DERIVED (sorry_free / sorry_open);
                   no REAL/DEMO claims here (PhD gate owns those)
  kind=sorry_open  every tracked `sorry` target in the compiled corpus,
                   one row per sorry occurrence — the self-proving loop
                   consumes THESE (states, not whole files)

Honesty rules (fail-closed):
  - Every row carries statement_sha256 + block_sha256 of the VERBATIM
    extracted text. The --check mode regenerates from the repo at HEAD and
    hard-fails on any byte drift: a statement cannot change without this
    file changing, and this file cannot claim a statement the repo does not
    contain.
  - `status` is derived, not asserted: PROVEN rows come only from the
    locked-8 claims file; nothing else is ever labelled PROVEN.
  - No timestamps, no randomness: the build is byte-deterministic.

Usage:
  python3 tools/build_estate_benchmark.py            # build (writes benchmark/)
  python3 tools/build_estate_benchmark.py --check    # verify, exit 1 on drift
"""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BENCH_DIR = ROOT / "benchmark"
CORPUS_PATH = BENCH_DIR / "estate_pinned_v1.jsonl"
MANIFEST_PATH = BENCH_DIR / "MANIFEST.json"
CLAIMS_PATH = ROOT / "claims" / "locked-formulas.v1.json"
SORRY_GATE_PATH = ROOT / ".github" / "workflows" / "sorry-gate.yml"

SCHEMA = "szl.lutar.estate-lean-eval/v1"

# Compiled-corpus scope mirrors count_sorries.py (proposals/ excluded), plus
# this tooling's own directories are excluded (they are not corpus math).
EXCLUDED_TOP = {"proposals", "benchmark", "tools", ".lake", ".git", "assets"}

def _sorry_baseline() -> int:
    """Read the one authoritative, literal compiled-corpus CI pin.

    Do not encode a count in this benchmark generator: a pin ratchet
    must update the generated manifest or the --check gate must fail.
    """
    try:
        source = SORRY_GATE_PATH.read_text(encoding="utf-8")
    except (OSError, UnicodeError):
        raise ValueError("SORRY_GATE_UNAVAILABLE") from None
    matches = re.findall(r'(?m)^\s+SORRY_BASELINE:\s*"([1-9][0-9]{0,5})"\s*$', source)
    if len(matches) != 1:
        raise ValueError("SORRY_GATE_PIN_UNAVAILABLE_OR_AMBIGUOUS")
    return int(matches[0])


DECL_RE = re.compile(r"^(theorem|lemma|def|abbrev)\b")
SORRY_RE = re.compile(r"\bsorry\b")
HEADLINE_U = [
    "CorollaryU1_LambdaUnique_Separable",
    "CorollaryU2_LambdaUnique_Factors",
    "TheoremU_LambdaUnique",
    "TheoremU_LambdaUnique_eq",
    "identifiability_forces_lambda",
    "lambda_equiv_to_eq_of_anchored",
]

def _strip_comments(text: str) -> str:
    """Comment-strip Lean source with a NESTED block-comment state machine.

    Line-aligned (same number of lines, same per-line prefixes) so stripped
    output can be used for decl-boundary detection while raw lines are kept
    for verbatim pinning. Handles /- -/ nesting and -- line comments; a `--`
    inside an open block comment stays a comment (correct Lean behaviour).
    """
    out_lines = []
    depth = 0
    for line in text.splitlines():
        chars = []
        i = 0
        n = len(line)
        while i < n:
            if depth > 0:
                if line.startswith("/-", i) or line.startswith("/--", i) or (line[i] == "/" and i + 1 < n and line[i + 1] == "-"):
                    depth += 1
                    i += 2
                elif line.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            else:
                if line[i] == "/" and i + 1 < n and line[i + 1] == "-":
                    depth += 1
                    i += 2
                elif line[i] == "-" and i + 1 < n and line[i + 1] == "-":
                    break  # rest of the line is a line comment
                else:
                    chars.append(line[i])
                    i += 1
        out_lines.append("".join(chars))
    return "\n".join(out_lines)

def _decl_name(line: str):
    m = re.match(r"^(?:theorem|lemma|def|abbrev)\s+([A-Za-z_][A-Za-z0-9_!?']*)", line)
    return m.group(1) if m else None

def _blocks(path: Path):
    """Yield (name, start_line, block_text) for top-level decl blocks.

    Boundaries are detected on the comment-stripped text (a `theorem` inside
    a block comment is NOT a boundary); the pinned block text is the RAW
    verbatim source slice.
    """
    raw = path.read_text(encoding="utf-8", errors="replace").splitlines()
    stripped = _strip_comments("\n".join(raw)).splitlines()
    starts = []
    for i, line in enumerate(stripped):
        if DECL_RE.match(line):
            starts.append(i)
    for k, s in enumerate(starts):
        e = starts[k + 1] if k + 1 < len(starts) else len(raw)
        block = "\n".join(raw[s:e]).rstrip() + "\n"
        yield _decl_name(stripped[s]), s + 1, block

def _statement(block: str):
    """Verbatim statement: decl through binders/type, up to (not incl.) := ."""
    stripped = _strip_comments(block)
    i = stripped.find(":=")
    if i == -1:
        return block.rstrip()
    # Map back onto the raw text: the := column in the stripped text may
    # differ from raw only through comment removal *within earlier lines*;
    # comments inside a signature are rare, and the statement is hashed raw.
    raw_i = block.find(":=")
    if raw_i == -1 or stripped[:i].rstrip() != _strip_comments(block[:raw_i]).rstrip():
        # comment inside the signature: fall back to stripped-truth
        return stripped[:i].rstrip()
    return block[:raw_i].rstrip()

def _sha(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()

def _corpus_files():
    for p in sorted(ROOT.rglob("*.lean")):
        rel = p.relative_to(ROOT)
        if rel.parts[0] in EXCLUDED_TOP:
            continue
        yield rel.as_posix(), p

def _locked8_carriers():
    claims = json.loads(CLAIMS_PATH.read_text(encoding="utf-8"))
    carriers = {}
    for c in claims["claims"]:
        for t in c["theorem_declarations"]:
            carriers[t] = c["claim_id"]
    return claims, carriers

def build_corpus():
    claims, carriers = _locked8_carriers()
    rows = []
    for rel, path in _corpus_files():
        putnam = bool(re.match(r"Lutar/Putnam/P_[AB][0-9]\.lean$", rel))
        for name, start, block in _blocks(path):
            if name is None:
                continue
            sorry_n = len(SORRY_RE.findall(_strip_comments(block)))
            stmt = _statement(block)
            if name in carriers and rel == claims["compiled_path"]:
                # Locked-8 carriers are pinned ONLY in the compiled surface
                # (claims file: "locked showcase names must be exact
                # LockedGuard carriers, not unbuilt PuriqFormulaLean.lean
                # aliases"). Name matches outside compiled_path are aliases
                # and are NOT pinned as locked-8.
                kind, claim_id = "locked8", carriers[name]
                status = "PROVEN"
            elif name in HEADLINE_U:
                kind, claim_id = "theorem_u", None
                status = "REAL-CONDITIONAL"
            elif putnam:
                kind, claim_id = "putnam", None
                status = "sorry_free" if sorry_n == 0 else "sorry_open"
            else:
                kind, claim_id, status = None, None, None
            base = {
                "schema": SCHEMA,
                "kind": kind,
                "name": name,
                "claim_id": claim_id,
                "source_path": rel,
                "start_line": start,
                "statement": stmt,
                "statement_sha256": _sha(stmt),
                "block_sha256": _sha(block),
                "sorry_count": sorry_n,
                "status": status,
            }
            if kind is not None:
                rows.append(dict(base, sorry_index=None))
            if sorry_n:
                for idx in range(1, sorry_n + 1):
                    rows.append(dict(base, kind="sorry_open", claim_id=None,
                                     status="OPEN", sorry_index=idx))
    rows.sort(key=lambda r: (r["kind"], r["source_path"], r["start_line"],
                             r["name"], r["sorry_index"] or 0))
    manifest = {
        "schema": SCHEMA + "/manifest",
        "authority": {
            "locked8": "claims/locked-formulas.v1.json (COMPILED_LOCKED_SURFACE)",
            "theorem_u": "szl-lake anchor: REAL-conditional; Conjecture 1 OPEN, machine-checked FALSE",
            "sorry_gate": f"SORRIES.md pinned baseline {_sorry_baseline()} (no-increase)",
        },
        "locked8_carriers": len(carriers),
        "theorem_u_decls": len(HEADLINE_U),
        "counts": {},
        "total_sorry_rows": 0,
    }
    for r in rows:
        manifest["counts"][r["kind"]] = manifest["counts"].get(r["kind"], 0) + 1
    manifest["total_sorry_rows"] = manifest["counts"].get("sorry_open", 0)
    payload = "".join(json.dumps(r, ensure_ascii=False, sort_keys=True) + "\n"
                     for r in rows)
    manifest["corpus_sha256"] = _sha(payload)
    manifest["corpus_rows"] = len(rows)
    return payload, manifest

def main(argv):
    payload, manifest = build_corpus()
    if "--check" in argv:
        ok = True
        if not CORPUS_PATH.exists():
            print("BENCH_DRIFT corpus file missing"); ok = False
        else:
            current = CORPUS_PATH.read_text(encoding="utf-8")
            if current != payload:
                print("BENCH_DRIFT corpus bytes differ from repo sources")
                a = current.splitlines(); b = payload.splitlines()
                for i, (x, y) in enumerate(zip(a, b)):
                    if x != y:
                        print("  first diff at row", i + 1); break
                print("  file rows:", len(a), "repo rows:", len(b))
                ok = False
        if MANIFEST_PATH.exists():
            m = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
            for key in ("corpus_sha256", "corpus_rows", "total_sorry_rows", "counts"):
                if m.get(key) != manifest.get(key):
                    print("BENCH_MANIFEST_DRIFT", key, m.get(key), "!=", manifest.get(key))
                    ok = False
        else:
            print("BENCH_MANIFEST_MISSING"); ok = False
        # Cross-gate: corpus sorry rows must equal the repo's own sorry gate
        # (count_sorries.py compiled-scope TOTAL). Fail-closed on divergence.
        cs = subprocess.run([sys.executable, str(ROOT / "count_sorries.py")],
                            cwd=ROOT, capture_output=True, text=True, timeout=120)
        m = re.search(r"TOTAL_SORRIES=(\d+)", cs.stdout or "")
        if m:
            if int(m.group(1)) != manifest["total_sorry_rows"]:
                print("BENCH_SORRY_GATE_MISMATCH count_sorries",
                      m.group(1), "!= corpus sorry_open rows",
                      manifest["total_sorry_rows"])
                ok = False
        else:
            print("BENCH_SORRY_GATE_UNREADABLE count_sorries.py output parse failed")
            ok = False
        print("BENCH_CHECK", "OK" if ok else "FAILED",
              "rows:", manifest["corpus_rows"],
              "sorry_rows:", manifest["total_sorry_rows"])
        sys.exit(0 if ok else 1)
    BENCH_DIR.mkdir(exist_ok=True)
    CORPUS_PATH.write_text(payload, encoding="utf-8")
    MANIFEST_PATH.write_text(
        json.dumps(manifest, ensure_ascii=False, indent=1, sort_keys=True) + "\n",
        encoding="utf-8")
    print("BENCH_BUILT rows:", manifest["corpus_rows"],
          "sorry_rows:", manifest["total_sorry_rows"],
          "counts:", manifest["counts"])

if __name__ == "__main__":
    main(sys.argv[1:])
