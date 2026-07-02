#!/usr/bin/env python3
"""Source-of-truth guard: every PROVEN_FORMULAS entry ↔ a real Lean declaration.

This is the SOURCE-side mirror of a11oy's served-formula registry guard (T101).
Where that check verifies the formulas a11oy *serves* against the corpus, this
check verifies the formulas lutar-lean *claims proven* in ``PROVEN_FORMULAS.md``
against the actual Lean theorem/lemma declarations in the repository's ``.lean``
files (the Lutar/Puriq/Formulas sources and everything else under ``Lutar/``).

The honest contract, per the szl-holdings doctrine:

  * Every entry the showcase labels **PROVEN** (the locked-kernel set, section 1)
    must resolve to a real Lean ``theorem``/``lemma``/``def`` DECLARATION that
    exists in the tree. Any named theorem that is absent is an *unbacked
    overclaim* — caught here, reported honestly, never listed as proven.
  * EXPERIMENTAL entries (section 2, CI-green waves) are labelled ``experimental``
    — reported, but never counted as proven and never a hard failure here.
  * Λ-uniqueness stays **Conjecture 1**, NEVER a theorem. The guard FAILS if the
    conjecture is ever shipped as a proof, if the showcase tags Λ-uniqueness as
    PROVEN, or if the machine-checked-false counterexample disappears.

Nothing here asserts "the AI is correct" — a resolved declaration is *evidence*
that the named theorem exists in the kernel sources, not a re-run of the kernel.

Usage:

    # Print the honest per-entry registry as JSON (exit 1 on any overclaim).
    python3 .github/scripts/check_proven_formulas.py --repo-path . --json

    # Human summary.
    python3 .github/scripts/check_proven_formulas.py --repo-path .

    # Self-test the checker against negative fixtures (no repo scan).
    python3 .github/scripts/check_proven_formulas.py --self-test
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys

# The locked-kernel proven set is EXACTLY these eight formula IDs. This mirrors
# the doc's own machine-enforced invariant (`locked_count_eight`, no axioms).
LOCKED_PROVEN_IDS = {"F1", "F4", "F7", "F11", "F12", "F18", "F19", "F22"}

# Λ-uniqueness is Conjecture 1: stated only as a `Prop`, machine-checked FALSE
# as-stated by this counterexample. Both anchors must hold for Λ to stay honest.
CONJECTURE_DEF = "Conjecture1_LambdaUnique"
LAMBDA_COUNTEREXAMPLE = "maxAgg_ne_Lambda"

# A served/locked formula must never smuggle a Λ-uniqueness claim into the
# proven set. If any locked theorem name matches this, it's an overclaim.
LAMBDA_CLAIM_TOKENS = ("lambda_unique", "lambda_uniqueness", "_lambdaunique")

# Lean declaration header: optional attributes + modifiers, then the keyword and
# the declaration name (up to the first whitespace/binder/type-ascription char).
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|scoped|local)\s+)*"
    r"(?P<kw>theorem|lemma|def)\s+"
    r"(?P<name>[^\s(){}\[\]:⦃⦄⟨⟩]+)"
)

NS_RE = re.compile(r"^\s*namespace\s+(\S+)")
END_RE = re.compile(r"^\s*end\s+(\S+)")

# A token inside a formula's parenthesised proof-name group looks like a Lean
# identifier, optionally namespaced, optionally a `*` prefix wildcard (e.g.
# `f18_*` meaning "the f18_ family").
NAME_TOKEN_RE = re.compile(r"^[A-Za-z][A-Za-z0-9_'.]*\*?$")


# ---------------------------------------------------------------------------
# Lean declaration index
# ---------------------------------------------------------------------------

def index_lean_decls(repo_root: str) -> dict:
    """Walk every .lean file and index declaration names by kind.

    Returns a dict with:
      * ``proof_bare``      — bare names of ``theorem``/``lemma`` decls
      * ``proof_qualified`` — fully-qualified names of ``theorem``/``lemma`` decls
      * ``def_bare``        — bare names of ``def`` decls
      * ``all_bare``        — bare names of any indexed decl (theorem/lemma/def)
      * ``all_qualified``   — fully-qualified names of any indexed decl
    """
    proof_bare: set[str] = set()
    proof_qualified: set[str] = set()
    def_bare: set[str] = set()
    all_bare: set[str] = set()
    all_qualified: set[str] = set()

    for dirpath, dirs, files in os.walk(repo_root):
        # Skip VCS + build artifacts.
        dirs[:] = [
            d for d in dirs
            if d not in {".git", ".lake", "lake-packages", "build", ".github"}
        ]
        for fn in files:
            if not fn.endswith(".lean"):
                continue
            abspath = os.path.join(dirpath, fn)
            try:
                with open(abspath, "r", encoding="utf-8", errors="replace") as fh:
                    text = fh.read()
            except OSError:
                continue
            ns_stack: list[str] = []
            for raw in text.splitlines():
                ns_m = NS_RE.match(raw)
                if ns_m:
                    ns_stack.append(ns_m.group(1))
                    continue
                end_m = END_RE.match(raw)
                if end_m and ns_stack:
                    # `end Foo` closes the matching namespace segment(s).
                    seg = end_m.group(1)
                    if ns_stack and ns_stack[-1].endswith(seg):
                        ns_stack.pop()
                    continue
                m = DECL_RE.match(raw)
                if not m:
                    continue
                name = m.group("name").strip(".")
                if not name:
                    continue
                prefix = ".".join(ns_stack)
                qualified = f"{prefix}.{name}" if prefix else name
                all_bare.add(name)
                all_qualified.add(qualified)
                if m.group("kw") in ("theorem", "lemma"):
                    proof_bare.add(name)
                    proof_qualified.add(qualified)
                else:
                    def_bare.add(name)
    return {
        "proof_bare": proof_bare,
        "proof_qualified": proof_qualified,
        "def_bare": def_bare,
        "all_bare": all_bare,
        "all_qualified": all_qualified,
    }


def _resolves(name: str, names_bare: set[str], names_qualified: set[str]) -> bool:
    """True if ``name`` matches a decl, bare/qualified/wildcard-prefix."""
    if name.endswith("*"):
        prefix = name[:-1]
        return any(b.startswith(prefix) for b in names_bare)
    if name in names_bare or name in names_qualified:
        return True
    # A namespaced reference (e.g. Round13.maxAgg_ne_Lambda) resolves if its
    # final segment is a known bare decl.
    if "." in name and name.rsplit(".", 1)[-1] in names_bare:
        return True
    return False


def proof_decl_exists(name: str, index: dict) -> bool:
    return _resolves(name, index["proof_bare"], index["proof_qualified"])


def any_decl_exists(name: str, index: dict) -> bool:
    return _resolves(name, index["all_bare"], index["all_qualified"])


# ---------------------------------------------------------------------------
# PROVEN_FORMULAS.md parsing
# ---------------------------------------------------------------------------

def _section(md_text: str, start_pat: str, *end_pats: str) -> str:
    """Return the slice of ``md_text`` from ``start_pat`` to the next end marker."""
    sm = re.search(start_pat, md_text, re.MULTILINE)
    if not sm:
        return ""
    start = sm.end()
    end = len(md_text)
    for ep in end_pats:
        em = re.search(ep, md_text[start:], re.MULTILINE)
        if em:
            end = min(end, start + em.start())
    return md_text[start:end]


def _table_rows(block: str) -> list[list[str]]:
    """Return the cells of every markdown table data row in ``block``."""
    rows: list[list[str]] = []
    for line in block.splitlines():
        line = line.strip()
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip("|").split("|")]
        # Skip header separators like |---|---|.
        if all(set(c) <= {"-", ":", ""} for c in cells):
            continue
        rows.append(cells)
    return rows


def _clean_id(cell: str) -> str:
    return cell.replace("*", "").strip()


def _proof_names_from_cell(cell: str) -> list[str]:
    """Extract Lean proof-name tokens from the parenthesised group(s) of a cell.

    Theorem names in the showcase live inside a trailing ``(...)`` group as
    backticked identifiers, e.g. ``Replay-Hash Determinism (`f1_a`, `f1_b`)`` or
    ``Reed–Solomon `RS(10,6)` Recovery Arithmetic (`f18_*`)``. We only harvest
    backticked tokens that sit INSIDE parentheses so descriptive backticks such
    as ``RS(10,6)`` are never mistaken for theorem names.
    """
    names: list[str] = []
    for group in re.findall(r"\(([^()]*)\)", cell):
        for tok in re.findall(r"`([^`]+)`", group):
            tok = tok.strip()
            if NAME_TOKEN_RE.match(tok):
                names.append(tok)
    return names


def parse_locked_entries(md_text: str) -> list[dict]:
    """Parse the section-1 locked-proven table into {formula_id, names}."""
    block = _section(
        md_text,
        r"^##\s+1\.\s+Locked kernel",
        r"^##\s+2\.",
    )
    entries: list[dict] = []
    for cells in _table_rows(block):
        if len(cells) < 4:
            continue
        formula_id = _clean_id(cells[0])
        maturity = cells[3]
        if "PROVEN" not in maturity.upper():
            continue
        names = _proof_names_from_cell(cells[1])
        entries.append({"formula_id": formula_id, "names": names})
    return entries


def parse_experimental_entries(md_text: str) -> list[dict]:
    """Parse the section-2.2 Wave-8 experimental table into {formula_id, names}."""
    block = _section(
        md_text,
        r"^###\s+2\.2\s+Wave-8",
        r"^##\s+3\.",
        r"^>\s+Wave-8 is",
    )
    entries: list[dict] = []
    for cells in _table_rows(block):
        if len(cells) < 2:
            continue
        formula_id = _clean_id(cells[0])
        names = [
            t.strip()
            for t in re.findall(r"`([^`]+)`", cells[1])
            if NAME_TOKEN_RE.match(t.strip())
        ]
        if not names:
            continue
        entries.append({"formula_id": formula_id, "names": names})
    return entries


# ---------------------------------------------------------------------------
# Registry + verdicts
# ---------------------------------------------------------------------------

def build_registry(index: dict, md_text: str) -> list[dict]:
    """Build the honest per-entry registry over locked + experimental entries."""
    registry: list[dict] = []

    for entry in parse_locked_entries(md_text):
        fid = entry["formula_id"]
        for name in entry["names"]:
            exists = proof_decl_exists(name, index)
            registry.append({
                "formula_id": fid,
                "name": name,
                "claimed_maturity": "proven",
                "lean_decl_exists": exists,
                "status": "verified" if exists else "unbacked",
            })

    for entry in parse_experimental_entries(md_text):
        fid = entry["formula_id"]
        for name in entry["names"]:
            registry.append({
                "formula_id": fid,
                "name": name,
                "claimed_maturity": "experimental",
                "lean_decl_exists": any_decl_exists(name, index),
                "status": "experimental",
            })

    return registry


def lambda_violations(index: dict, md_text: str) -> list[str]:
    """Return honesty violations that would tag Λ-uniqueness as proven."""
    violations: list[str] = []

    # 1. Conjecture 1 must exist ONLY as a `def` statement, never as a proof.
    if CONJECTURE_DEF not in index["def_bare"]:
        violations.append(
            f"{CONJECTURE_DEF} (Conjecture 1) is not declared as a Lean `def` "
            "statement — the honest OPEN obligation is missing."
        )
    if CONJECTURE_DEF in index["proof_bare"]:
        violations.append(
            f"{CONJECTURE_DEF} is declared as a theorem/lemma — Λ-uniqueness must "
            "stay Conjecture 1, NEVER a proven theorem."
        )

    # 2. The machine-checked-FALSE counterexample must remain a real theorem.
    if not proof_decl_exists(LAMBDA_COUNTEREXAMPLE, index):
        violations.append(
            f"{LAMBDA_COUNTEREXAMPLE} counterexample theorem is absent — nothing "
            "keeps Λ-uniqueness machine-checked false."
        )

    # 3. No locked-proven theorem name may be a Λ-uniqueness claim.
    for entry in parse_locked_entries(md_text):
        for name in entry["names"]:
            low = name.lower()
            if any(tok in low for tok in LAMBDA_CLAIM_TOKENS):
                violations.append(
                    f"Locked-proven entry {entry['formula_id']} names "
                    f"'{name}' — a Λ-uniqueness claim must never be in the "
                    "proven set."
                )

    # 4. The Conjecture-1 row in the doc must be OPEN, never PROVEN/REAL·PROVEN.
    conj_block = _section(md_text, r"^##\s+3\.", r"^##\s+4\.")
    for line in conj_block.splitlines():
        if CONJECTURE_DEF in line:
            upper = line.upper()
            if "OPEN" not in upper:
                violations.append(
                    "Conjecture 1 row in section 3 no longer marked OPEN: "
                    f"{line.strip()}"
                )
            if re.search(r"\bPROVEN\b", upper) or "REAL · PROVEN" in upper:
                violations.append(
                    "Conjecture 1 row tags the conjecture PROVEN: "
                    f"{line.strip()}"
                )

    return violations


def locked_id_violations(md_text: str) -> list[str]:
    """The locked-proven set must be exactly the eight canonical formula IDs."""
    found = {e["formula_id"] for e in parse_locked_entries(md_text)}
    violations: list[str] = []
    missing = LOCKED_PROVEN_IDS - found
    extra = found - LOCKED_PROVEN_IDS
    if missing:
        violations.append(
            f"Locked proven set is missing expected IDs: {sorted(missing)}"
        )
    if extra:
        violations.append(
            f"Locked proven set has unexpected IDs (locked count must stay 8): "
            f"{sorted(extra)}"
        )
    return violations


def evaluate(repo_root: str) -> dict:
    """Full verdict: registry + all violation classes."""
    md_path = os.path.join(repo_root, "PROVEN_FORMULAS.md")
    with open(md_path, "r", encoding="utf-8") as fh:
        md_text = fh.read()
    index = index_lean_decls(repo_root)
    registry = build_registry(index, md_text)
    unbacked = [r for r in registry if r["status"] == "unbacked"]
    result = {
        "registry": registry,
        "counts": {
            "verified": sum(1 for r in registry if r["status"] == "verified"),
            "unbacked": len(unbacked),
            "experimental": sum(
                1 for r in registry if r["status"] == "experimental"
            ),
        },
        "unbacked": unbacked,
        "lambda_violations": lambda_violations(index, md_text),
        "locked_id_violations": locked_id_violations(md_text),
    }
    result["ok"] = (
        not unbacked
        and not result["lambda_violations"]
        and not result["locked_id_violations"]
    )
    return result


# ---------------------------------------------------------------------------
# Self-test (negative fixtures — trust the checker before trusting the repo)
# ---------------------------------------------------------------------------

def _self_test() -> int:
    fake_index = {
        "proof_bare": {"f1_real", "maxAgg_ne_Lambda"},
        "proof_qualified": {"maxAgg_ne_Lambda"},
        "def_bare": {"Conjecture1_LambdaUnique"},
        "all_bare": {"f1_real", "maxAgg_ne_Lambda", "Conjecture1_LambdaUnique"},
        "all_qualified": set(),
    }

    # (a) An unbacked proven entry must be caught.
    md_unbacked = (
        "## 1. Locked kernel — proven, sorry-free\n"
        "| ID | Theorem | What | Maturity | ax |\n"
        "|---|---|---|---|---|\n"
        "| **F1** | Real (`f1_real`) | x | **PROVEN** | core |\n"
        "| **F99** | Bogus (`f99_does_not_exist`) | x | **PROVEN** | core |\n"
    )
    reg = build_registry(fake_index, md_unbacked)
    statuses = {r["name"]: r["status"] for r in reg}
    assert statuses.get("f1_real") == "verified", statuses
    assert statuses.get("f99_does_not_exist") == "unbacked", statuses

    # (b) a Λ-uniqueness entry falsely tagged proven must be caught (it stays Conjecture 1).
    bad_index = dict(fake_index)
    bad_index["proof_bare"] = fake_index["proof_bare"] | {"Conjecture1_LambdaUnique"}
    viol = lambda_violations(bad_index, md_unbacked)
    assert any("NEVER a proven theorem" in v for v in viol), viol

    # (c) A locked entry naming a Λ-uniqueness claim must be caught.
    md_lambda_claim = (
        "## 1. Locked kernel — proven, sorry-free\n"
        "| ID | Theorem | What | Maturity | ax |\n"
        "|---|---|---|---|---|\n"
        "| **F1** | Lambda (`lambda_unique_bad`) | x | **PROVEN** | core |\n"
    )
    viol2 = lambda_violations(fake_index, md_lambda_claim)
    assert any("never be in the" in v for v in viol2), viol2

    # (d) Missing counterexample must be caught.
    no_ce = dict(fake_index)
    no_ce["proof_bare"] = {"f1_real"}
    no_ce["proof_qualified"] = set()
    viol3 = lambda_violations(no_ce, md_unbacked)
    assert any("machine-checked false" in v for v in viol3), viol3

    # (e) Wildcard + namespaced resolution.
    assert _resolves("f1_*", {"f1_a", "f1_b"}, set())
    assert _resolves("Round13.maxAgg_ne_Lambda", {"maxAgg_ne_Lambda"}, set())
    assert not _resolves("nope_*", {"f1_a"}, set())

    print("self-test OK")
    return 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo-path", default=".", help="repository root")
    ap.add_argument("--json", action="store_true", help="emit JSON verdict")
    ap.add_argument("--self-test", action="store_true", help="run negative fixtures")
    args = ap.parse_args(argv)

    if args.self_test:
        return _self_test()

    result = evaluate(args.repo_path)

    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        c = result["counts"]
        print(
            f"PROVEN_FORMULAS registry: {c['verified']} verified · "
            f"{c['unbacked']} unbacked · {c['experimental']} experimental"
        )
        for r in result["registry"]:
            mark = {"verified": "OK ", "unbacked": "!! ", "experimental": "~~ "}[
                r["status"]
            ]
            print(
                f"  {mark}{r['formula_id']:<5} {r['name']:<40} "
                f"decl={r['lean_decl_exists']} status={r['status']}"
            )
        for v in result["locked_id_violations"]:
            print(f"  LOCKED-SET VIOLATION: {v}")
        for v in result["lambda_violations"]:
            print(f"  Λ VIOLATION: {v}")
        print("VERDICT:", "OK" if result["ok"] else "FAIL")

    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
