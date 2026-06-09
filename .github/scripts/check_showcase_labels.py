#!/usr/bin/env python3
"""Showcase REAL/DEMO label honesty gate.

The Putnam formalization showcase (`Showcase/PutnamLean/*.lean`) labels every
problem either **REAL** (kernel-checked, zero `sorry`, only in-policy Lean-core
axioms) or **DEMO** (statement formalized, proof is `sorry`). The claimed label
is declared in the human-readable writeup `Showcase/Putnam/<id>.md`
("Honesty label: REAL/DEMO"). Nothing previously enforced that the label matches
what the Lean kernel actually accepts — a file marked REAL could silently start
using `sorry` or pull an out-of-policy axiom, and a DEMO could be quietly
finished without being relabeled. Because the showcase lives OUTSIDE `Lutar/`,
the canonical numbers/drift gate (`lean_numbers.py`) does not cover it.

This gate keeps the label and the proof in lockstep:

  * the claimed label is read from `Showcase/Putnam/<stem>.md` (paired by the
    Lean file's stem, e.g. `P01.lean` <-> `P01.md`), so the two cannot drift;
  * **REAL** must contain ZERO non-comment `sorry`; **DEMO** must contain at
    least one non-comment `sorry` (i.e. a DEMO that is actually finished must be
    promoted/relabeled);
  * with `--with-axioms` (CI, after `lake build`), each REAL theorem's
    `#print axioms` footprint must be free of `sorryAx` and a subset of the
    in-policy Lean-core axioms {propext, Classical.choice, Quot.sound}, and each
    DEMO file must have at least one theorem whose footprint contains `sorryAx`.

`sorry` detection strips Lean comments first (both `--` line comments and nested
`/- -/` block comments) so prose like "zero `sorry`" inside a REAL file's
doc-comment is not mistaken for a real proof hole.

Exit codes: 0 = all labels honest, 1 = a mismatch, 2 = usage / structural error.

Usage:
  # Static gate (no Lean toolchain needed): labels vs `sorry`.
  python3 check_showcase_labels.py --repo-path .

  # Full gate (CI, after `lake build`): also verify REAL axiom footprints.
  python3 check_showcase_labels.py --repo-path . --with-axioms

  # Offline parser self-tests (no lean, no repo).
  python3 check_showcase_labels.py --self-test
"""
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys

# Showcase layout (repo-relative).
LEAN_DIR = os.path.join("Showcase", "PutnamLean")
WRITEUP_DIR = os.path.join("Showcase", "Putnam")

# In-policy Lean-core axioms a REAL proof may depend on. The showcase is
# Mathlib-free / core-only, so the policy is exactly the kernel set (no declared
# repo axioms are allowed here). Mirrors the {propext, Classical.choice,
# Quot.sound} policy used for Lutar/ in gen_verified_theorems.py.
KERNEL_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
SORRY_AX = "sorryAx"

# Canonical label declaration in the writeup, e.g. "## Honesty label: REAL".
LABEL_RE = re.compile(r"Honesty label:\s*\*{0,2}(REAL|DEMO)\*{0,2}", re.IGNORECASE)
# Fallback: the H1 title token, e.g. "# P01 — Putnam 2001 A1  ·  **REAL**".
TITLE_LABEL_RE = re.compile(r"^#\s.*\*\*(REAL|DEMO)\*\*", re.IGNORECASE | re.MULTILINE)

SORRY_RE = re.compile(r"\bsorry\b")

# Declaration header (theorem/lemma name); we read it from comment-masked source
# so prose mentions never match. `def`/`instance`/... are intentionally ignored.
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:noncomputable\s+)?(?:private\s+)?"
    r"(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'!]*)"
)
NS_RE = re.compile(r"^namespace\s+(\S+)\s*$")
END_RE = re.compile(r"^end(?:\s+(\S+))?\s*$")

# #print axioms output (robust to lean's location-prefixed, line-wrapped messages).
AX_DEPENDS_RE = re.compile(r"'([^']+)' depends on axioms: \[(.*?)\]", re.DOTALL)
AX_NONE_RE = re.compile(r"'([^']+)' does not depend on any axioms")


# ---------------------------------------------------------------------------
# Comment-aware source handling
# ---------------------------------------------------------------------------
def mask_comments(text: str) -> str:
    """Replace Lean comments with spaces (newlines preserved) so token scans
    ignore `--` line comments and nested `/- -/` block comments."""
    res = list(text)
    i, n = 0, len(text)
    depth = 0
    line_comment = False
    while i < n:
        c = text[i]
        if line_comment:
            if c == "\n":
                line_comment = False
            else:
                res[i] = " "
            i += 1
            continue
        if depth > 0:
            if text[i:i + 2] == "/-":
                res[i] = res[i + 1] = " "
                depth += 1
                i += 2
                continue
            if text[i:i + 2] == "-/":
                res[i] = res[i + 1] = " "
                depth -= 1
                i += 2
                continue
            if c != "\n":
                res[i] = " "
            i += 1
            continue
        if text[i:i + 2] == "/-":
            res[i] = res[i + 1] = " "
            depth += 1
            i += 2
            continue
        if text[i:i + 2] == "--":
            res[i] = res[i + 1] = " "
            line_comment = True
            i += 2
            continue
        i += 1
    return "".join(res)


def find_real_sorries(text: str) -> list[int]:
    """1-based line numbers of `sorry` tokens that are NOT inside a comment."""
    masked = mask_comments(text)
    return [masked.count("\n", 0, m.start()) + 1 for m in SORRY_RE.finditer(masked)]


def parse_theorems(text: str) -> list[str]:
    """Fully-qualified theorem/lemma names declared in `text` (comment-masked)."""
    masked = mask_comments(text)
    ns_stack: list[str] = []
    names: list[str] = []
    for line in masked.splitlines():
        stripped = line.strip()
        m_ns = NS_RE.match(stripped)
        if m_ns:
            ns_stack.append(m_ns.group(1))
            continue
        if END_RE.match(stripped):
            if ns_stack:
                ns_stack.pop()
            continue
        m_decl = DECL_RE.match(line)
        if m_decl:
            ns = ".".join(ns_stack)
            name = m_decl.group(1)
            names.append(f"{ns}.{name}" if ns else name)
    return names


# ---------------------------------------------------------------------------
# Writeup label
# ---------------------------------------------------------------------------
def read_label(md_path: str) -> str | None:
    """Return 'REAL'/'DEMO' from a writeup, or None if absent/ambiguous."""
    with open(md_path, "r", encoding="utf-8", errors="replace") as fh:
        text = fh.read()
    labels = {m.group(1).upper() for m in LABEL_RE.finditer(text)}
    if not labels:
        m = TITLE_LABEL_RE.search(text)
        if m:
            labels = {m.group(1).upper()}
    if len(labels) == 1:
        return labels.pop()
    return None  # missing (0) or conflicting (>1)


def module_of(lean_path: str) -> str:
    """Importable module root for a Showcase/PutnamLean file (srcDir is flat)."""
    return os.path.splitext(os.path.basename(lean_path))[0]


# ---------------------------------------------------------------------------
# Axiom footprint audit (needs the Lean toolchain + a warm build)
# ---------------------------------------------------------------------------
def build_audit(modules: list[str], theorems: list[str]) -> str:
    lines = [
        "-- AUTO-GENERATED by .github/scripts/check_showcase_labels.py — do NOT commit.",
        "-- Footprint audit: one `#print axioms` per showcase theorem.",
    ]
    lines += [f"import {m}" for m in modules]
    lines.append("")
    lines += [f"#print axioms {fqn}" for fqn in theorems]
    return "\n".join(lines) + "\n"


def parse_footprints(output: str) -> dict[str, set[str]]:
    fps: dict[str, set[str]] = {}
    for m in AX_NONE_RE.finditer(output):
        fps[m.group(1)] = set()
    for m in AX_DEPENDS_RE.finditer(output):
        items = [s.strip() for s in m.group(2).split(",")]
        fps[m.group(1)] = {s for s in items if s}
    return fps


def run_audit(root: str, audit_text: str) -> str:
    audit_path = os.path.join(root, ".showcase_labels_audit.lean")
    with open(audit_path, "w", encoding="utf-8") as fh:
        fh.write(audit_text)
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", ".showcase_labels_audit.lean"],
            cwd=root, capture_output=True, text=True,
        )
    finally:
        try:
            os.remove(audit_path)
        except OSError:
            pass
    out = (proc.stdout or "") + "\n" + (proc.stderr or "")
    if proc.returncode != 0:
        sys.stderr.write(
            "::warning::`lake env lean` exited %d during showcase footprint audit.\n"
            "----- audit output (head) -----\n%s\n" % (proc.returncode, out[:4000])
        )
    return out


# ---------------------------------------------------------------------------
# Gate
# ---------------------------------------------------------------------------
def gather(root: str) -> tuple[list[dict], list[str]]:
    """Return (per-file records, errors). One record per Showcase Lean file."""
    errors: list[str] = []
    lean_base = os.path.join(root, LEAN_DIR)
    if not os.path.isdir(lean_base):
        errors.append(f"showcase Lean directory not found: {LEAN_DIR}/")
        return [], errors
    records: list[dict] = []
    for fn in sorted(os.listdir(lean_base)):
        if not fn.endswith(".lean"):
            continue
        lean_path = os.path.join(lean_base, fn)
        stem = os.path.splitext(fn)[0]
        md_rel = os.path.join(WRITEUP_DIR, stem + ".md")
        md_path = os.path.join(root, md_rel)
        with open(lean_path, "r", encoding="utf-8", errors="replace") as fh:
            text = fh.read()
        if not os.path.isfile(md_path):
            errors.append(
                f"{os.path.join(LEAN_DIR, fn)}: no writeup {md_rel} to derive a "
                f"label from (every showcase Lean file needs a paired writeup)."
            )
            continue
        label = read_label(md_path)
        if label is None:
            errors.append(
                f"{md_rel}: could not derive an unambiguous REAL/DEMO label "
                f"(expected exactly one 'Honesty label: REAL|DEMO')."
            )
            continue
        records.append({
            "lean_rel": os.path.join(LEAN_DIR, fn),
            "md_rel": md_rel,
            "module": module_of(fn),
            "label": label,
            "sorries": find_real_sorries(text),
            "theorems": parse_theorems(text),
        })
    return records, errors


def check_static(records: list[dict]) -> list[str]:
    errors: list[str] = []
    for r in records:
        n = len(r["sorries"])
        if r["label"] == "REAL" and n:
            where = ", ".join(str(x) for x in r["sorries"])
            errors.append(
                f"{r['lean_rel']}: labeled REAL (per {r['md_rel']}) but has "
                f"{n} non-comment `sorry` (line(s) {where}). A REAL file must be "
                f"kernel-checked with zero `sorry` — fix the proof or relabel DEMO."
            )
        if r["label"] == "DEMO" and n == 0:
            errors.append(
                f"{r['lean_rel']}: labeled DEMO (per {r['md_rel']}) but contains "
                f"zero non-comment `sorry`. If the proof is complete, promote it "
                f"to REAL; otherwise the DEMO label is misleading."
            )
    return errors


def check_axioms(root: str, records: list[dict]) -> list[str]:
    errors: list[str] = []
    modules = [r["module"] for r in records if r["theorems"]]
    all_theorems = [t for r in records for t in r["theorems"]]
    if not all_theorems:
        return errors
    output = run_audit(root, build_audit(modules, all_theorems))
    fps = parse_footprints(output)

    for r in records:
        if not r["theorems"]:
            continue
        demo_has_sorryax = False
        for fqn in r["theorems"]:
            fp = fps.get(fqn)
            if fp is None:
                errors.append(
                    f"{r['lean_rel']}: `#print axioms {fqn}` produced no footprint "
                    f"(unknown constant / elaboration error). Build must be warm."
                )
                continue
            if r["label"] == "REAL":
                if SORRY_AX in fp:
                    errors.append(
                        f"{r['lean_rel']}: labeled REAL but `{fqn}` depends on "
                        f"`sorryAx` — it is not kernel-checked. Fix or relabel DEMO."
                    )
                bad = sorted(a for a in fp if a not in KERNEL_AXIOMS)
                if bad:
                    errors.append(
                        f"{r['lean_rel']}: labeled REAL but `{fqn}` pulls "
                        f"out-of-policy axiom(s): {', '.join(bad)}. REAL allows "
                        f"only {{propext, Classical.choice, Quot.sound}}."
                    )
            elif r["label"] == "DEMO":
                if SORRY_AX in fp:
                    demo_has_sorryax = True
        if r["label"] == "DEMO" and not demo_has_sorryax:
            errors.append(
                f"{r['lean_rel']}: labeled DEMO but no theorem depends on "
                f"`sorryAx` (every proof is complete). Promote it to REAL or "
                f"correct the label."
            )
    return errors


def run_gate(root: str, with_axioms: bool) -> int:
    records, errors = gather(root)
    if not errors and not records:
        errors.append("no Showcase Lean files found — nothing to verify.")
    errors += check_static(records)
    if with_axioms and records:
        errors += check_axioms(root, records)

    for r in records:
        n = len(r["sorries"])
        print(f"  {r['lean_rel']}: label={r['label']} "
              f"sorries={n} theorems={len(r['theorems'])} (writeup {r['md_rel']})")

    if errors:
        print(f"::error::showcase label honesty gate FAILED "
              f"({len(errors)} problem(s)):")
        for e in errors:
            print(f"  - {e}")
        return 1
    mode = "static + axioms" if with_axioms else "static"
    print(f"showcase label honesty gate: PASS ({len(records)} file(s), {mode}).")
    return 0


# ---------------------------------------------------------------------------
# Self-test (offline; no lean / no repo)
# ---------------------------------------------------------------------------
def self_test() -> int:
    ok = True

    def check(cond, msg):
        nonlocal ok
        if not cond:
            ok = False
            print(f"SELF-TEST FAIL: {msg}")

    # Comment masking: prose `sorry` inside doc / line comments is invisible.
    real_src = (
        "/-\nComplete, kernel-checked proof with zero `sorry`.\n-/\n"
        "namespace Showcase.Putnam\n"
        "theorem foo : True := by trivial  -- not a sorry here\n"
        "end Showcase.Putnam\n"
    )
    check(find_real_sorries(real_src) == [], "REAL doc-comment `sorry` ignored")
    check(parse_theorems(real_src) == ["Showcase.Putnam.foo"], "theorem fqn parse")

    demo_src = (
        "/- the proof is `sorry`; #print axioms would report `sorryAx` -/\n"
        "namespace Showcase.Putnam\n"
        "theorem bar : True := by\n  sorry\n"
        "end Showcase.Putnam\n"
    )
    sorries = find_real_sorries(demo_src)
    check(sorries == [4], f"DEMO real `sorry` found at line 4 -> {sorries}")
    check(parse_theorems(demo_src) == ["Showcase.Putnam.bar"], "demo theorem parse")

    # Nested block comments.
    nested = "/- outer /- inner sorry -/ still comment sorry -/\nx sorry\n"
    check(find_real_sorries(nested) == [2], "nested block comment masking")

    # Label parsing: canonical line, title fallback, ambiguity.
    check(read_label_from_text("## Honesty label: REAL\n") == "REAL", "label REAL")
    check(read_label_from_text("## Honesty label: **DEMO**\n") == "DEMO", "label DEMO bold")
    check(read_label_from_text("# P01 — foo · **REAL**\nbody\n") == "REAL", "title fallback")
    check(read_label_from_text("no label here\n") is None, "missing label -> None")
    check(read_label_from_text(
        "## Honesty label: REAL\n## Honesty label: DEMO\n") is None,
        "conflicting labels -> None")

    # Footprint parsing + policy.
    out = (
        "a.lean:1:0: information: 'Showcase.Putnam.foo' does not depend on any axioms\n"
        "a.lean:2:0: information: 'Showcase.Putnam.cube' depends on axioms: [propext]\n"
        "a.lean:3:0: information: 'Showcase.Putnam.bar' depends on axioms: "
        "[propext,\n sorryAx]\n"
        "a.lean:4:0: information: 'Showcase.Putnam.bad' depends on axioms: "
        "[propext, Nat.someExtraAxiom]\n"
    )
    fps = parse_footprints(out)
    check(fps.get("Showcase.Putnam.foo") == set(), "footprint none")
    check(fps.get("Showcase.Putnam.cube") == {"propext"}, "footprint propext")
    check(SORRY_AX in fps.get("Showcase.Putnam.bar", set()), "footprint sorryAx")
    check(all(a in KERNEL_AXIOMS for a in fps["Showcase.Putnam.cube"]),
          "cube in-policy")
    check(any(a not in KERNEL_AXIOMS for a in fps["Showcase.Putnam.bad"]),
          "bad out-of-policy detected")

    # End-to-end static logic on synthetic records.
    recs = [
        {"lean_rel": "L/real_ok.lean", "md_rel": "m1", "label": "REAL",
         "sorries": [], "theorems": ["a"]},
        {"lean_rel": "L/real_bad.lean", "md_rel": "m2", "label": "REAL",
         "sorries": [9], "theorems": ["b"]},
        {"lean_rel": "L/demo_ok.lean", "md_rel": "m3", "label": "DEMO",
         "sorries": [5], "theorems": ["c"]},
        {"lean_rel": "L/demo_bad.lean", "md_rel": "m4", "label": "DEMO",
         "sorries": [], "theorems": ["d"]},
    ]
    errs = check_static(recs)
    blamed = " ".join(errs)
    check("real_bad.lean" in blamed, "REAL-with-sorry flagged")
    check("demo_bad.lean" in blamed, "DEMO-without-sorry flagged")
    check("real_ok.lean" not in blamed and "demo_ok.lean" not in blamed,
          "honest files not flagged")
    check(len(errs) == 2, f"exactly two static failures -> {len(errs)}")

    print("SELF-TEST: PASS" if ok else "SELF-TEST: FAILED")
    return 0 if ok else 1


def read_label_from_text(text: str) -> str | None:
    """Self-test helper mirroring read_label() without touching the filesystem."""
    labels = {m.group(1).upper() for m in LABEL_RE.finditer(text)}
    if not labels:
        m = TITLE_LABEL_RE.search(text)
        if m:
            labels = {m.group(1).upper()}
    return labels.pop() if len(labels) == 1 else None


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------
def main() -> int:
    ap = argparse.ArgumentParser(
        description="Verify each Putnam showcase problem's REAL/DEMO label is honest.")
    ap.add_argument("--repo-path", default=".", help="lutar-lean checkout root.")
    ap.add_argument("--with-axioms", action="store_true",
                    help="Also verify REAL axiom footprints via `lake env lean` "
                         "(requires the Lean toolchain + a warm `lake build`).")
    ap.add_argument("--self-test", action="store_true",
                    help="Run offline parser/logic self-tests and exit.")
    args = ap.parse_args()
    if args.self_test:
        return self_test()
    return run_gate(args.repo_path, args.with_axioms)


if __name__ == "__main__":
    raise SystemExit(main())
