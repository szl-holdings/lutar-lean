#!/usr/bin/env python3
"""Generate VERIFIED_THEOREMS.md — the honest, machine-checked "solved theorems" list.

PDF §7 / Doctrine v11. This is the single human-readable, citable artifact that is
regenerated from the *real* build so the published "solved" list can never drift
from what the Lean kernel actually verifies.

A declaration is **REAL** (and therefore listed) iff ALL of the following hold:
  * it is a `theorem` / `lemma` on the governed surface (see GOVERNANCE_SURFACE),
    declared non-`private` (private decls are unimportable, hence unauditable);
  * the kernel checks it with **zero `sorry`** — i.e. `#print axioms <name>` does
    NOT contain `sorryAx`;
  * its `#print axioms` footprint stays within the allowed set:
    {propext, Classical.choice, Quot.sound}  ∪  the already-declared, cited repo
    axioms recorded in `.github/data/lean_numbers.json` (`axiom_names`).

The footprint is read from the **actual build** via an auto-generated audit file
(`#print axioms <fqn>` per candidate) run through `lake env lean`, which
re-elaborates fresh and is therefore robust to a restored `.lake` cache. The
declaration *names + type signatures* are taken from source (deterministic), so
the emitted Markdown is byte-stable across runs at a fixed SHA — which is what the
drift gate (`check_verified_theorems_drift.py`) relies on.

Honesty doctrine v11: locked-proven set stays exactly 8; Conjecture 1
(unconditional Λ uniqueness) is machine-checked FALSE under A1–A5
(`Lutar.Round13.maxAgg_ne_Lambda`) and therefore can NEVER appear here. When the
Theorem U kernel task lands under `Lutar/Uniqueness/`, its sorry-free theorems are
picked up automatically (the directory is already on the governed surface).

Usage:
  # Full run (CI): enumerate -> audit -> lake env lean -> filter -> write Markdown
  python3 gen_verified_theorems.py --repo-path . --out VERIFIED_THEOREMS.md

  # Emit only the audit .lean (no lean needed) for inspection
  python3 gen_verified_theorems.py --repo-path . --emit-audit-only /tmp/audit.lean

  # Validate the source/output parsers offline (no lean, no build)
  python3 gen_verified_theorems.py --self-test
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys

REPO = "szl-holdings/lutar-lean"

# ---------------------------------------------------------------------------
# Governance surface: source files / directories whose theorems are candidates.
# A trailing os.sep entry is a directory prefix (all .lean beneath it); otherwise
# an exact file. `Lutar/Uniqueness/` is the (currently absent) Theorem U kernel
# directory — listed so its sorry-free theorems are auto-included once it lands.
# ---------------------------------------------------------------------------
GOVERNANCE_SURFACE = (
    os.path.join("Lutar", "Uniqueness.lean"),
    os.path.join("Lutar", "Uniqueness") + os.sep,
    os.path.join("Lutar", "Round13", "Lambda_Uniqueness.lean"),
)

# Lean-core axioms that are always trusted.
KERNEL_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
SORRY_AX = "sorryAx"

DEFAULT_NUMBERS_JSON = os.path.join(".github", "data", "lean_numbers.json")

# Declaration header: optional attribute block + optional modifiers + kw + name.
# `private` may appear before and/or after `noncomputable`; we only emit
# theorem/lemma (not def/instance/...), and we drop private decls.
DECL_HEADER_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?P<priv1>private\s+)?(?:noncomputable\s+)?(?P<priv2>private\s+)?"
    r"(?P<kw>theorem|lemma)\s+(?P<name>[A-Za-z_][A-Za-z0-9_'!]*)"
)
NS_RE = re.compile(r"^namespace\s+(\S+)\s*$")
SEC_RE = re.compile(r"^section(?:\s+(\S+))?\s*$")
END_RE = re.compile(r"^end(?:\s+(\S+))?\s*$")

OPENERS = "([{\u27e8\u2983"   # ( [ { ⟨ ⦃
CLOSERS = ")]}\u27e9\u2984"   # ) ] } ⟩ ⦄

# #print axioms output (robust to lean's location-prefixed, line-wrapped messages).
AX_DEPENDS_RE = re.compile(r"'([^']+)' depends on axioms: \[(.*?)\]", re.DOTALL)
AX_NONE_RE = re.compile(r"'([^']+)' does not depend on any axioms")


# ---------------------------------------------------------------------------
# Source enumeration
# ---------------------------------------------------------------------------
def module_of(relpath: str) -> str:
    no_ext = relpath[:-5] if relpath.endswith(".lean") else relpath
    return no_ext.replace(os.sep, ".")


def iter_surface_files(root: str):
    """Yield (relpath, abspath) for existing governed-surface .lean files."""
    seen = set()
    for entry in GOVERNANCE_SURFACE:
        if entry.endswith(os.sep):
            base = os.path.join(root, entry)
            if not os.path.isdir(base):
                continue
            for dirpath, _dirs, files in os.walk(base):
                for fn in sorted(files):
                    if fn.endswith(".lean"):
                        full = os.path.join(dirpath, fn)
                        rel = os.path.relpath(full, root)
                        if rel not in seen:
                            seen.add(rel)
                            yield rel, full
        else:
            full = os.path.join(root, entry)
            if os.path.isfile(full):
                rel = os.path.relpath(full, root)
                if rel not in seen:
                    seen.add(rel)
                    yield rel, full


def _find_body_start(text: str) -> int:
    """Index of the depth-0 ':=' that starts the proof body, or -1."""
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        elif c == ":" and depth == 0 and i + 1 < n and text[i + 1] == "=":
            return i
        i += 1
    return -1


def parse_theorems(abspath: str, relpath: str) -> list[dict]:
    """Return ordered theorem metadata dicts for one governed-surface file."""
    module = module_of(relpath)
    with open(abspath, "r", encoding="utf-8", errors="replace") as fh:
        lines = fh.readlines()

    ns_stack: list[tuple[str, str | None]] = []
    out: list[dict] = []
    n = len(lines)
    i = 0
    while i < n:
        raw = lines[i]
        line = raw.rstrip("\n")
        col0 = bool(line) and not line[0].isspace()

        if col0:
            stripped = line.strip()
            m_ns = NS_RE.match(stripped)
            m_end = END_RE.match(stripped)
            m_sec = SEC_RE.match(stripped)
            if m_ns:
                ns_stack.append(("ns", m_ns.group(1)))
                i += 1
                continue
            if m_end:
                if ns_stack:
                    ns_stack.pop()
                i += 1
                continue
            if m_sec:
                ns_stack.append(("sec", m_sec.group(1)))
                i += 1
                continue

        m_decl = DECL_HEADER_RE.match(line)
        if m_decl is None:
            i += 1
            continue

        # Accumulate the declaration header up to the depth-0 ':=' (bounded).
        buf: list[str] = []
        j = i
        cap = min(n, i + 250)
        cut = -1
        while j < cap:
            buf.append(lines[j].rstrip("\n"))
            full = "\n".join(buf)
            cut = _find_body_start(full)
            if cut != -1:
                break
            j += 1

        i += 1  # always advance one line (keep namespace tracking honest)

        if cut == -1:
            continue  # no body found within window — skip defensively

        is_private = bool(m_decl.group("priv1") or m_decl.group("priv2"))
        if is_private:
            continue

        name = m_decl.group("name")
        header = full[:cut]
        body_sig = header[m_decl.end():]
        signature = re.sub(r"\s+", " ", body_sig).strip()
        ns = ".".join(nm for kind, nm in ns_stack if kind == "ns" and nm)
        fqn = f"{ns}.{name}" if ns else name
        out.append(
            {
                "name": name,
                "fqn": fqn,
                "signature": f"{name} {signature}".strip(),
                "module": module,
                "relpath": relpath,
                "line": (i),  # 1-based-ish source order key
            }
        )
    return out


def enumerate_governed(root: str) -> list[dict]:
    theorems: list[dict] = []
    for rel, full in iter_surface_files(root):
        theorems.extend(parse_theorems(full, rel))
    return theorems


# ---------------------------------------------------------------------------
# Audit file + footprint parsing
# ---------------------------------------------------------------------------
def build_audit(theorems: list[dict]) -> str:
    modules: list[str] = []
    seen = set()
    for t in theorems:
        if t["module"] not in seen:
            seen.add(t["module"])
            modules.append(t["module"])
    lines = [
        "-- AUTO-GENERATED by .github/scripts/gen_verified_theorems.py — do NOT commit.",
        "-- Footprint audit: one `#print axioms` per governed-surface candidate.",
    ]
    for mod in modules:
        lines.append(f"import {mod}")
    lines.append("")
    for t in theorems:
        lines.append(f"#print axioms {t['fqn']}")
    return "\n".join(lines) + "\n"


def parse_footprints(output: str) -> dict[str, set[str]]:
    """fqn -> set of axiom names from `#print axioms` output."""
    fps: dict[str, set[str]] = {}
    for m in AX_NONE_RE.finditer(output):
        fps[m.group(1)] = set()
    for m in AX_DEPENDS_RE.finditer(output):
        items = [s.strip() for s in m.group(2).split(",")]
        fps[m.group(1)] = {s for s in items if s}
    return fps


def load_repo_axioms(numbers_json: str) -> set[str]:
    try:
        with open(numbers_json, "r", encoding="utf-8") as fh:
            return set(json.load(fh)["numbers"].get("axiom_names", []))
    except FileNotFoundError:
        return set()


def is_allowed_axiom(ax: str, repo_axioms: set[str]) -> bool:
    if ax in KERNEL_AXIOMS:
        return True
    # Declared, cited repo axiom: an in-repo (Lutar.*) constant whose short name
    # is recorded in lean_numbers.json's axiom_names (which are short tokens).
    short = ax.rsplit(".", 1)[-1]
    if ax.startswith("Lutar.") and short in repo_axioms:
        return True
    if ax in repo_axioms:
        return True
    return False


def classify(theorems, footprints, repo_axioms):
    """Return (real, excluded, missing)."""
    real, excluded, missing = [], [], []
    for t in theorems:
        fp = footprints.get(t["fqn"])
        if fp is None:
            missing.append(t)
            continue
        if SORRY_AX in fp:
            excluded.append((t, "sorry"))
            continue
        bad = sorted(a for a in fp if not is_allowed_axiom(a, repo_axioms))
        if bad:
            excluded.append((t, "axioms:" + ",".join(bad)))
            continue
        real.append(t)
    return real, excluded, missing


# ---------------------------------------------------------------------------
# Rendering
# ---------------------------------------------------------------------------
HEADER = """# Verified Theorems

> **AUTO-GENERATED — do not edit by hand.** Produced by
> `.github/scripts/gen_verified_theorems.py` from the real `lake build`, and gated
> in CI by `check_verified_theorems_drift.py` (any hand edit or drift fails the
> build). Each entry below is a `theorem`/`lemma` on the governed uniqueness /
> identifiability surface that the Lean kernel checks with **zero `sorry`** and
> whose `#print axioms` footprint stays within
> `{propext, Classical.choice, Quot.sound}` plus the already-declared, cited repo
> axioms in `.github/data/lean_numbers.json`.
>
> **Honesty doctrine v11.** The locked-proven set stays exactly 8. Conjecture 1
> (unconditional Λ uniqueness, `∀ Φ, LutarAxioms Φ → Φ = Λ k`) is machine-checked
> **FALSE** under A1–A5 — `Lutar.Round13.maxAgg_ne_Lambda` exhibits the max
> aggregator as an A1–A5 counterexample — so it can never appear here. Only the
> *conditional* uniqueness (`lambda_unique_of_factors`) is REAL.
"""


def render_md(real: list[dict]) -> str:
    parts = [HEADER, ""]
    by_file: dict[str, list[dict]] = {}
    for t in real:
        by_file.setdefault(t["relpath"], []).append(t)
    if not real:
        parts.append("_No REAL theorems on the governed surface at this revision._")
        parts.append("")
        return "\n".join(parts)
    for rel in sorted(by_file):
        parts.append(f"## `{rel}`")
        parts.append("")
        for t in sorted(by_file[rel], key=lambda d: d["line"]):
            parts.append(f"- `{t['signature']}`")
        parts.append("")
    return "\n".join(parts)


# ---------------------------------------------------------------------------
# Lean invocation
# ---------------------------------------------------------------------------
def run_audit(root: str, audit_text: str, keep: bool) -> str:
    audit_path = os.path.join(root, ".verified_theorems_audit.lean")
    with open(audit_path, "w", encoding="utf-8") as fh:
        fh.write(audit_text)
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", ".verified_theorems_audit.lean"],
            cwd=root,
            capture_output=True,
            text=True,
        )
    finally:
        if not keep:
            try:
                os.remove(audit_path)
            except OSError:
                pass
    out = (proc.stdout or "") + "\n" + (proc.stderr or "")
    if proc.returncode != 0:
        sys.stderr.write(
            "::warning::`lake env lean` exited %d during footprint audit.\n"
            "----- audit output (head) -----\n%s\n"
            % (proc.returncode, out[:4000])
        )
    return out


# ---------------------------------------------------------------------------
# Self-test (offline; no lean / no build)
# ---------------------------------------------------------------------------
def self_test() -> int:
    ok = True

    def check(cond, msg):
        nonlocal ok
        if not cond:
            ok = False
            print(f"SELF-TEST FAIL: {msg}")

    # depth-0 ':=' scanner ignores ':' inside binders.
    txt = "foo {k : Nat} (hk : 0 < k) :\n    IsMonotone (Λ k) := by\n  intro x"
    cut = _find_body_start(txt)
    check(cut != -1 and txt[cut:cut + 2] == ":=", "body-start scanner")
    check(":=" not in txt[:cut], "body-start before any ':='")

    # footprint parsers, incl. wrapped multi-line + 'no axioms'.
    sample = (
        "audit.lean:5:0: information: 'Lutar.Round13.maxAgg_ne_Lambda' depends on "
        "axioms: [propext,\n Classical.choice, Quot.sound]\n"
        "audit.lean:6:0: information: 'Lutar.Round13.lambda_unique' depends on "
        "axioms: [propext, sorryAx]\n"
        "audit.lean:7:0: information: 'Lutar.foo' does not depend on any axioms\n"
    )
    fps = parse_footprints(sample)
    check(
        fps.get("Lutar.Round13.maxAgg_ne_Lambda")
        == {"propext", "Classical.choice", "Quot.sound"},
        f"parse wrapped axiom list -> {fps.get('Lutar.Round13.maxAgg_ne_Lambda')}",
    )
    check(SORRY_AX in fps.get("Lutar.Round13.lambda_unique", set()), "parse sorryAx")
    check(fps.get("Lutar.foo") == set(), "parse 'no axioms'")

    # classify with a declared repo axiom (short token, FQN footprint).
    repo_ax = {"pinsker"}
    th = [
        {"fqn": "A", "name": "A", "signature": "A : True", "relpath": "x", "line": 1},
        {"fqn": "B", "name": "B", "signature": "B : True", "relpath": "x", "line": 2},
        {"fqn": "C", "name": "C", "signature": "C : True", "relpath": "x", "line": 3},
        {"fqn": "D", "name": "D", "signature": "D : True", "relpath": "x", "line": 4},
    ]
    foot = {
        "A": {"propext", "Quot.sound"},
        "B": {"propext", "sorryAx"},
        "C": {"Lutar.Puriq.DPOFeasibility.pinsker", "propext"},
        "D": {"SomeOther.badAxiom"},
    }
    real, excluded, missing = classify(th, foot, repo_ax)
    names = {t["fqn"] for t in real}
    check(names == {"A", "C"}, f"classify real set -> {names}")
    check(any(fqn == "B" for (t, _r) in excluded for fqn in [t["fqn"]]), "B excluded (sorry)")
    check(any(fqn == "D" for (t, _r) in excluded for fqn in [t["fqn"]]), "D excluded (axiom)")
    check(missing == [], "no missing in classify test")

    # module path derivation.
    check(
        module_of(os.path.join("Lutar", "Round13", "Lambda_Uniqueness.lean"))
        == "Lutar.Round13.Lambda_Uniqueness",
        "module_of",
    )

    print("SELF-TEST: PASS" if ok else "SELF-TEST: FAILED")
    return 0 if ok else 1


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------
def main() -> int:
    ap = argparse.ArgumentParser(description="Generate VERIFIED_THEOREMS.md from the build.")
    ap.add_argument("--repo-path", default=".", help="lutar-lean checkout root.")
    ap.add_argument("--out", help="Write Markdown here (default: stdout).")
    ap.add_argument("--numbers-json", default=DEFAULT_NUMBERS_JSON,
                    help="Path to lean_numbers.json (declared repo axiom allowlist).")
    ap.add_argument("--emit-audit-only", metavar="PATH",
                    help="Only write the audit .lean (no lean run) and exit.")
    ap.add_argument("--keep-audit", action="store_true",
                    help="Keep the temp audit .lean after running.")
    ap.add_argument("--self-test", action="store_true",
                    help="Run offline parser self-tests and exit.")
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    root = args.repo_path
    if not os.path.isdir(os.path.join(root, "Lutar")):
        print(f"error: {root} has no Lutar/ directory", file=sys.stderr)
        return 2

    theorems = enumerate_governed(root)
    if not theorems:
        print("error: no governed-surface theorems found", file=sys.stderr)
        return 2

    audit_text = build_audit(theorems)

    if args.emit_audit_only:
        os.makedirs(os.path.dirname(args.emit_audit_only) or ".", exist_ok=True)
        with open(args.emit_audit_only, "w", encoding="utf-8") as fh:
            fh.write(audit_text)
        print(f"wrote audit {args.emit_audit_only} ({len(theorems)} candidates)")
        return 0

    output = run_audit(root, audit_text, args.keep_audit)
    footprints = parse_footprints(output)
    repo_axioms = load_repo_axioms(os.path.join(root, args.numbers_json))
    real, excluded, missing = classify(theorems, footprints, repo_axioms)

    if missing:
        names = ", ".join(t["fqn"] for t in missing)
        sys.stderr.write(
            "::error::%d governed candidate(s) produced no `#print axioms` "
            "footprint (unknown constant / elaboration error): %s\n" % (len(missing), names)
        )
        return 3

    md = render_md(real)
    if args.out:
        with open(args.out, "w", encoding="utf-8") as fh:
            fh.write(md)
        print(f"wrote {args.out}: {len(real)} REAL, {len(excluded)} excluded "
              f"of {len(theorems)} candidates")
        for t, reason in excluded:
            print(f"  excluded {t['fqn']} ({reason})")
    else:
        sys.stdout.write(md)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
