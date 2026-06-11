#!/usr/bin/env python3
"""Build a deterministic, verifiable proof-milestone snapshot for szl-lake anchoring.

Runs in lutar-lean CI (e.g. lake-build.yml) AFTER `lake build`, `lake exe ref_vectors`,
the axiom-hygiene gate, and the canonical-numbers recompute have all succeeded.
It assembles a single self-contained JSON describing the *kernel-verified* state of
a named milestone:

  * the kernel commit (full + short) and branch,
  * the per-declaration #print-axioms footprint of the milestone's headline pack
    (parsed from the axiom-hygiene gate's captured output), with a kernel-only
    assertion over the WHOLE parsed footprint,
  * the regenerated canonical Lean numbers (decl/axiom/sorry counts) + a replay
    hash over the measured numbers and the reference vectors,
  * an explicit, per-snapshot honesty block (never a blanket "proven"): each
    milestone carries its own truthful status (proven / conditional / open).

Originally Theorem-U-specific; now generalized so ANY green proof milestone (a
future Conjecture-2 result, an updated doctrine snapshot, etc.) can be anchored
through the same pipeline by passing `--kind` plus a milestone profile. The
DEFAULT profile (`--kind theorem-u`) reproduces the original Theorem-U snapshot
content.

No network, no signing here -- this only emits the *subject* that the anchor
workflow signs (cosign keyless OIDC) and records in szl-lake. Deterministic given
the same inputs except for `built_at_utc`; receipt idempotency keys off
(kind, kernel_commit, snapshot_sha), not the whole-file hash.
"""
from __future__ import annotations

import argparse
import datetime as _dt
import hashlib
import json
import os
import re
import sys

SNAPSHOT_SCHEMA = "szl.proof.snapshot/v1"

KERNEL_TRUST_BASE = {"propext", "funext", "Classical.choice", "Quot.sound"}

# --------------------------------------------------------------------------- #
# Built-in milestone profiles.
#
# A profile defines what makes a given milestone snapshot "green": the headline
# declarations whose axiom footprint must be present + kernel-clean, the human
# title + module, the milestone status label, and the per-snapshot honesty block.
# The honesty block is carried VERBATIM into the snapshot and the receipt; it must
# state the truth for THAT milestone (proven vs conditional vs open), never a
# blanket "proven".
#
# Default profile = theorem-u (reproduces the original behaviour).
# --------------------------------------------------------------------------- #
PROFILES: dict[str, dict] = {
    "theorem-u": {
        "title": "Theorem U -- Lambda uniqueness (conditional)",
        "module": "Lutar.Uniqueness",
        "pack_dir": "Lutar/Uniqueness",
        "status": "REAL-conditional",
        # Matched by FQN suffix so namespacing (Lutar.Uniqueness.<name>) is tolerated.
        "headline_suffixes": [
            "TheoremU_LambdaUnique",
            "TheoremU_LambdaUnique_eq",
            "CorollaryU1_LambdaUnique_Separable",
            "CorollaryU2_LambdaUnique_Factors",
            "identifiability_forces_lambda",
            "lambda_equiv_to_eq_of_anchored",
        ],
        "require_headline": True,
        "honesty": {
            "doctrine": "v11",
            "theorem_u": (
                "REAL-conditional: Lutar.Uniqueness Theorem U is kernel-verified "
                "(axiom footprint within the Lean/Mathlib trust base, no sorry) but "
                "CONDITIONAL on its stated checkable hypotheses; it is NOT part of "
                "the locked-proven baseline."
            ),
            "conjecture_1": (
                "OPEN: unconditional Lambda uniqueness is Conjecture 1 and is "
                "machine-checked FALSE as stated. Theorem U does NOT close it."
            ),
            "locked_five_unchanged": True,
            "locked_set": ["F1", "F11", "F12", "F18", "F19"],
        },
    },
    # Second anchored milestone (Task #723): the kernel-verified meta-invariants
    # that pin the LOCKED-proven baseline itself. These are `decide`-proven
    # meta-theorems in Lutar/Uniqueness/AxiomCheck.lean (already emitted into the
    # same axiom-hygiene capture the theorem-u snapshot reads), so anchoring this
    # milestone needs NO new Lean files. It proves the generalized snapshot+anchor
    # path works end-to-end for a NON-Theorem-U kind on the live Khipu chain.
    # Honesty: this milestone asserts what the locked baseline IS (exactly the
    # eight {F1,F4,F7,F11,F12,F18,F19,F22}); it does NOT prove those formulas and
    # leaves Theorem U conditional / Conjecture 1 open.
    "locked-baseline": {
        "title": "Locked-proven baseline (Doctrine v11) — kernel meta-invariants",
        "module": "Lutar.Uniqueness.AxiomCheck",
        "pack_dir": "Lutar/Uniqueness",
        "status": "REAL-invariant",
        # Matched by FQN suffix (Lutar.Uniqueness.AxiomCheck.<name>).
        "headline_suffixes": [
            "locked_count_eight",
            "theoremU_excluded_from_locked",
            "theoremU_axiom_sets_kernel_only",
            "conjecture1_still_open",
        ],
        "require_headline": True,
        "honesty": {
            "doctrine": "v11",
            "locked_baseline": (
                "REAL-invariant: kernel-verified meta-theorems in "
                "Lutar/Uniqueness/AxiomCheck.lean (locked_count_eight, "
                "theoremU_excluded_from_locked, theoremU_axiom_sets_kernel_only, "
                "conjecture1_still_open) — each proven by `decide`, axiom footprint "
                "within the Lean/Mathlib trust base, no sorry. They ASSERT that the "
                "locked-proven baseline is EXACTLY the eight "
                "{F1,F4,F7,F11,F12,F18,F19,F22}; they do NOT themselves re-prove "
                "those formulas (the formula proofs live in "
                "Lutar/Puriq/Formulas/ProvedFormulas.lean)."
            ),
            "locked_set": ["F1", "F4", "F7", "F11", "F12", "F18", "F19", "F22"],
            "theorem_u": (
                "Theorem U stays REAL-conditional and EXCLUDED from this locked "
                "baseline (theoremU_excluded_from_locked); anchoring this milestone "
                "does not change Theorem U's status."
            ),
            "conjecture_1": (
                "OPEN: unconditional Lambda uniqueness is Conjecture 1 and is "
                "machine-checked FALSE as stated; conjecture1_still_open re-asserts "
                "it stays open."
            ),
        },
    },
}

_DEPENDS_RE = re.compile(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", re.DOTALL)
_NODEPS_RE = re.compile(r"'([^']+)' does not depend on any axioms")

# VERIFIED_THEOREMS(.generated).md is emitted by gen_verified_theorems.py as a
# `## \`<relpath>\`` header per source file followed by `- \`<signature>\`` items,
# one per REAL (kernel-checked, zero-sorry, in-policy axiom footprint) theorem on
# the governed surface, and is CI-drift-gated against the real build. We parse it
# back into a deterministic per-theorem list so EVERY CI-green theorem rides the
# same cosign-signed snapshot/receipt the anchor workflow records into szl-lake.
_VT_FILE_RE = re.compile(r"^##\s+`([^`]+)`\s*$")
_VT_ITEM_RE = re.compile(r"^-\s+`(.+)`\s*$")
_VT_NAME_RE = re.compile(r"^([^\s(){}:]+)")

VERIFIED_THEOREMS_SCHEMA = "szl.lake.verified-theorems/v1"


def parse_verified_theorems(md_text: str) -> list[dict]:
    """Parse VERIFIED_THEOREMS(.generated).md into a deterministic theorem list.

    Returns records {file, name, signature} sorted by (file, name) so the embedded
    block is byte-stable at a fixed revision regardless of within-file ordering.
    Each record is a kernel-checked REAL theorem (the source file is regenerated
    from the real `lake build` and CI-drift-gated); we never invent entries.
    """
    out: list[dict] = []
    current_file = None
    for raw in md_text.splitlines():
        line = raw.rstrip()
        mf = _VT_FILE_RE.match(line)
        if mf:
            current_file = mf.group(1).strip()
            continue
        mi = _VT_ITEM_RE.match(line)
        if mi and current_file:
            sig = mi.group(1).strip()
            mn = _VT_NAME_RE.match(sig)
            if not mn:
                continue
            out.append({"file": current_file, "name": mn.group(1), "signature": sig})
    out.sort(key=lambda r: (r["file"], r["name"]))
    return out


def build_verified_theorems_block(path: str, doctrine: str) -> dict | None:
    """Build the embeddable verified_theorems block from the generated md file."""
    if not path:
        return None
    if not os.path.exists(path):
        print(f"::warning::--verified-theorems {path} not found; snapshot will omit "
              "the verified_theorems block", file=sys.stderr)
        return None
    with open(path, "r", encoding="utf-8") as fh:
        text = fh.read()
    theorems = parse_verified_theorems(text)
    return {
        "schema": VERIFIED_THEOREMS_SCHEMA,
        "source": os.path.basename(path),
        "source_sha256": _sha256_bytes(text.encode()),
        "doctrine": doctrine or "v11",
        "count": len(theorems),
        "theorems": theorems,
    }


def _self_test() -> int:
    """Offline parser self-test (no lean, no build, no network)."""
    fixture = (
        "# Verified Theorems\n\n"
        "> **Honesty doctrine v11.** Conjecture 1 is machine-checked FALSE.\n\n"
        "## `Lutar/Uniqueness/TheoremU.lean`\n\n"
        "- `TheoremU_LambdaUnique {k : \u2115} (\u03a6 \u03a8 : Aggregator k) : LambdaEquiv \u03a6 \u03a8`\n"
        "- `identifiability_forces_lambda {k : \u2115} (\u03a6 : Aggregator k) : \u03a6 = \u039b k`\n\n"
        "## `Lutar/Uniqueness/AxiomCheck.lean`\n\n"
        "- `locked_count_eight : lockedNames.length = 8`\n"
        "- `conjecture1_still_open : openConjectures.length = 1`\n"
    )
    ok = True

    def chk(cond, msg):
        nonlocal ok
        if not cond:
            ok = False
            print(f"SELF-TEST FAIL: {msg}")

    rows = parse_verified_theorems(fixture)
    chk(len(rows) == 4, f"expected 4 theorems, got {len(rows)}")
    names = [r["name"] for r in rows]
    chk(names == ["conjecture1_still_open", "locked_count_eight",
                  "TheoremU_LambdaUnique", "identifiability_forces_lambda"],
        f"unexpected order/names: {names}")
    chk(all(r["file"] and r["name"] and r["signature"] for r in rows),
        "every record must have file/name/signature")
    chk(all("`" not in r["signature"] for r in rows), "signatures must be backtick-free")
    chk(parse_verified_theorems(fixture) == rows, "parser must be deterministic")
    # Empty / headerless input yields an empty list (never crashes, never invents).
    chk(parse_verified_theorems("# Verified Theorems\n\n_No REAL theorems._\n") == [],
        "empty surface must parse to []")
    print("SELF-TEST: PASS" if ok else "SELF-TEST: FAILED")
    return 0 if ok else 1


def _sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def _sha256_file(path: str) -> str:
    with open(path, "rb") as fh:
        return _sha256_bytes(fh.read())


def parse_axiom_footprint(text: str) -> dict[str, list[str]]:
    """Parse `#print axioms` output into {decl_fqn: sorted([axiom, ...])}."""
    out: dict[str, list[str]] = {}
    for m in _DEPENDS_RE.finditer(text):
        name = m.group(1).strip()
        raw = m.group(2)
        axioms = sorted({a.strip() for a in raw.split(",") if a.strip()})
        out[name] = axioms
    for m in _NODEPS_RE.finditer(text):
        out.setdefault(m.group(1).strip(), [])
    return out


def find_headline(footprint: dict[str, list[str]],
                  suffixes: list[str]) -> dict[str, list[str]]:
    """Select the headline decls (by FQN suffix) from the full footprint."""
    found: dict[str, list[str]] = {}
    for suffix in suffixes:
        for fqn, axs in footprint.items():
            if fqn == suffix or fqn.endswith("." + suffix):
                found[suffix] = axs
                break
    return found


def collect_decl_sources(root: str) -> dict[str, str]:
    """sha256 of every .lean file under the milestone's pack dir (sorted)."""
    sources: dict[str, str] = {}
    for dirpath, _dirs, files in os.walk(root):
        for fn in sorted(files):
            if fn.endswith(".lean"):
                full = os.path.join(dirpath, fn)
                rel = os.path.relpath(full, ".")
                sources[rel] = _sha256_file(full)
    return dict(sorted(sources.items()))


def _load_profile(args) -> dict:
    """Resolve the milestone profile: built-in default merged with overrides."""
    base = dict(PROFILES.get(args.kind, {}))
    if args.profile:
        with open(args.profile, "r", encoding="utf-8") as fh:
            base.update(json.load(fh))
    if not base and not args.profile:
        # Unknown kind with no profile file: build a minimal profile from flags so
        # callers can anchor a new milestone without registering it here first.
        base = {}

    # Per-flag overrides take precedence over the profile file / built-in.
    if args.title is not None:
        base["title"] = args.title
    if args.status is not None:
        base["status"] = args.status
    if args.module is not None:
        base["module"] = args.module
    if args.pack_dir is not None:
        base["pack_dir"] = args.pack_dir
    if args.headline_suffixes is not None:
        base["headline_suffixes"] = [
            s.strip() for s in args.headline_suffixes.split(",") if s.strip()
        ]
    if args.honesty_file:
        with open(args.honesty_file, "r", encoding="utf-8") as fh:
            base["honesty"] = json.load(fh)
    if args.require_headline is not None:
        base["require_headline"] = args.require_headline

    base.setdefault("title", args.kind)
    base.setdefault("status", "REAL-conditional")
    base.setdefault("headline_suffixes", [])
    base.setdefault("require_headline", bool(base["headline_suffixes"]))
    base.setdefault("pack_dir", base.get("module", "").replace(".", "/"))
    base.setdefault("module", base.get("pack_dir", "").replace("/", "."))
    return base


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--kind", default="theorem-u",
                    help="milestone kind id (default: theorem-u)")
    ap.add_argument("--profile", default=None,
                    help="optional JSON file overriding/defining the milestone profile")
    ap.add_argument("--title", default=None, help="human-readable milestone title")
    ap.add_argument("--status", default=None,
                    help="milestone status label (e.g. REAL-conditional, PROVEN, OPEN)")
    ap.add_argument("--module", default=None, help="milestone module (dotted)")
    ap.add_argument("--honesty-file", default=None,
                    help="JSON file with the per-snapshot honesty block")
    ap.add_argument("--headline-suffixes", default=None,
                    help="comma-separated FQN suffixes of headline decls")
    ap.add_argument("--require-headline", dest="require_headline",
                    action="store_true", default=None,
                    help="fail if any headline decl is missing (default if suffixes set)")
    ap.add_argument("--no-require-headline", dest="require_headline",
                    action="store_false",
                    help="allow an empty/partial headline set")
    ap.add_argument("--axiomcheck-out", default=None,
                    help="captured stdout of the axiom-hygiene gate (#print axioms)")
    ap.add_argument("--numbers", default=None,
                    help="regenerated canonical numbers (lean_numbers.measured.json)")
    ap.add_argument("--reference-vectors", default=None,
                    help="reference-vectors.json produced by `lake exe ref_vectors`")
    ap.add_argument("--pack-dir", default=None,
                    help="milestone pack source directory (overrides the profile)")
    ap.add_argument("--verified-theorems", default=None,
                    help="VERIFIED_THEOREMS(.generated).md to embed as the per-theorem "
                         "anchor record set (every CI-green governed-surface theorem)")
    ap.add_argument("--repo", default=os.environ.get("GITHUB_REPOSITORY", "szl-holdings/lutar-lean"))
    ap.add_argument("--commit", default=os.environ.get("GITHUB_SHA", ""))
    ap.add_argument("--branch", default=os.environ.get("GITHUB_REF_NAME", ""))
    ap.add_argument("--out", default="theorem_u_snapshot.json")
    ap.add_argument("--self-test", action="store_true",
                    help="run offline parser self-tests (no lean/build/network) and exit")
    args = ap.parse_args()

    if args.self_test:
        return _self_test()
    missing = [f"--{n.replace('_', '-')}" for n in
               ("axiomcheck_out", "numbers", "reference_vectors")
               if not getattr(args, n)]
    if missing:
        ap.error("the following arguments are required: " + ", ".join(missing))

    profile = _load_profile(args)
    headline_suffixes = profile["headline_suffixes"]
    pack_dir = profile["pack_dir"]
    if not pack_dir:
        print("::error::milestone profile has no pack_dir/module", file=sys.stderr)
        return 1
    honesty = profile.get("honesty")
    if honesty is None:
        print(f"::error::milestone '{args.kind}' has no honesty block; refusing to "
              "anchor without a per-snapshot honesty statement", file=sys.stderr)
        return 1

    with open(args.axiomcheck_out, "r", encoding="utf-8", errors="replace") as fh:
        axiom_text = fh.read()
    footprint = parse_axiom_footprint(axiom_text)
    if not footprint:
        print("::error::no #print axioms results parsed from axiom-hygiene output", file=sys.stderr)
        return 1

    headline = find_headline(footprint, headline_suffixes)
    if profile["require_headline"]:
        missing = [s for s in headline_suffixes if s not in headline]
        if missing:
            print(f"::error::{args.kind} headline decls missing from axiom footprint: {missing}",
                  file=sys.stderr)
            return 1

    # Kernel-only assertion over the WHOLE parsed footprint (the gate already
    # fails on sorryAx; this re-asserts the trust base for the record). This is
    # what makes the snapshot a GREEN, kernel-verified milestone regardless of
    # whether the honesty label is "proven" or "conditional".
    offenders: dict[str, list[str]] = {}
    for fqn, axs in footprint.items():
        bad = [a for a in axs if a not in KERNEL_TRUST_BASE]
        if bad:
            offenders[fqn] = bad
    kernel_only = not offenders
    if not kernel_only:
        print(f"::error::axiom footprint escapes the kernel trust base: {offenders}",
              file=sys.stderr)
        return 1

    with open(args.numbers, "r", encoding="utf-8") as fh:
        numbers_doc = json.load(fh)
    numbers = numbers_doc.get("numbers", {})

    numbers_sha = _sha256_file(args.numbers)
    refvec_sha = _sha256_file(args.reference_vectors)
    decl_sources = collect_decl_sources(pack_dir)

    milestone = {
        "id": args.kind,
        "title": profile["title"],
        "module": profile["module"] or pack_dir.replace("/", "."),
        "status": profile["status"],
        "headline_decls": sorted(headline.keys()),
        "headline_axiom_footprint": dict(sorted(headline.items())),
        "full_axiom_footprint": dict(sorted(footprint.items())),
        "kernel_trust_base": sorted(KERNEL_TRUST_BASE),
        "kernel_only": kernel_only,
        "decl_source_sha256": decl_sources,
    }

    snapshot = {
        "schema": SNAPSHOT_SCHEMA,
        "kind": args.kind,
        "repo": args.repo,
        "kernel_commit": args.commit,
        "kernel_commit_short": args.commit[:12] if args.commit else "",
        "branch": args.branch,
        "built_at_utc": _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "milestone": milestone,
        "lean_numbers": {
            "schema": numbers_doc.get("schema"),
            "numbers": numbers,
            "lean_numbers_sha256": numbers_sha,
            "reference_vectors_sha256": refvec_sha,
            "replay_hash": _sha256_bytes(
                (numbers_sha + ":" + refvec_sha).encode()
            ),
        },
        "honesty": honesty,
    }

    # Embed EVERY CI-green governed-surface theorem (kernel-checked, drift-gated)
    # so the cosign-signed snapshot/receipt anchored into szl-lake records them all.
    vt_block = build_verified_theorems_block(
        args.verified_theorems,
        honesty.get("doctrine", "v11") if isinstance(honesty, dict) else "v11",
    )
    if vt_block is not None:
        snapshot["verified_theorems"] = vt_block

    with open(args.out, "w", encoding="utf-8") as fh:
        json.dump(snapshot, fh, indent=2, sort_keys=True, ensure_ascii=False)
        fh.write("\n")

    snap_sha = _sha256_file(args.out)
    print(f"{args.out} written; schema={SNAPSHOT_SCHEMA} kind={args.kind} sha256={snap_sha}")
    print(f"  kernel_commit = {snapshot['kernel_commit']}")
    print(f"  status = {milestone['status']}")
    print(f"  headline decls = {milestone['headline_decls']}")
    print(f"  kernel_only = {kernel_only}")
    print(f"  numbers = decl {numbers.get('declarations')} / "
          f"axioms_unique {numbers.get('axioms_unique')} / "
          f"sorries_noncomment {numbers.get('sorries_noncomment')}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
