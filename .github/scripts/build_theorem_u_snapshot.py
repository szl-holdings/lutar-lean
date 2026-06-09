#!/usr/bin/env python3
"""Build a deterministic, verifiable Theorem-U snapshot for szl-lake anchoring.

Runs in lutar-lean CI (lake-build.yml) AFTER `lake build`, `lake exe ref_vectors`,
the axiom-hygiene gate, and the canonical-numbers recompute have all succeeded.
It assembles a single self-contained JSON describing the *kernel-verified* state:

  * the kernel commit (full + short) and branch,
  * the per-declaration #print-axioms footprint of the Theorem-U pack (parsed from
    the axiom-hygiene gate's captured output), with a kernel-only assertion,
  * the regenerated canonical Lean numbers (decl/axiom/sorry counts) + a replay
    hash over the measured numbers and the reference vectors,
  * an explicit honesty block (doctrine v11): Theorem U is REAL-conditional;
    Conjecture 1 (unconditional Lambda uniqueness) is OPEN / machine-checked FALSE.

No network, no signing here -- this only emits the *subject* that the anchor
workflow signs (cosign keyless OIDC) and records in szl-lake. Deterministic given
the same inputs except for `built_at_utc`; receipt idempotency keys off
`kernel_commit`, not the whole-file hash.
"""
from __future__ import annotations

import argparse
import datetime as _dt
import hashlib
import json
import os
import re
import sys

KERNEL_TRUST_BASE = {"propext", "funext", "Classical.choice", "Quot.sound"}

# Theorem-U headline results we explicitly assert are present + kernel-clean.
# Matched by FQN suffix so namespacing (Lutar.Uniqueness.<name>) is tolerated.
HEADLINE_SUFFIXES = [
    "TheoremU_LambdaUnique",
    "TheoremU_LambdaUnique_eq",
    "CorollaryU1_LambdaUnique_Separable",
    "CorollaryU2_LambdaUnique_Factors",
    "identifiability_forces_lambda",
    "lambda_equiv_to_eq_of_anchored",
]

_DEPENDS_RE = re.compile(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", re.DOTALL)
_NODEPS_RE = re.compile(r"'([^']+)' does not depend on any axioms")


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


def find_headline(footprint: dict[str, list[str]]) -> dict[str, list[str]]:
    """Select the headline decls (by FQN suffix) from the full footprint."""
    found: dict[str, list[str]] = {}
    for suffix in HEADLINE_SUFFIXES:
        for fqn, axs in footprint.items():
            if fqn == suffix or fqn.endswith("." + suffix):
                found[suffix] = axs
                break
    return found


def collect_decl_sources(root: str) -> dict[str, str]:
    """sha256 of every .lean file under the Theorem-U pack dir (sorted)."""
    sources: dict[str, str] = {}
    for dirpath, _dirs, files in os.walk(root):
        for fn in sorted(files):
            if fn.endswith(".lean"):
                full = os.path.join(dirpath, fn)
                rel = os.path.relpath(full, ".")
                sources[rel] = _sha256_file(full)
    return dict(sorted(sources.items()))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--axiomcheck-out", required=True,
                    help="captured stdout of the axiom-hygiene gate (#print axioms)")
    ap.add_argument("--numbers", required=True,
                    help="regenerated canonical numbers (lean_numbers.measured.json)")
    ap.add_argument("--reference-vectors", required=True,
                    help="reference-vectors.json produced by `lake exe ref_vectors`")
    ap.add_argument("--pack-dir", default="Lutar/Uniqueness",
                    help="Theorem-U pack source directory")
    ap.add_argument("--repo", default=os.environ.get("GITHUB_REPOSITORY", "szl-holdings/lutar-lean"))
    ap.add_argument("--commit", default=os.environ.get("GITHUB_SHA", ""))
    ap.add_argument("--branch", default=os.environ.get("GITHUB_REF_NAME", ""))
    ap.add_argument("--out", default="theorem_u_snapshot.json")
    args = ap.parse_args()

    with open(args.axiomcheck_out, "r", encoding="utf-8", errors="replace") as fh:
        axiom_text = fh.read()
    footprint = parse_axiom_footprint(axiom_text)
    if not footprint:
        print("::error::no #print axioms results parsed from axiom-hygiene output", file=sys.stderr)
        return 1

    headline = find_headline(footprint)
    missing = [s for s in HEADLINE_SUFFIXES if s not in headline]
    if missing:
        print(f"::error::Theorem-U headline decls missing from axiom footprint: {missing}",
              file=sys.stderr)
        return 1

    # Kernel-only assertion over the WHOLE parsed footprint (the gate already
    # fails on sorryAx; this re-asserts the trust base for the record).
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
    decl_sources = collect_decl_sources(args.pack_dir)

    snapshot = {
        "schema": "szl.theorem_u.snapshot/v1",
        "repo": args.repo,
        "kernel_commit": args.commit,
        "kernel_commit_short": args.commit[:12] if args.commit else "",
        "branch": args.branch,
        "built_at_utc": _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "theorem_u": {
            "module": args.pack_dir.replace("/", "."),
            "status": "REAL-conditional",
            "headline_decls": sorted(headline.keys()),
            "headline_axiom_footprint": dict(sorted(headline.items())),
            "full_axiom_footprint": dict(sorted(footprint.items())),
            "kernel_trust_base": sorted(KERNEL_TRUST_BASE),
            "kernel_only": kernel_only,
            "decl_source_sha256": decl_sources,
        },
        "lean_numbers": {
            "schema": numbers_doc.get("schema"),
            "numbers": numbers,
            "lean_numbers_sha256": numbers_sha,
            "reference_vectors_sha256": refvec_sha,
            "replay_hash": _sha256_bytes(
                (numbers_sha + ":" + refvec_sha).encode()
            ),
        },
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
    }

    with open(args.out, "w", encoding="utf-8") as fh:
        json.dump(snapshot, fh, indent=2, sort_keys=True, ensure_ascii=False)
        fh.write("\n")

    snap_sha = _sha256_file(args.out)
    print(f"theorem_u_snapshot.json written; sha256={snap_sha}")
    print(f"  kernel_commit = {snapshot['kernel_commit']}")
    print(f"  headline decls = {snapshot['theorem_u']['headline_decls']}")
    print(f"  kernel_only = {kernel_only}")
    print(f"  numbers = decl {numbers.get('declarations')} / "
          f"axioms_unique {numbers.get('axioms_unique')} / "
          f"sorries_noncomment {numbers.get('sorries_noncomment')}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
