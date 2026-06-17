# Architecture — lutar-lean

> Doctrine v11 LOCKED `749/14/163` · Kernel commit `c7c0ba17` · locked-proven = 8
> `{F1,F4,F7,F11,F12,F18,F19,F22}` · Λ = **Conjecture 1** (conditional Theorem U,
> NOT a closed theorem) · SLSA L1 honest · L2 roadmap.

`lutar-lean` is the Lean 4 + Mathlib formalization that formally underwrites SZL's
governance math. It is the **single source of truth** for every "proven" claim made
anywhere in the SZL ecosystem.

## High-level shape

```
lutar-lean/
├── Lutar/ , Lutar.lean        Core library: Λ aggregator, LutarAxioms (A1–A5),
│                              aggregator bounds / monotonicity / permutation-
│                              invariance, hash-chain tamper-evidence, conformal
│                              coverage, quorum agreement.
├── Main.lean / MainRef.lean   Executable entry points / reference runners.
├── RefVectors.lean            Reference vectors checked against runtime outputs.
├── TH8/ , Showcase/           Theorem-U / Wave8 locked-set declarations + showcase.
├── conjectures/ , proposals/  Open conjectures and proof proposals (Tier-2 work).
├── bounties/                  Λ-bounty problem statements.
├── docs/                      Long-form proof documentation.
├── tests/                     Lean + script tests.
├── scripts/, *.py             count_sorries.py, scoreboard.py, propose_proof.py.
└── lakefile.lean, lake-manifest.json, lean-toolchain   Build pinning.
```

## Two-tier honesty doctrine

The proof estate is split into two tiers that never blend:

- **Tier 1 — LOCKED.** Exactly **8** formulas are locked-proven
  (`F1, F4, F7, F11, F12, F18, F19, F22`). They are zero-`sorry`, use only
  Lean-core axioms `[propext, Classical.choice, Quot.sound]`, and the fact that there
  are *exactly 8* is itself a Lean theorem
  (`Lutar.Wave8.AxiomDisclosure.locked_count_eight`). The locked set cannot silently
  grow.
- **Tier 2 — EXPERIMENTAL · CI-green.** Kernel-verified but explicitly labeled
  conditional; never counted in the locked set.

`Λ` (the trust aggregator — geometric mean over provenance, containment, coherence,
convergence) is published as **Conjecture 1**, conditional on Theorem U. It is never
asserted as a closed theorem.

## CI gates (required on `main`)

`DCO` · `lake build + numbers` · `overclaim / Governed surfaces are honest (Theorem U
citation rule)` · `Theorem-U snapshot honesty (PR merge gate)`. The canonical counts
`749/14/163` are machine-enforced; a divergent count fails the build.

## Downstream consumers

The proven properties here back the runtime claims of **a11oy**, **killinchu**, the
UDS bundles, and the **szl-papers** academic corpus. If a property is asserted in the
apps or papers, it is either proven here and labeled *locked*, proven *conditionally*,
or honestly labeled a **conjecture**.

## Provenance

Verified snapshots are anchored into `szl-lake` (DSSE receipts). DOI
[10.5281/zenodo.20434308](https://doi.org/10.5281/zenodo.20434308).

---

© 2026 Lutar, Stephen P. — SZL Holdings · Apache-2.0
