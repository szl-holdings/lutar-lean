# STATUS.md — lutar-lean (Lean 4 Proof Kernel)

**Updated:** 2026-06-02
**Doctrine v11 — 749 / 14 / 163 — replay hash c7c0ba17**

---

## What's Live

- **Lean 4 proof kernel** — formal proofs of the Λ aggregator
- **Canonical numbers** — 749 declarations · 14 unique axioms (15 raw, 1 duplicate) · 163 tracked sorries (112 baseline + 51 Putnam)
- **Replay hash** — c7c0ba17
- **`lean_numbers.py`** — CI script regenerates canonical numbers on every push
- **CITATION.cff** — citable, ORCID 0009-0001-0110-4173
- **Concept DOI** — [10.5281/zenodo.19944926](https://doi.org/10.5281/zenodo.19944926)

## What's Experimental

- **Putnam sorry reduction** — 51 Putnam sorries are open; reduction in progress
- **Mathlib alignment** — periodic Mathlib upgrades may require proof adjustments
- **Theorem U (`Lutar/Uniqueness/`)** — a CONDITIONAL Λ-uniqueness reframing, additive and
  EXPERIMENTAL (NOT folded into the locked 749/14/163 @ c7c0ba17 baseline; locked-proven stays
  EXACTLY 5 {F1,F11,F12,F18,F19}). Introduces the audit-invariant equivalence `≈Λ` (`LambdaEquiv`:
  a genuine `Equivalence` + `Decidable` + the `lambdaEquiv_nondegenerate` anti-vacuity guard — the
  proven A1–A5 counterexample `maxAgg` is `≉Λ` to `Λ 2`, so "uniqueness modulo `≈Λ`" is non-trivial),
  the `IdentifiabilityAssumptions` (IA) bundle with `FactorAssumptions`/`SeparableAssumptions`
  bridges, and **Theorem U** (`TheoremU_LambdaUnique`) proving any two IA-solutions are `≈Λ`
  (indeed `=`) **BY REDUCTION** to the already-proven `Round13.lambda_unique_of_separable` /
  `lambda_unique_of_factors` — NO new `axiom` token, no proof placeholder. The unconditional
  statement `Conjecture1_LambdaUnique` ships **statement-only**: Λ stays **Conjecture 1**
  (machine-checked false as stated). A dedicated axiom-hygiene CI gate in `lake-build.yml` enforces
  the no-axiom / no-placeholder invariant; see `DEPENDENCY_MAP.md`.

## Uniqueness tracking (Doctrine v11 citation rule)

Any Λ-uniqueness claim cites **Theorem U** / **U₁** / **U₂** — uniqueness modulo the
audit-invariant equivalence `≈Λ` under the Identifiability Assumptions (IA); strict `=`
only under the `Anchored`/`Normalized` predicate. Source: [`Lutar/Uniqueness/TheoremU.lean`](./Lutar/Uniqueness/TheoremU.lean),
ledger [`DEPENDENCY_MAP.md`](./DEPENDENCY_MAP.md). The [overclaim guard](./.github/workflows/overclaim-guard.yml)
fails CI on any unqualified Λ-uniqueness or Conjecture-1 overclaim.

| Result | Status |
|---|---|
| **Theorem U** (`TheoremU_LambdaUnique`) — uniqueness modulo `≈Λ` under IA | **REAL · CONDITIONAL** (axiom-free, no `sorry`) |
| **Corollary U₁** (`CorollaryU1_LambdaUnique_Separable`) | **REAL · CONDITIONAL** |
| **Corollary U₂** (`CorollaryU2_LambdaUnique_Factors`) | **REAL · CONDITIONAL** |
| strict `=` under `Anchored`/`Normalized` (`TheoremU_LambdaUnique_eq`) | **REAL · CONDITIONAL** |
| **Conjecture 1** (`Conjecture1_LambdaUnique`) — unconditional uniqueness | **OPEN / DEMO** — statement-only, machine-checked FALSE as stated; bounty `lambda-bounty` |

## What's Deprecated

Nothing deprecated in this repo.

---

*Co-Authored-By: Perplexity Computer Agent*
*Doctrine v11 — 749/14/163 — c7c0ba17*
