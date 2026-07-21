/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Uniqueness/TheoremU.lean — Theorem U: conditional Λ-uniqueness modulo `≈Λ`

This module lands **Theorem U** and its corollaries **by reduction** to the already-proven
Round13 conditional theorems (`lambda_unique_of_separable`, `lambda_unique_of_factors`). It
introduces NO new `axiom` token and contains no proof placeholder.

## What is PROVEN here (placeholder-free; NO new `axiom` token)

* `CorollaryU2_LambdaUnique_Factors` — under `FactorAssumptions`, `Φ = Λ k`
  (reduction to `Round13.lambda_unique_of_factors`).
* `CorollaryU1_LambdaUnique_Separable` — under `SeparableAssumptions`, `Φ = Λ k`
  (reduction to `Round13.lambda_unique_of_separable`).
* `identifiability_forces_lambda` — under `IdentifiabilityAssumptions`, `Φ = Λ k`
  (the strict-equality core; IA bundles the separable data).
* `TheoremU_LambdaUnique` — **Theorem U**: any two IA-solutions are `≈Λ`-equivalent. Proved by
  reduction: both equal `Λ k`, hence share the audit invariant.
* `TheoremU_LambdaUnique_eq` — the same conclusion strengthened to strict `=`.
* `lambda_equiv_to_eq_of_anchored` — the gauge-upgrade: `≈Λ` strengthens to `=` once both
  aggregators are `Anchored` to the canonical Λ gauge.

## Honesty / scope
- Theorem U is **CONDITIONAL** on the identifiability assumptions (existence + separability +
  normalization), all discharged through proven in-tree lemmas + Mathlib. The UNCONDITIONAL
  uniqueness statement (`Conjecture1_LambdaUnique`) stays OPEN / machine-checked-false; Λ stays
  **Conjecture 1**. Locked-proven set unchanged (EXACTLY 8 {F1,F4,F7,F11,F12,F18,F19,F22}). NO new `axiom`; no placeholders.

Signed-off-by: SZL CTO <cto@szl-holdings.com>
-/
import Lutar.Uniqueness.LambdaEquiv
import Lutar.Uniqueness.Identifiability
import Lutar.Round13.LambdaSeparable
import Lutar.Round13.Lambda_Uniqueness

namespace Lutar.Uniqueness

open Lutar Lutar.Round13

/-- **Corollary U₂.** Under factor assumptions, `Φ = Λ k`
    (reduction to `Round13.lambda_unique_of_factors`). -/
theorem CorollaryU2_LambdaUnique_Factors {k : ℕ} (Φ : Aggregator k)
    (fa : FactorAssumptions Φ) : Φ = Λ k :=
  lambda_unique_of_factors fa.pos Φ fa.axioms fa.exps fa.factors

/-- **Corollary U₁.** Under separable assumptions, `Φ = Λ k`
    (reduction to `Round13.lambda_unique_of_separable`). -/
theorem CorollaryU1_LambdaUnique_Separable {k : ℕ} (Φ : Aggregator k)
    (sa : SeparableAssumptions Φ) : Φ = Λ k :=
  lambda_unique_of_separable sa.pos Φ sa.axioms sa.slices sa.separates
    sa.slice_mul sa.slice_one sa.slice_mono

/-- **Identifiability forces Λ.** Under Identifiability Assumptions, `Φ = Λ k`. This is the
    strict-equality core that Theorem U coarsens to `≈Λ`. -/
theorem identifiability_forces_lambda {k : ℕ} (Φ : Aggregator k)
    (ia : IdentifiabilityAssumptions Φ) : Φ = Λ k :=
  lambda_unique_of_separable ia.pos Φ ia.axioms ia.slices ia.separates
    ia.slice_mul ia.slice_one ia.slice_mono

/-- **Theorem U — conditional Λ-uniqueness modulo `≈Λ`.** Any two aggregators satisfying the
    Identifiability Assumptions are `≈Λ`-equivalent. Proved by reduction: each equals `Λ k`,
    so they share the audit invariant. (By `lambdaEquiv_nondegenerate` this conclusion is
    non-vacuous: `≈Λ` is strictly coarser than the total relation.) -/
theorem TheoremU_LambdaUnique {k : ℕ} (Φ Ψ : Aggregator k)
    (iaΦ : IdentifiabilityAssumptions Φ) (iaΨ : IdentifiabilityAssumptions Ψ) :
    LambdaEquiv Φ Ψ := by
  have hΦ := identifiability_forces_lambda Φ iaΦ
  have hΨ := identifiability_forces_lambda Ψ iaΨ
  unfold LambdaEquiv InvariantΛ
  rw [hΦ, hΨ]

/-- **Theorem U (strict form).** Under IA the two solutions are not merely `≈Λ` but literally
    equal — both reduce to `Λ k`. -/
theorem TheoremU_LambdaUnique_eq {k : ℕ} (Φ Ψ : Aggregator k)
    (iaΦ : IdentifiabilityAssumptions Φ) (iaΨ : IdentifiabilityAssumptions Ψ) :
    Φ = Ψ :=
  (identifiability_forces_lambda Φ iaΦ).trans (identifiability_forces_lambda Ψ iaΨ).symm

/-- **Gauge upgrade.** Strict `=` is recoverable from `≈Λ` once both aggregators are
    `Anchored` to the canonical Λ gauge (the budget-1 normalization that pins the fiber
    representative). Without anchoring, `≈Λ` is strictly coarser than `=`
    (`lambdaEquiv_nondegenerate`). -/
theorem lambda_equiv_to_eq_of_anchored {k : ℕ} {Φ Ψ : Aggregator k}
    (_h : LambdaEquiv Φ Ψ) (hΦ : Anchored Φ) (hΨ : Anchored Ψ) : Φ = Ψ :=
  hΦ.trans hΨ.symm

end Lutar.Uniqueness
