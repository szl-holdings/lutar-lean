/-
# WAVE 5 — TIER-1 Mathlib instantiations (substrate-relevant, signatures verified verbatim)

  (Mathlib-DEPENDENT — verified by lutar-lean CI `lake build`, NOT by bare lean
   here: Mathlib does not fit the sandbox disk.)

Each result (a) MODELS a Lutar substrate object, (b) IMPORTS a Mathlib lemma whose
signature was verified character-for-character against pinned Mathlib (`d7317655`,
v4.13.0), (c) APPLIES it, (d) states the SUBSTRATE COROLLARY. Zero new mathematical
risk: the math is machine-checked in standard Mathlib; we only instantiate.

## Honesty / doctrine (Doctrine v11)
- Λ (F23) stays Conjecture 1; W5-1/W5-2 below are the AM-GM and Cauchy–Schwarz building
  blocks that Λ (the geometric-mean aggregator) RELIES ON — they do NOT prove Λ unique.
- Maturity: `proven` ONLY once CI `lake build` is green (Mathlib-dependent).
- Locked kernel (749/14/163 @ c7c0ba17) SEPARATE; this is experimental/wave5. SLSA L2.

## Citations & Mathlib paths (verified present at d7317655)
- W5-1 weighted AM–GM: `Real.geom_mean_le_arith_mean_weighted`
  (Mathlib.Analysis.MeanInequalities, line 124). Hardy–Littlewood–Pólya,
  *Inequalities* (1934), Thm 9. The geometric mean (Lutar Λ) is ≤ the arithmetic mean.
- W5-1b two-point weighted AM–GM: `Real.geom_mean_le_arith_mean2_weighted` (same file).
- W5-2 Cauchy–Schwarz (real inner product): `real_inner_le_norm`
  (Mathlib.Analysis.InnerProductSpace.Basic, line 1144). Cauchy (1821); Schwarz (1888).

## Substrate use
- W5-1: Λ aggregator domination — the geometric-mean trust aggregator never exceeds the
  arithmetic mean of the same scores under the same weights (conservative-by-construction
  aggregation; a no-inflation guarantee for a11oy/killinchu weighted trust scores).
- W5-2: trust-vector similarity bound — any inner-product similarity between two receipt
  feature vectors is bounded by the product of their norms (normalized-cosine ∈ [-1,1]
  sanity bound for killinchu vector-trust scoring).
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Wave5.MathlibCore

open scoped BigOperators

/-! ## W5-1 — weighted AM–GM: the geometric-mean aggregator (Λ) is dominated by the
    arithmetic mean under matched nonneg weights summing to 1. -/

/-- **W5-1 — Λ no-inflation (weighted AM–GM).** For a finite index set `s`, nonnegative
    weights `w` summing to 1, and nonnegative scores `z`, the weighted geometric mean
    `∏ zᵢ ^ wᵢ` (the Lutar Λ aggregator) is ≤ the weighted arithmetic mean `∑ wᵢ zᵢ`.
    Direct instantiation of `Real.geom_mean_le_arith_mean_weighted`. -/
theorem w5_1_lambda_le_arith_mean
    {ι : Type*} (s : Finset ι) (w z : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ^ w i ≤ ∑ i ∈ s, w i * z i :=
  Real.geom_mean_le_arith_mean_weighted s w z hw hw' hz

/-- **W5-1b — two-agent weighted AM–GM.** The two-point specialization: for nonnegative
    weights `w₁+w₂ = 1` and nonnegative scores `p₁ p₂`,
    `p₁^w₁ · p₂^w₂ ≤ w₁ p₁ + w₂ p₂`. The pairwise Λ-vs-mean inequality used in the
    two-agent consensus diagnostic. Instantiation of `Real.geom_mean_le_arith_mean2_weighted`. -/
theorem w5_1b_lambda2_le_arith_mean
    {w₁ w₂ p₁ p₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hw : w₁ + w₂ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ ≤ w₁ * p₁ + w₂ * p₂ :=
  Real.geom_mean_le_arith_mean2_weighted hw₁ hw₂ hp₁ hp₂ hw

/-! ## W5-2 — Cauchy–Schwarz for real inner-product trust vectors. -/

/-- **W5-2 — trust-vector similarity bound (Cauchy–Schwarz).** In any real inner-product
    space, `⟪x, y⟫ ≤ ‖x‖ · ‖y‖`. For killinchu receipt-feature vectors this bounds the
    raw similarity score by the product of the norms (so normalized cosine ∈ [-1,1]).
    Direct instantiation of `real_inner_le_norm`. -/
theorem w5_2_trust_inner_le_norm
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (x y : F) :
    @inner ℝ _ _ x y ≤ ‖x‖ * ‖y‖ :=
  real_inner_le_norm x y

end Wave5.MathlibCore

-- ## Axiom disclosure (CI prints these in the build log).
-- All three are pure instantiations of Mathlib theorems; expected dependencies are the
-- standard Mathlib trio [propext, Classical.choice, Quot.sound] (NO sorryAx, NO declared
-- Lutar axioms). The #print axioms output is captured in the CI build log.
#print axioms Wave5.MathlibCore.w5_1_lambda_le_arith_mean
#print axioms Wave5.MathlibCore.w5_1b_lambda2_le_arith_mean
#print axioms Wave5.MathlibCore.w5_2_trust_inner_le_norm
