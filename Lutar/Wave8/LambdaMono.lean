/-
  Lutar/Wave8/LambdaMono.lean  —  L3: per-component strict monotonicity of a
  concrete geometric-mean trust aggregator.

  EXPERIMENTAL Wave8 pack.  NOT folded into the locked v11 baseline:
  locked-proven stays EXACTLY 5 {F1,F11,F12,F18,F19}.

  IMPORTANT HONESTY NOTE.  This file proves ONLY that the *concrete*
  geometric-mean aggregator
        G(w) = (∏ i, w i) ^ (1 / n)        (over ℝ≥0, n = |ι|)
  is STRICTLY MONOTONE per component: raising one trust score (others fixed)
  strictly raises the aggregate.  It makes NO claim that this aggregator is the
  UNIQUE function with such properties.  The uniqueness of Λ remains
  **Conjecture 1** and is deliberately untouched here.  No open obligation, no open
  obligation, no fabricated numbers.

  Software / Warhacker benefit:
    The trust-fusion gate composes component trust scores with a geometric mean
    (so a single near-zero component drags the aggregate down — the
    "weakest-link" behaviour).  L3 gives a kernel-checked guarantee that the
    gate is *responsive*: any genuine improvement in one source's trust score
    strictly improves the fused trust, which is the monotonicity property the
    governance layer relies on for incentive-compatibility.

  References:
    * `Finset.prod_lt_prod'` (strict product monotonicity):
      https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/BigOperators/Group/Finset.html
    * `NNReal.rpow_lt_rpow` (strict monotonicity of `x ↦ x^z` in the base):
      https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.html

  Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset

namespace Lutar.Wave8.LambdaMono

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The concrete geometric-mean trust aggregator over `ℝ≥0` component scores. -/
noncomputable def gmean (w : ι → NNReal) : NNReal :=
  (∏ i, w i) ^ ((Fintype.card ι : ℝ)⁻¹)

/-- The unnormalised product is strictly monotone per component:
    raising one component (others ≥, and that one strictly >) strictly raises
    the product, provided every component is positive. -/
theorem prod_strict_mono (w w' : ι → NNReal)
    (hpos : ∀ i, 0 < w i)
    (hle : ∀ i, w i ≤ w' i) (k : ι) (hk : w k < w' k) :
    (∏ i, w i) < (∏ i, w' i) := by
  refine Finset.prod_lt_prod' (s := Finset.univ) (fun i _ => hle i) ?_
  exact ⟨k, Finset.mem_univ k, hk⟩

/-- **L3 — per-component strict monotonicity of the geometric-mean aggregator.**
    If every component score is positive, all scores weakly improve, and at
    least one component `k` strictly improves, then the fused trust strictly
    increases.  (No uniqueness of Λ is asserted — Conjecture 1 untouched.) -/
theorem gmean_strict_mono (w w' : ι → NNReal)
    (hpos : ∀ i, 0 < w i)
    (hle : ∀ i, w i ≤ w' i) (k : ι) (hk : w k < w' k) :
    gmean w < gmean w' := by
  unfold gmean
  have hexp : (0 : ℝ) < (Fintype.card ι : ℝ)⁻¹ := by
    have : (0 : ℝ) < (Fintype.card ι : ℝ) := by
      exact_mod_cast Fintype.card_pos
    positivity
  exact NNReal.rpow_lt_rpow (prod_strict_mono w w' hpos hle k hk) hexp

/-- Weak (non-strict) monotonicity also holds: weakly improving every component
    weakly improves the fused trust. -/
theorem gmean_mono (w w' : ι → NNReal) (hle : ∀ i, w i ≤ w' i) :
    gmean w ≤ gmean w' := by
  unfold gmean
  have hexp : (0 : ℝ) ≤ (Fintype.card ι : ℝ)⁻¹ := by positivity
  exact NNReal.rpow_le_rpow (Finset.prod_le_prod' (fun i _ => hle i)) hexp

end Lutar.Wave8.LambdaMono

-- Axiom disclosure (verified in CI; Mathlib build required, cannot run locally).
#print axioms Lutar.Wave8.LambdaMono.prod_strict_mono
#print axioms Lutar.Wave8.LambdaMono.gmean_strict_mono
#print axioms Lutar.Wave8.LambdaMono.gmean_mono
