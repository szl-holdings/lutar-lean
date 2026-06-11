/-
Copyright © 2026 Stephen P. Lutar Jr. (SZL Holdings).
Released under the Apache-2.0 License.

# Neuroplasticity — machine-checked properties of SZL's learning-rule pillar.

## What is NEW here (vs the existing kernel)

`szl_neuroplasticity.py` grounds a11oy's agent learning loop in cited
neuroplasticity math (Hebb/Oja/BCM/STDP/critical-period). This file machine-checks
the order/analysis properties that backbone two of those rules:

1. `cp_strict_antitone_after_peak` — the Hubel–Wiesel critical-period
   plasticity envelope `α(t) = α_max · exp(−(t − t_peak)²/(2σ²))` is strictly
   decreasing for `t > t_peak` (plasticity only wanes after the peak). Real-analysis
   monotonicity, no `sorry`.
2. `bcm_potentiation_iff` — the BCM plasticity sign φ(y) = y·(y − θ_M) is positive
   (potentiation) iff postsynaptic activity `y` exceeds the sliding threshold `θ_M`
   (for `y > 0`). Algebraic, no `sorry`.

## What this does NOT do (doctrine hard gate)

This adds NOTHING to the locked-proven set (stays EXACTLY 8). It does NOT touch Λ:
unconditional Λ-uniqueness stays **Conjecture 1** (machine-checked FALSE); these
learning-rule properties are EXPERIMENTAL/PROPOSED-tier, never theorems about Λ.
Trust never 100%.
Citations: Hubel & Wiesel (Nobel 1981); Bienenstock–Cooper–Munro (1982).
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Monotone.Basic

namespace Lutar.Neuroplasticity

open Real

/-- Hubel–Wiesel critical-period plasticity envelope:
`cp α_max t_peak σ t = α_max · exp(−(t − t_peak)² / (2 σ²))`. -/
noncomputable def cp (αmax tpeak σ t : ℝ) : ℝ :=
  αmax * Real.exp (-((t - tpeak) ^ 2) / (2 * σ ^ 2))

/-- The envelope is non-negative when `αmax ≥ 0`. -/
theorem cp_nonneg {αmax tpeak σ t : ℝ} (h : 0 ≤ αmax) : 0 ≤ cp αmax tpeak σ t := by
  unfold cp
  exact mul_nonneg h (Real.exp_nonneg _)

/-- The envelope attains value `αmax` at the peak `t = tpeak`. -/
theorem cp_peak (αmax tpeak σ : ℝ) : cp αmax tpeak σ tpeak = αmax := by
  unfold cp
  simp

/-- After the peak (`tpeak ≤ a < b`), with positive amplitude and width, the
critical-period plasticity envelope is strictly decreasing: plasticity wanes.
(Proof: the exponent `−(t−tpeak)²/(2σ²)` is strictly decreasing for `t ≥ tpeak`,
and `exp` is strictly monotone, then scale by `αmax > 0`.) -/
theorem cp_strict_antitone_after_peak
    {αmax tpeak σ a b : ℝ} (hα : 0 < αmax) (hσ : 0 < σ)
    (hpa : tpeak ≤ a) (hab : a < b) :
    cp αmax tpeak σ b < cp αmax tpeak σ a := by
  unfold cp
  apply mul_lt_mul_of_pos_left _ hα
  apply Real.exp_lt_exp.mpr
  -- need: -(b - tpeak)^2/(2σ^2) < -(a - tpeak)^2/(2σ^2)
  have hden : (0 : ℝ) < 2 * σ ^ 2 := by positivity
  -- the squared distances satisfy (a - tpeak)^2 < (b - tpeak)^2
  have hbase : (0 : ℝ) ≤ a - tpeak := by linarith
  have hlt : a - tpeak < b - tpeak := by linarith
  have hsq : (a - tpeak) ^ 2 < (b - tpeak) ^ 2 := by
    apply pow_lt_pow_left₀ hlt hbase
    norm_num
  -- goal: -(b-tpeak)^2/(2σ^2) < -(a-tpeak)^2/(2σ^2).
  -- rewrite numerators as negations, reduce to a strict division on the
  -- positive denominator, then negate.
  rw [neg_div, neg_div, neg_lt_neg_iff]
  -- goal: (a-tpeak)^2/(2σ^2) < (b-tpeak)^2/(2σ^2); divide hsq by the positive denominator
  gcongr

/-- BCM plasticity function `φ(y) = y·(y − θ_M)`. (Bienenstock–Cooper–Munro 1982.) -/
def bcmPhi (y θM : ℝ) : ℝ := y * (y - θM)

/-- For positive postsynaptic activity, BCM potentiates (φ > 0) iff `y` exceeds the
sliding modification threshold `θ_M`. -/
theorem bcm_potentiation_iff {y θM : ℝ} (hy : 0 < y) :
    0 < bcmPhi y θM ↔ θM < y := by
  unfold bcmPhi
  constructor
  · intro h
    -- from 0 < y·(y − θM) and 0 < y, derive 0 < y − θM, hence θM < y
    nlinarith [h, hy]
  · intro h
    have : 0 < y - θM := by linarith
    exact mul_pos hy this

end Lutar.Neuroplasticity
