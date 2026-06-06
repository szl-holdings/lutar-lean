/-
  Lutar/Wave8/CPA.lean  —  G1: Closest-Point Approach (CPA) minimality.

  EXPERIMENTAL Wave8 pack.  NOT folded into the locked v11 baseline:
  locked-proven stays EXACTLY 5 {F1,F11,F12,F18,F19}.  Λ remains Conjecture 1
  (untouched here).  No open obligation, no open obligation, no fabricated numbers.

  Statement (software / Warhacker benefit):
    For two agents on linear trajectories, let `Δp` be the relative position and
    `Δv` the relative velocity (both vectors in a real inner-product space, e.g.
    `EuclideanSpace ℝ (Fin 2)`).  The squared separation at time `t` is
        f(t) = ‖Δp + t • Δv‖².
    When the closing speed is nonzero (`Δv ≠ 0`), the Closest-Point-Approach time
        t* = - ⟪Δp, Δv⟫ / ‖Δv‖²
    is the UNIQUE global minimiser of `f`, and `f(t*) ≤ f(t)` for every `t`.
    This is exactly the geometric collision-prediction kernel used by the
    killinchu de-confliction / collision-detection tab: it backs the "minimum
    separation occurs at the CPA time" guarantee with a kernel-checked proof.

  References:
    * Inner-product / norm expansion `norm_add_sq_real`, `real_inner_smul_left`,
      `real_inner_smul_right`, `real_inner_self_eq_norm_sq`:
      https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Basic.html
    * `EuclideanSpace` inner-product instance:
      https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/PiL2.html

  Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open RealInnerProductSpace

namespace Lutar.Wave8.CPA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Squared separation between two linearly-moving agents at time `t`. -/
noncomputable def sep2 (Δp Δv : E) (t : ℝ) : ℝ := ‖Δp + t • Δv‖ ^ 2

/-- The Closest-Point-Approach time. -/
noncomputable def cpaTime (Δp Δv : E) : ℝ := - ⟪Δp, Δv⟫ / ‖Δv‖ ^ 2

/-- Quadratic expansion of the squared separation in `t`. -/
theorem sep2_expand (Δp Δv : E) (t : ℝ) :
    sep2 Δp Δv t = ‖Δp‖ ^ 2 + 2 * t * ⟪Δp, Δv⟫ + t ^ 2 * ‖Δv‖ ^ 2 := by
  unfold sep2
  rw [norm_add_sq_real, real_inner_smul_right, real_inner_self_eq_norm_sq,
      norm_smul]
  have hv : (‖(t : ℝ)‖ * ‖Δv‖) ^ 2 = t ^ 2 * ‖Δv‖ ^ 2 := by
    rw [mul_pow, Real.norm_eq_abs, sq_abs]
  rw [hv]; ring

/-- Difference of separations is a perfect square in `(t - t*)`, hence ≥ 0
    whenever `Δv ≠ 0`.  This is the algebraic heart of CPA minimality. -/
theorem sep2_sub_cpa (Δp Δv : E) (hΔv : Δv ≠ 0) (t : ℝ) :
    sep2 Δp Δv t - sep2 Δp Δv (cpaTime Δp Δv)
      = ‖Δv‖ ^ 2 * (t - cpaTime Δp Δv) ^ 2 := by
  have hpos : ‖Δv‖ ^ 2 ≠ 0 := by
    have : ‖Δv‖ ≠ 0 := by simpa [norm_eq_zero] using hΔv
    positivity
  rw [sep2_expand, sep2_expand]
  unfold cpaTime
  field_simp
  ring

/-- **G1 — CPA minimality.**  When closing speed is nonzero, the squared
    separation at the CPA time is a lower bound for every time `t`. -/
theorem cpa_is_min (Δp Δv : E) (hΔv : Δv ≠ 0) (t : ℝ) :
    sep2 Δp Δv (cpaTime Δp Δv) ≤ sep2 Δp Δv t := by
  have h := sep2_sub_cpa Δp Δv hΔv t
  have hsq : (0 : ℝ) ≤ ‖Δv‖ ^ 2 * (t - cpaTime Δp Δv) ^ 2 := by positivity
  linarith [h ▸ hsq]

/-- **G1 — uniqueness of the CPA minimiser.**  If `t` attains the same squared
    separation as the CPA time, then `t = t*`.  (Strict minimality.) -/
theorem cpa_unique (Δp Δv : E) (hΔv : Δv ≠ 0) (t : ℝ)
    (ht : sep2 Δp Δv t = sep2 Δp Δv (cpaTime Δp Δv)) :
    t = cpaTime Δp Δv := by
  have h := sep2_sub_cpa Δp Δv hΔv t
  rw [ht, sub_self] at h
  have hpos : ‖Δv‖ ^ 2 ≠ 0 := by
    have : ‖Δv‖ ≠ 0 := by simpa [norm_eq_zero] using hΔv
    positivity
  have : (t - cpaTime Δp Δv) ^ 2 = 0 := by
    rcases mul_eq_zero.mp h.symm with h1 | h2
    · exact absurd h1 hpos
    · exact h2
  have : t - cpaTime Δp Δv = 0 := by
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  linarith

end Lutar.Wave8.CPA

-- Axiom disclosure (verified in CI; Mathlib build required, cannot run locally).
#print axioms Lutar.Wave8.CPA.sep2_expand
#print axioms Lutar.Wave8.CPA.sep2_sub_cpa
#print axioms Lutar.Wave8.CPA.cpa_is_min
#print axioms Lutar.Wave8.CPA.cpa_unique
