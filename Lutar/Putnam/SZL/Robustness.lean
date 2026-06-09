import Mathlib

namespace Lutar.Putnam.SZL.Robustness

/-!
# SZL original — scaling robustness (Lipschitz bound)

An SZL-original companion to the Putnam set: scaling by `c` on `ℝ` is exactly
`|c|`-Lipschitz, hence nonexpansive when `|c| ≤ 1`. This is the robustness
backbone behind certified-radius style guarantees. All proofs are REAL
(kernel-checked); no `sorry`, no new axiom.

EXPERIMENTAL — not folded into the locked v11 baseline.
-/

/-- Scaling by `c` is exactly `|c|`-Lipschitz: `|c x − c y| = |c| · |x − y|`. -/
theorem scaling_lipschitz_eq (c x y : ℝ) : |c * x - c * y| = |c| * |x - y| := by
  rw [← mul_sub, abs_mul]

/-- One-sided Lipschitz bound. -/
theorem scaling_lipschitz (c x y : ℝ) : |c * x - c * y| ≤ |c| * |x - y| :=
  le_of_eq (scaling_lipschitz_eq c x y)

/-- A contraction: if `|c| ≤ 1`, scaling by `c` is nonexpansive. -/
theorem scaling_nonexpansive (c x y : ℝ) (hc : |c| ≤ 1) :
    |c * x - c * y| ≤ |x - y| := by
  rw [scaling_lipschitz_eq]
  calc |c| * |x - y| ≤ 1 * |x - y| :=
        mul_le_mul_of_nonneg_right hc (abs_nonneg _)
    _ = |x - y| := one_mul _

end Lutar.Putnam.SZL.Robustness
