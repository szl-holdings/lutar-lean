import Mathlib

namespace Lutar.Putnam.SZL.LambdaEquiv

/-!
# SZL original — positive-scaling equivalence (Λ ≈ scaling)

An SZL-original companion to the Putnam set: positive scaling on a real vector
space is an equivalence relation. This is the scale-invariance backbone of the
Λ-invariant story (Λ identified up to positive scaling). All proofs are REAL
(kernel-checked); no `sorry`, no new axiom.

EXPERIMENTAL — not folded into the locked v11 baseline.
-/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Positive-scaling relation: `x ≈ y` iff `y = c • x` for some `c > 0`. -/
def ScaleEquiv (x y : V) : Prop := ∃ c : ℝ, 0 < c ∧ y = c • x

theorem scaleEquiv_refl (x : V) : ScaleEquiv x x :=
  ⟨1, one_pos, (one_smul ℝ x).symm⟩

theorem scaleEquiv_symm {x y : V} (h : ScaleEquiv x y) : ScaleEquiv y x := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

theorem scaleEquiv_trans {x y z : V} (hxy : ScaleEquiv x y) (hyz : ScaleEquiv y z) :
    ScaleEquiv x z := by
  obtain ⟨c, hc, rfl⟩ := hxy
  obtain ⟨d, hd, rfl⟩ := hyz
  exact ⟨d * c, mul_pos hd hc, by rw [smul_smul]⟩

/-- Positive scaling is an equivalence relation (REAL, kernel-checked). -/
theorem scaleEquiv_equivalence : Equivalence (ScaleEquiv (V := V)) :=
  ⟨scaleEquiv_refl, scaleEquiv_symm, scaleEquiv_trans⟩

end Lutar.Putnam.SZL.LambdaEquiv
