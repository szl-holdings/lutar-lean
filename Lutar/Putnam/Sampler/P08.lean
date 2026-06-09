import Mathlib

namespace Lutar.Putnam.Sampler

/-!
# Sampler Problem 8 (Geometry / parallelogram law in ℝⁿ)

**Problem (PDF):** For vectors `u, v ∈ ℝⁿ`, prove the parallelogram law
`‖u+v‖² + ‖u-v‖² = 2‖u‖² + 2‖v‖²`.

**Faithful note:** `ℝⁿ` is modeled as `EuclideanSpace ℝ (Fin n)`, the standard real inner
product space. The identity is Mathlib's `parallelogram_law_with_norm`.

**Difficulty:** 2.
**Status:** KERNEL-VERIFIED (sorry-free).
-/

theorem p08 {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have h := parallelogram_law_with_norm ℝ u v
  simp only [pow_two]
  linarith [h]

end Lutar.Putnam.Sampler
