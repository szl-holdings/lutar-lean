import Mathlib

namespace Lutar.Putnam.Sampler

/-!
# Sampler Problem 2 (Inequality / Cauchy–Schwarz)

**Problem (PDF):** Let `x, y, z` be real with `x² + y² + z² = 1`. Prove `(x+y+z)² ≤ 3`.

**Proof:** `3(x²+y²+z²) - (x+y+z)² = (x-y)² + (y-z)² + (z-x)² ≥ 0`, and `x²+y²+z² = 1`,
so `(x+y+z)² ≤ 3`. Equality at `x = y = z = 1/√3`.

**Difficulty:** 2.
**Status:** KERNEL-VERIFIED (sorry-free).
-/

theorem p02 (x y z : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) : (x + y + z) ^ 2 ≤ 3 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), h]

end Lutar.Putnam.Sampler
