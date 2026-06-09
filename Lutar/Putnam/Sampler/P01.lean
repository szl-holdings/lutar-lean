import Mathlib

namespace Lutar.Putnam.Sampler

/-!
# Sampler Problem 1 (Inequality / AM–GM with structure)

**Problem (PDF):** Let `a, b, c > 0` with `abc = 1`. Prove
`(a-1)²/(a+b+c) + (b-1)²/(a+b+c) + (c-1)²/(a+b+c) ≥ 0`.

**Faithful note:** As literally written this is a *nonnegativity warm-up*: each numerator
is a square `≥ 0` and the common denominator `a+b+c > 0`, so each summand is `≥ 0` and so is
their sum. The `abc = 1` hypothesis is kept for faithfulness even though the bound does not
need it.

**Difficulty:** 1 (warm-up).
**Status:** KERNEL-VERIFIED (sorry-free).
-/

theorem p01 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) :
    0 ≤ (a - 1) ^ 2 / (a + b + c) + (b - 1) ^ 2 / (a + b + c) + (c - 1) ^ 2 / (a + b + c) := by
  have hpos : 0 < a + b + c := by linarith
  have h1 : 0 ≤ (a - 1) ^ 2 / (a + b + c) := div_nonneg (sq_nonneg _) hpos.le
  have h2 : 0 ≤ (b - 1) ^ 2 / (a + b + c) := div_nonneg (sq_nonneg _) hpos.le
  have h3 : 0 ≤ (c - 1) ^ 2 / (a + b + c) := div_nonneg (sq_nonneg _) hpos.le
  linarith

end Lutar.Putnam.Sampler
