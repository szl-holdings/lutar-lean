import Mathlib

namespace Lutar.Putnam.Sampler

/-!
# Sampler Problem 3 (Number theory / quadratic residues)

**Problem (PDF):** Show there is no integer `n` with `n² ≡ 2 (mod 4)`.

**Faithful note:** `Int.ModEq 4 (n^2) 2` is *by definition* `n^2 % 4 = 2 % 4`, and `2 % 4 = 2`,
so the statement `¬ (n² ≡ 2 [ZMOD 4])` is exactly `n ^ 2 % 4 ≠ 2`, which is what we prove.

**Proof:** Split `n` even/odd. If `n = k + k` then `n² = 4k²`, so `n² % 4 = 0`. If
`n = 2k+1` then `n² = 4(k²+k) + 1`, so `n² % 4 = 1`. Neither is `2`.

**Difficulty:** 1.
**Status:** KERNEL-VERIFIED (sorry-free).
-/

theorem p03 (n : ℤ) : n ^ 2 % 4 ≠ 2 := by
  rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [hk]
    have h1 : (k + k) ^ 2 = 4 * k ^ 2 := by ring
    rw [h1]; omega
  · rw [hk]
    have h2 : (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 := by ring
    rw [h2]; omega

end Lutar.Putnam.Sampler
