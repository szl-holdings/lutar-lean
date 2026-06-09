import Mathlib

namespace Lutar.Putnam.P_B3

/-!
# Putnam 2025 B3

**Problem.** Suppose `S` is a nonempty set of positive integers such that if
`n ∈ S`, then every positive divisor of `2025^n − 15^n` is in `S`. Must `S`
contain all positive integers?

**Corrected expression.** `2025^n − 15^n` (a POWER).

*Drift note.* An earlier version read `2025 · n − 15^n`, which is negative for
`n ≥ 4` (e.g. `n = 4`: `8100 − 50625 < 0`) and so ill-posed for "positive
divisor". The power form `2025^n − 15^n` is positive for all `n ≥ 1`.

**Official answer.** Yes.

**Honest status: DEMO** — faithful statement, proof DEFERRED (`sorry`).
`val_at_1` is REAL (kernel-checked).
-/

/-- `S` is closed under positive divisors of `2025^n − 15^n`. -/
def ClosedUnderDivisors (S : Set ℕ) : Prop :=
  ∀ n ∈ S, ∀ d : ℕ, 0 < d → (d : ℤ) ∣ ((2025 : ℤ) ^ n - (15 : ℤ) ^ n) → d ∈ S

/-- `2025¹ − 15¹ = 2010` (REAL). -/
theorem val_at_1 : (2025 : ℤ) ^ 1 - (15 : ℤ) ^ 1 = 2010 := by norm_num

/-- Faithful statement of the corrected Putnam 2025 B3 (DEMO: proof deferred). -/
theorem putnam_B3_correct (S : Set ℕ) (hne : S.Nonempty)
    (hpos : ∀ n ∈ S, 0 < n) (hclosed : ClosedUnderDivisors S) :
    ∀ n : ℕ, 0 < n → n ∈ S := by
  sorry

end Lutar.Putnam.P_B3
