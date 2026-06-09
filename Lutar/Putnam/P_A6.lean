import Mathlib

namespace Lutar.Putnam.P_A6

/-!
# Putnam 2025 A6

**Problem.** Let `b₀ = 0` and `bₙ₊₁ = 2 bₙ² + bₙ + 1` for `n ≥ 0`. For each
`k ≥ 1`, show that `b_{2^{k+1}} − 2 · b_{2^k}` is divisible by `2^{2k+2}` but
not by `2^{2k+3}`.

**Honest status.**
* `putnam_A6_correct_pow` (the general theorem) — OPEN, proof DEFERRED (`sorry`).
* The concrete base data is REAL (kernel-checked): `b_one … b_four`,
  `d_pow_one`, `d_pow_one_val`.
* `putnam_A6_original_statement_is_false` is REAL: it shows the NAIVE
  *linear-index* reading `2^{2k+2} ∣ b_{2k+1} − 2 b_{2k}` is FALSE already at
  `k = 1` (`b₃ − 2 b₂ = 29`, and `16 ∤ 29`). This documents the index-confusion
  drift — the divisibility holds for the powers-of-two indices `2^{k+1}, 2^k`,
  NOT the linear indices `2k+1, 2k`.
-/

/-- `b₀ = 0`, `bₙ₊₁ = 2 bₙ² + bₙ + 1`. -/
def b : ℕ → ℤ
  | 0 => 0
  | (n + 1) => 2 * (b n) ^ 2 + b n + 1

theorem b_zero : b 0 = 0 := rfl
theorem b_succ (n : ℕ) : b (n + 1) = 2 * (b n) ^ 2 + b n + 1 := rfl

theorem b_one : b 1 = 1 := by show b (0 + 1) = 1; rw [b_succ, b_zero]; norm_num
theorem b_two : b 2 = 4 := by show b (1 + 1) = 4; rw [b_succ, b_one]; norm_num
theorem b_three : b 3 = 37 := by show b (2 + 1) = 37; rw [b_succ, b_two]; norm_num
theorem b_four : b 4 = 2776 := by show b (3 + 1) = 2776; rw [b_succ, b_three]; norm_num

/-- `d_pow k = b_{2^{k+1}} − 2 · b_{2^k}`. -/
def d_pow (k : ℕ) : ℤ := b (2 ^ (k + 1)) - 2 * b (2 ^ k)

theorem d_pow_one : d_pow 1 = 2768 := by
  have h : d_pow 1 = b 4 - 2 * b 2 := by norm_num [d_pow]
  rw [h, b_four, b_two]; norm_num

theorem d_pow_one_val : (16 : ℤ) ∣ d_pow 1 ∧ ¬ (32 : ℤ) ∣ d_pow 1 := by
  rw [d_pow_one]; exact ⟨by norm_num, by norm_num⟩

/-- The general claim for the powers-of-two indices (OPEN: proof deferred). -/
theorem putnam_A6_correct_pow (k : ℕ) (hk : 1 ≤ k) :
    (2 : ℤ) ^ (2 * k + 2) ∣ d_pow k ∧ ¬ (2 : ℤ) ^ (2 * k + 3) ∣ d_pow k := by
  sorry

/-- The naive LINEAR-index reading is FALSE at `k = 1` (REAL, kernel-checked). -/
theorem putnam_A6_original_statement_is_false :
    ¬ (∀ k : ℕ, 1 ≤ k → (2 : ℤ) ^ (2 * k + 2) ∣ (b (2 * k + 1) - 2 * b (2 * k))) := by
  intro h
  have h1 := h 1 (by norm_num)
  norm_num [b_three, b_two] at h1

end Lutar.Putnam.P_A6
