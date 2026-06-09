import Mathlib

namespace Lutar.Putnam.P_B4

/-!
# Putnam 2025 B4

**Problem.** For `n ≥ 2`, let `A = [aᵢⱼ]` be an `n × n` matrix of nonnegative
integers such that:
(a) `aᵢⱼ = 0` when `i + j ≤ n`;
(b) `aᵢ₊₁,ⱼ ∈ {aᵢⱼ, aᵢⱼ + 1}` for `1 ≤ i ≤ n−1`, `1 ≤ j ≤ n`;
(c) `aᵢ,ⱼ₊₁ ∈ {aᵢⱼ, aᵢⱼ + 1}` for `1 ≤ i ≤ n`, `1 ≤ j ≤ n−1`.
Let `S` be the sum of the entries and `N` the number of nonzero entries. Prove
`S ≤ (n + 2) N / 3`, i.e. `3 S ≤ (n + 2) N`.

**Honest status: DEMO** — faithful statement, proof DEFERRED (`sorry`).
Entries are modelled by `a : ℕ → ℕ → ℕ` restricted to `1 ≤ i, j ≤ n`.
-/

/-- The Putnam B4 constraints on the entry function `a` over `1 ≤ i, j ≤ n`. -/
def IsPutnamMatrix (n : ℕ) (a : ℕ → ℕ → ℕ) : Prop :=
  (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → i + j ≤ n → a i j = 0) ∧
  (∀ i j, 1 ≤ i → i ≤ n - 1 → 1 ≤ j → j ≤ n →
      a (i + 1) j = a i j ∨ a (i + 1) j = a i j + 1) ∧
  (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n - 1 →
      a i (j + 1) = a i j ∨ a i (j + 1) = a i j + 1)

/-- Sum of the entries `S`. -/
def Ssum (n : ℕ) (a : ℕ → ℕ → ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n, a i j

/-- Number of nonzero entries `N`. -/
def Ncount (n : ℕ) (a : ℕ → ℕ → ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n, (if a i j = 0 then 0 else 1)

/-- Faithful statement of Putnam 2025 B4 (DEMO: proof deferred). -/
theorem putnam_B4_correct (n : ℕ) (hn : 2 ≤ n) (a : ℕ → ℕ → ℕ)
    (h : IsPutnamMatrix n a) :
    3 * Ssum n a ≤ (n + 2) * Ncount n a := by
  sorry

end Lutar.Putnam.P_B4
