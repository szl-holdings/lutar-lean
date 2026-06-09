import Mathlib

namespace Lutar.Putnam.P_A5

/-!
# Putnam 2025 A5

**Problem.** Let `n ≥ 2`. For a sequence `s = (s₁, …, s_{n-1})` with each
`sᵢ = ±1`, let `f(s)` be the number of permutations `(a₁, …, aₙ)` of `(1, …, n)`
such that `sᵢ (aᵢ₊₁ − aᵢ) > 0` for all `i`. For each `n`, determine the
sequences `s` for which `f(s)` is maximal.

**Official answer.** The alternating sequences (`sᵢ · sᵢ₊₁ = −1`).

**Honest status: DEMO** — faithful statement, proof DEFERRED (`sorry`).
A permutation is modelled as `σ : Equiv.Perm (Fin n)` (so `aᵢ = σ(i)`), and the
sign pattern as `s : ℕ → ℤ`; `fcount` counts the realizing permutations.
-/

/-- `σ` realizes the sign pattern `s`: for every `i` with `i + 1 < n`,
`sᵢ · (σ(i+1) − σ(i)) > 0`. -/
def Realizes {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : ℕ → ℤ) : Prop :=
  ∀ i : ℕ, ∀ h : i + 1 < n,
    0 < s i * (((σ ⟨i + 1, h⟩ : Fin n).val : ℤ) - ((σ ⟨i, by omega⟩ : Fin n).val : ℤ))

/-- The number of permutations of `Fin n` realizing the sign pattern `s`. -/
noncomputable def fcount (n : ℕ) (s : ℕ → ℤ) : ℕ :=
  Nat.card {σ : Equiv.Perm (Fin n) // Realizes σ s}

/-- An alternating sign pattern starting with `+1`. -/
def altUp : ℕ → ℤ := fun i => if i % 2 = 0 then 1 else -1

/-- An alternating sign pattern starting with `−1`. -/
def altDown : ℕ → ℤ := fun i => if i % 2 = 0 then -1 else 1

/-- Faithful statement of Putnam 2025 A5 (DEMO: proof deferred): the alternating
patterns maximize the realizing count. -/
theorem putnam_A5_correct (n : ℕ) (hn : 2 ≤ n) (s : ℕ → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) :
    fcount n s ≤ fcount n altUp ∧ fcount n s ≤ fcount n altDown := by
  sorry

end Lutar.Putnam.P_A5
