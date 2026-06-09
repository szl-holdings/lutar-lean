import Mathlib

namespace Lutar.Putnam.P_B6

/-!
# Putnam 2025 B6

**Problem.** Let `ℕ = {1, 2, 3, …}`. Find the largest real constant `r` such
that there exists a function `g : ℕ → ℕ` with `g(n+1) − g(n) ≥ (g(g(n)))^r` for
all `n ∈ ℕ`.

**Official answer.** `r = 1/2`.

**Honest status: DEMO** — faithful statement with the official extremal
constant, proof DEFERRED (`sorry`). The two conjuncts state achievability at
`r = 1/2` and impossibility for every `r > 1/2`.
-/

noncomputable def r_opt : ℝ := 1 / 2

/-- Faithful statement of Putnam 2025 B6 (DEMO: proof deferred). -/
theorem putnam_B6_correct :
    (∃ g : ℕ → ℕ, ∀ n : ℕ, 0 < n → (g (n + 1) : ℝ) - g n ≥ (g (g n) : ℝ) ^ r_opt) ∧
    (∀ r : ℝ, r_opt < r →
      ¬ ∃ g : ℕ → ℕ, ∀ n : ℕ, 0 < n → (g (n + 1) : ℝ) - g n ≥ (g (g n) : ℝ) ^ r) := by
  sorry

end Lutar.Putnam.P_B6
