import Mathlib

namespace Lutar.Putnam.P_A2

/-!
# Putnam 2025 A2

**Problem.** Find the largest real `a` and the smallest real `b` such that
`a · x · (π − x) ≤ sin x ≤ b · x · (π − x)` for all `x ∈ [0, π]`.

**Official answer.** `a = 1/π`, `b = 4/π²`.

**Honest status: DEMO** — faithful statement with the official extremal
constants, proof DEFERRED (`sorry`).
-/

noncomputable def a_val : ℝ := 1 / Real.pi
noncomputable def b_val : ℝ := 4 / Real.pi ^ 2

/-- Faithful statement of Putnam 2025 A2 (DEMO: proof deferred). -/
theorem putnam_A2_correct :
    (∀ x : ℝ, x ∈ Set.Icc 0 Real.pi → a_val * x * (Real.pi - x) ≤ Real.sin x) ∧
    (∀ x : ℝ, x ∈ Set.Icc 0 Real.pi → Real.sin x ≤ b_val * x * (Real.pi - x)) ∧
    (∀ a : ℝ, (∀ x : ℝ, x ∈ Set.Icc 0 Real.pi → a * x * (Real.pi - x) ≤ Real.sin x) →
      a ≤ a_val) ∧
    (∀ b : ℝ, (∀ x : ℝ, x ∈ Set.Icc 0 Real.pi → Real.sin x ≤ b * x * (Real.pi - x)) →
      b_val ≤ b) := by
  sorry

end Lutar.Putnam.P_A2
