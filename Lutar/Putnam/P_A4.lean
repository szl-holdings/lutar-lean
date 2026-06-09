import Mathlib

namespace Lutar.Putnam.P_A4

/-!
# Putnam 2025 A4

**Problem.** Find the minimal `k` such that there exist `k × k` real matrices
`A₁, …, A₂₀₂₅` with the property that `Aᵢ Aⱼ = Aⱼ Aᵢ` iff `|i − j| ∈ {0, 1, 2024}`.

**Corrected answer.** `k = 3`.

*Drift note.* An earlier version of this file asserted `k = 2`. We formalize the
corrected minimum `k = 3`: the two conjuncts below — a `3 × 3` realization
exists, and no `2 × 2` realization exists — together pin the minimum at `3`
(a `2 × 2` non-realization implies no smaller size works, by embedding).

**Honest status: DEMO** — faithful statement, proof DEFERRED (`sorry`).
-/

/-- Faithful statement of the corrected Putnam 2025 A4 answer (DEMO: proof
deferred). -/
theorem putnam_A4_correct :
    (∃ A : Fin 2025 → Matrix (Fin 3) (Fin 3) ℝ,
        ∀ i j : Fin 2025, (A i * A j = A j * A i) ↔
          (Nat.dist i.val j.val ∈ ({0, 1, 2024} : Set ℕ))) ∧
    ¬ (∃ A : Fin 2025 → Matrix (Fin 2) (Fin 2) ℝ,
        ∀ i j : Fin 2025, (A i * A j = A j * A i) ↔
          (Nat.dist i.val j.val ∈ ({0, 1, 2024} : Set ℕ))) := by
  sorry

end Lutar.Putnam.P_A4
