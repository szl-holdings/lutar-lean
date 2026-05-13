/-
# Bound theorem

**Theorem 2.** For every axes vector `x : Fin k → [0,1]`,

    min_i (x i)  ≤  Λ_k x  ≤  max_i (x i)  ≤  1.

This is the substrate guarantee that the Λ-gate is *interpretable*: a passing
Λ value never exceeds the best axis nor falls below the worst.

Status: stated; full proof reduces to standard AM/GM theory in Mathlib
(`Real.inner_le_nnreal_iff` and `Finset.prod_le_pow_card`). Marked `sorry`
pending the Mathlib citation.
-/
import Lutar.Axioms
import Lutar.Invariant

namespace Lutar

open NNReal

/-- Λ never exceeds the max axis (Axiom A4 realised). -/
theorem Λ_le_max {k : ℕ} (hk : 0 < k) (x : Axes k) :
    Λ k x ≤ Finset.univ.sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ x := by
  sorry

/-- Λ is at least the min axis. -/
theorem min_le_Λ {k : ℕ} (hk : 0 < k) (x : Axes k) :
    Finset.univ.inf' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ x ≤ Λ k x := by
  sorry

end Lutar
