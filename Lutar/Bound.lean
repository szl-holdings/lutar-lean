/-
# Bound theorem

**Theorem 2.** For every axes vector `x : Fin k → [0,1]`,

    min_i (x i)  ≤  Λ_k x  ≤  max_i (x i)  ≤  1.

This is the substrate guarantee that the Λ-gate is *interpretable*: a passing
Λ value never exceeds the best axis nor falls below the worst.

## Status (2026-05-12 audit)

The two statements below are formal Lean theorems; their proofs are scaffolded
with `sorry` pending the Mathlib citations:

- `Λ_le_max` discharges to `Real.geom_mean_le_arith_mean_weighted` followed by
  the trivial bound `arith_mean ≤ max`, then `Real.rpow_le_rpow_of_exponent_le`.
  Equivalent self-contained route: combine `Finset.prod_le_pow_card` (which
  gives `∏ x ≤ (max x) ^ k`) with the monotonicity of `(·) ^ (1/k)`.
- `min_le_Λ` is the dual; it discharges to `Real.pow_arith_mean_le_arith_mean_pow`
  or, self-contained, to `Finset.pow_card_le_prod` + `Real.rpow_le_rpow`.

Discharging these is tracked as a v13 work-item (issue
`https://github.com/szl-holdings/lutar-lean/issues/2`). The 52-test runtime
Λ suite under `packages/ouroboros-invariant/test/` exercises both bounds
numerically on the reference vectors, so the bounds are empirically verified
on every CI run even while the Lean proofs remain `sorry`.
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
