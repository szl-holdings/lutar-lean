/-
Copyright © 2026 Stephen P. Lutar Jr. (SZL Holdings).
Released under the Apache-2.0 License.

# AggregatorLfp — constructive Kleene iterate-supremum characterization of the
# Λ-aggregator least fixed point, and fixpoint-stability of the routing weights.
# (Wave25, NEW — staged PROPOSED; distinct from Round5/OuroborosKleeneHalt.)

## What is NEW here (vs the existing kernel)

`Lutar/Innovations/round5/OuroborosKleeneHalt.lean` already proves *existence* of a
least fixed point of a monotone operator on a complete lattice (Knaster–Tarski /
Kleene existence, via `OrderHom.lfp_eq` + `OrderHom.lfp_le`).

This module proves the **constructive** content that existence alone does not give:
  1. `lfp_eq_iSup_iterate` — when the Λ-aggregator `Φ` is ω-Scott-continuous, its least
     fixed point EQUALS the supremum of the Kleene iterate chain `⊥, Φ⊥, Φ²⊥, …`
     (the actual *computation* of the fixed point, not just its existence);
  2. `iterate_mono` — that chain is monotone (`Φⁿ⊥ ≤ Φⁿ⁺¹⊥`), so the router's
     successive weight refinements never regress;
  3. `lfp_is_fixed` / `lfp_least` — the limit is a fixed point and the least one, i.e.
     the closure-stable routing weights are the *minimal* self-consistent assignment;
  4. `lambda_route_stable` — instantiated for the Λ-aggregator: at the least fixed
     point the routing weights are stable under one more aggregation step (the honest
     "the tier choice has converged" certificate).

This is the convergence backbone for the PURIQ tier/budget router. It does NOT touch
Conjecture 1: Λ unconditional uniqueness stays Conjecture 1 (machine-checked FALSE),
locked-proven stays EXACTLY 8, and this file is EXPERIMENTAL-tier on green build only.

## Honest status
PROPOSED / Wave25 candidate.  Becomes a CI-green EXPERIMENTAL theorem only when
`lake build` passes with no `sorry` and Lean-core axioms only.  Never folded into
the locked 8.  Existence (Round5) is cited, NOT reclaimed.

## Citations
  - Kleene, S.C. (1938). J. Symbolic Logic 3(4), 150–155.  doi:10.2307/2267778
  - Tarski, A. (1955). "A lattice-theoretical fixpoint theorem." Pacific J. Math 5, 285.
  - Mathlib: `Mathlib.Order.FixedPoints` (`OrderHom.lfp`, `fixedPoints.lfp_eq_sSup_iterate`).
-/
import Mathlib.Order.FixedPoints
import Mathlib.Order.OmegaCompletePartialOrder

namespace Lutar.Lambda.AggregatorLfp

open OrderHom

variable {α : Type*} [CompleteLattice α]

/-- The Kleene iterate chain of the aggregator `Φ` started from `⊥`:
    `iterate Φ n = Φ^[n] ⊥`. -/
def iterate (Φ : α →o α) (n : ℕ) : α := (Φ^[n]) ⊥

@[simp] theorem iterate_zero (Φ : α →o α) : iterate Φ 0 = ⊥ := rfl

theorem iterate_succ (Φ : α →o α) (n : ℕ) :
    iterate Φ (n + 1) = Φ (iterate Φ n) := by
  unfold iterate
  rw [Function.iterate_succ']
  rfl

/-- **Monotone chain.** Each Kleene iterate dominates the previous one:
    `Φⁿ⊥ ≤ Φⁿ⁺¹⊥`.  The router's successive weight refinements never regress. -/
theorem iterate_mono (Φ : α →o α) : Monotone (iterate Φ) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => simp [iterate, iterate_succ]
  | succ k ih =>
      rw [iterate_succ Φ (k + 1), iterate_succ Φ k]
      exact Φ.monotone ih

/-- The least fixed point is itself a fixed point (existence side — cited to Round5,
    restated here only as a building block for the constructive results). -/
theorem lfp_is_fixed (Φ : α →o α) : Φ (lfp Φ) = lfp Φ := map_lfp Φ

/-- The least fixed point is below any other fixed point: it is the *minimal*
    self-consistent weight assignment. -/
theorem lfp_least (Φ : α →o α) {y : α} (hy : Φ y = y) : lfp Φ ≤ y :=
  lfp_le Φ hy.le

/-- Every Kleene iterate is below the least fixed point. -/
theorem iterate_le_lfp (Φ : α →o α) (n : ℕ) : iterate Φ n ≤ lfp Φ := by
  induction n with
  | zero => simp [iterate]
  | succ k ih =>
      rw [iterate_succ]
      calc Φ (iterate Φ k) ≤ Φ (lfp Φ) := Φ.monotone ih
        _ = lfp Φ := map_lfp Φ

/-- **Constructive Kleene characterization.** When `Φ` is ω-Scott-continuous, its
    least fixed point is exactly the supremum of the iterate chain:
        `lfp Φ = ⨆ n, Φⁿ ⊥`.
    This is the *computation* of the fixed point, not merely its existence. -/
theorem lfp_eq_iSup_iterate (Φ : α →o α)
    (hΦ : OmegaCompletePartialOrder.ωScottContinuous Φ) :
    lfp Φ = ⨆ n, iterate Φ n := by
  -- Mathlib provides the Kleene fixpoint theorem for ω-Scott-continuous maps.
  have h := fixedPoints.lfp_eq_sSup_iterate Φ hΦ
  -- rewrite the `sSup` over the iterate set as an `iSup` over ℕ
  simpa [iterate, Set.range, iSup] using h

/-- **Λ-route stability certificate.** At the least fixed point of the Λ-aggregator,
    the routing weights are stable: applying one more aggregation step returns the
    same assignment.  This is the honest "the tier choice has converged" witness used
    by the PURIQ router — it is a CONVERGENCE statement, not a uniqueness claim, and
    does NOT bear on Conjecture 1. -/
theorem lambda_route_stable (Λ : α →o α) : Λ (lfp Λ) = lfp Λ := map_lfp Λ

end Lutar.Lambda.AggregatorLfp
