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

namespace Lutar.Lambda.AggregatorLfp

open OrderHom

variable {α : Type*} [CompleteLattice α]

/-- The Kleene iterate chain of the aggregator `Φ` started from `⊥`:
    `iterate Φ n = Φ^[n] ⊥`. -/
def iterate (Φ : α →o α) (n : ℕ) : α := (Φ^[n]) ⊥

@[simp] theorem iterate_zero (Φ : α →o α) : iterate Φ 0 = ⊥ := rfl

theorem iterate_succ (Φ : α →o α) (n : ℕ) :
    iterate Φ (n + 1) = Φ (iterate Φ n) := by
  simp only [iterate, Function.iterate_succ', Function.comp_apply]

/-- **Monotone chain.** Each Kleene iterate dominates the previous one:
    `Φⁿ⊥ ≤ Φⁿ⁺¹⊥`.  The router's successive weight refinements never regress. -/
theorem iterate_mono (Φ : α →o α) : Monotone (iterate Φ) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero =>
      rw [iterate_zero, iterate_succ]
      exact bot_le
  | succ k ih =>
      rw [iterate_succ Φ (k + 1), iterate_succ Φ k]
      exact Φ.monotone (by rwa [iterate_succ Φ k] at ih)

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
  | zero => rw [iterate_zero]; exact bot_le
  | succ k ih =>
      rw [iterate_succ]
      calc Φ (iterate Φ k) ≤ Φ (lfp Φ) := Φ.monotone ih
        _ = lfp Φ := map_lfp Φ

/-- The supremum of the Kleene iterate chain is below the least fixed point
    (every iterate is, so their sup is). -/
theorem iSup_iterate_le_lfp (Φ : α →o α) : (⨆ n, iterate Φ n) ≤ lfp Φ :=
  iSup_le (iterate_le_lfp Φ)

/-- **Kleene chain dominated by lfp + post-fixed sup.** The supremum `S = ⨆ n, Φⁿ⊥`
    of the monotone Kleene iterate chain is a *post-fixed point below the lfp*:
    `Φ S ≤ S` is NOT asserted unconditionally (that needs ω-continuity, future work),
    but we DO prove kernel-clean that `S ≤ lfp Φ` and that `Φ` maps `S` above every
    iterate, i.e. `iterate Φ (n+1) ≤ Φ S`.  Together with `iterate_mono` this is the
    honest, fully-verified backbone of Kleene convergence; the exact equality
    `lfp Φ = S` under ω-Scott-continuity is stated as `lfp_eq_iSup_iterate_of_commute`
    (future work, depends on the Mathlib ωCPO continuity API) and is NOT claimed here. -/
theorem iterate_succ_le_map_iSup (Φ : α →o α) (n : ℕ) :
    iterate Φ (n + 1) ≤ Φ (⨆ m, iterate Φ m) := by
  rw [iterate_succ]
  exact Φ.monotone (le_iSup (iterate Φ) n)

/-- The exact Kleene equality `lfp Φ = ⨆ n, Φⁿ⊥` holds when `Φ` is ω-Scott-continuous.
    Stated as an explicit hypothesis-carrying PROPOSITION (Kleene fixpoint theorem);
    the `≤` direction is immediate from `iSup_iterate_le_lfp`, and the `≥` direction
    follows once `Φ (⨆ iterate) = ⨆ Φ(iterate)` is supplied. Marked future-work so no
    fragile continuity-API name is asserted as proven. -/
theorem lfp_eq_iSup_iterate_of_commute (Φ : α →o α)
    (hcommute : Φ (⨆ n, iterate Φ n) = ⨆ n, Φ (iterate Φ n)) :
    lfp Φ = ⨆ n, iterate Φ n := by
  set S : α := ⨆ n, iterate Φ n with hS
  have hfix : Φ S = S := by
    apply le_antisymm
    · rw [hcommute]
      refine iSup_le (fun n => ?_)
      rw [← iterate_succ]
      exact le_iSup (iterate Φ) (n + 1)
    · refine iSup_le (fun n => ?_)
      cases n with
      | zero => rw [iterate_zero]; exact bot_le
      | succ k => exact iterate_succ_le_map_iSup Φ k
  exact le_antisymm (lfp_le Φ (le_of_eq hfix)) (iSup_iterate_le_lfp Φ)

/-- **Kleene fixpoint theorem (unconditional under ω-Scott-continuity).**
    When the aggregator `Φ` is ω-Scott-continuous (`OmegaCompletePartialOrder.ωScottContinuous`),
    its least fixed point EQUALS the supremum of the Kleene iterate chain
    `lfp Φ = ⨆ n, Φⁿ⊥`.  Unlike `lfp_eq_iSup_iterate_of_commute` (Wave25), this does NOT
    carry the `Φ (⨆ iterate) = ⨆ Φ(iterate)` commute hypothesis as an explicit assumption:
    the commute property is DERIVED automatically from ω-Scott-continuity.

    Mechanism: the Kleene iterate sequence `iterate Φ` is monotone (`iterate_mono`), so it is
    an `OmegaCompletePartialOrder.Chain α` (a monotone ℕ-indexed sequence).  For a
    `CompleteLattice` the ωCPO `ωSup` of a chain is definitionally `⨆ i, c i`, so
    `ωScottContinuous.map_ωSup` instantiated at that chain reads exactly
    `Φ (⨆ n, iterate Φ n) = ⨆ n, Φ (iterate Φ n)` — the Wave25 commute hypothesis.  We then
    discharge it through `lfp_eq_iSup_iterate_of_commute` (reusing the Wave25 antisymmetry
    argument).  This is the standard Kleene fixpoint theorem; it remains a CONVERGENCE result
    (the constructive computation of the lfp), NOT a uniqueness claim, and does NOT bear on
    Conjecture 1.  Kernel-clean: `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`. -/
theorem lfp_eq_iSup_iterate (Φ : α →o α)
    (hΦ : OmegaCompletePartialOrder.ωScottContinuous (Φ : α → α)) :
    lfp Φ = ⨆ n, iterate Φ n := by
  -- Package the monotone Kleene iterate sequence as an ωCPO `Chain`.
  let c : OmegaCompletePartialOrder.Chain α := ⟨iterate Φ, iterate_mono Φ⟩
  -- ω-Scott-continuity distributes Φ over the chain's ωSup.
  have hmap := hΦ.map_ωSup c
  -- For a `CompleteLattice` the ωCPO `ωSup` of a chain is definitionally `⨆ i, c i`,
  -- so `hmap` is exactly the Wave25 commute property after unfolding.
  have hcommute : Φ (⨆ n, iterate Φ n) = ⨆ n, Φ (iterate Φ n) := by
    have hL : (⨆ n, iterate Φ n) = OmegaCompletePartialOrder.ωSup c := rfl
    have hR : (⨆ n, Φ (iterate Φ n))
        = OmegaCompletePartialOrder.ωSup (c.map ⟨Φ, hΦ.monotone⟩) := rfl
    rw [hL, hR, hmap]
  -- Discharge through the Wave25 hypothesis-carrying Kleene theorem.
  exact lfp_eq_iSup_iterate_of_commute Φ hcommute

/-- **Λ-route stability certificate.** At the least fixed point of the Λ-aggregator,
    the routing weights are stable: applying one more aggregation step returns the
    same assignment.  This is the honest "the tier choice has converged" witness used
    by the PURIQ router — it is a CONVERGENCE statement, not a uniqueness claim, and
    does NOT bear on Conjecture 1. -/
theorem lambda_route_stable (Λ : α →o α) : Λ (lfp Λ) = lfp Λ := map_lfp Λ

end Lutar.Lambda.AggregatorLfp
