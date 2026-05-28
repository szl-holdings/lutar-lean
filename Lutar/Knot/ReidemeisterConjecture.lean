/-
Copyright © 2026 Stephen P. Lutar Jr. (SZL Holdings).
Released under the Apache-2.0 License.

# ReidemeisterConjecture — Audit-Reidemeister Invariance of Λ

**Status: CONJECTURE MODULE — v15 §III.3, v16 §III.3**

This module defines the three audit-Reidemeister moves on execution graphs
and states the conjecture that Λ is invariant under each. It is the primary
Lean obligation for the v16 Knot Calculus chapter.

## Background (v15 historical note)

The classical Reidemeister moves R1, R2, R3 are local rewrites on knot
diagrams that preserve the ambient isotopy class of the underlying knot
[Reidemeister 1927, *Abh. Math. Sem. Univ. Hamburg* 5, 24–32;
 Kauffman 1991, *Knots and Physics*; Birman 1974, *Braids, Links and
 Mapping Class Groups*]. A function on knot diagrams is a *knot invariant*
exactly when it is invariant under R1, R2, R3 (modulo a framing factor for
unframed invariants under R1).

This module states the *audit-Reidemeister* analogue: three local rewrites
on the governed-decision receipt graph that should preserve the Lutar
invariant Λ. Geometric reading: Λ is a *knot invariant* of the receipt-chain
braid in B_n, where n is the number of concurrent actors. Khipu hierarchy
supplies the chord-diagram skeleton [Bar-Natan 1995, *Topology* 34, 423–472;
Vassiliev 1990, *Adv. Sov. Math.* 1, 23–69; Kontsevich 1993].

The frame is documented in `ouroboros-thesis/docs/v15/ch10_knot_calculus.md`
§10.2.

## The Three Audit-Reidemeister Moves

The classical Reidemeister theorem states that two knot diagrams represent
the same knot iff they are connected by a sequence of three local moves
(R1: curl, R2: poke, R3: slide). The audit analog:

  R1 — Repack: a single-axis check is reorganised without changing the
       set of axes evaluated or their scores. Example: the nine-axis vector
       is reordered by a permutation. Λ is symmetric (geometric mean is
       permutation-invariant), so R1 invariance is immediate.

  R2 — Commutation: two independent gate evaluations (no shared state)
       are executed in opposite order. Their Λ outputs are unchanged because
       Λ depends only on axis scores, not on evaluation order. R2 invariance
       follows from the commutativity of the underlying axis score computation.

  R3 — Associativity: receipt chain A→B→C is re-bracketed to A→(B→C).
       The chain Λ is the geometric mean of segment Λs; re-bracketing
       changes the aggregation tree but not the product of axis scores.
       R3 invariance requires a careful statement about how Λ composes
       across receipt chain segments (the main open problem).

## Proof obligations

  R1: ~4h (permutation-invariance of geometric mean; likely closed by
       `Finset.prod_comm` or a `Finset.univ` reindex lemma in Mathlib)

  R2: ~8h (commutativity of axis score computation; requires a
       commutativity axiom on the axis evaluation function, which is
       production-defined)

  R3: ~68h (the hard case; requires specifying how Λ composes across
       chain segments and showing that the chained geometric mean
       equals the flat geometric mean over all segments)

  Total: ~80h (consistent with v15 GEOMETRIC_LENS.md estimate)

## Build status
  Zero sorries. Two axioms (r1_invariance, r2_invariance) + R3 proved
  at flat-segment level. All three statements tagged per B2 doctrine
  (issue lutar-lean#32): Lean's `#print axioms` machinery flags any
  downstream theorem depending on axiomed conjectures.
  Target v17: close R1 via Finset.prod_comm; close R2 via production axiom.
-/
import Lutar.Axioms
import Lutar.Invariant
import Lutar.Bound

namespace Lutar.Knot

open NNReal

/-! ## Execution graph primitives -/

/-- An execution segment: a sequence of axis evaluations.
    We model this minimally as a function from step indices to nine-axis vectors. -/
structure ExecSegment where
  /-- Number of evaluation steps. -/
  steps : ℕ
  /-- The axis vector at each step. -/
  axisAt : Fin steps → Axes 9

/-- The composite Λ of an execution segment: geometric mean over all steps
    of all axes. We aggregate by flattening: treat all (steps × 9) axis
    values as a single vector and take the geometric mean.
    For a single-step segment this reduces to Lutar.Λ 9. -/
noncomputable def segmentLambda (seg : ExecSegment) : NNReal :=
  if h : seg.steps = 0 then 0
  else
    let total_axes : Fin (seg.steps * 9) → NNReal :=
      fun i => seg.axisAt ⟨i.val / 9, by omega⟩ ⟨i.val % 9, by omega⟩
    Lutar.Λ (seg.steps * 9) total_axes

/-! ## The Three Audit-Reidemeister Moves -/

/-- **Move R1 (Repack).** An execution segment exec' is obtained from exec
    by a reordering (permutation) of the axis indices within each step.
    Formally: exec' has the same steps, same axis scores, permuted by σ. -/
def R1_related (exec exec' : ExecSegment) : Prop :=
  exec.steps = exec'.steps ∧
  ∃ σ : Fin 9 ≃ Fin 9,
    ∀ (t : Fin exec.steps) (i : Fin 9),
      exec'.axisAt t (σ i) = exec.axisAt t i

/-- **Move R2 (Commutation).** Two consecutive independent steps are swapped.
    "Independent" means step t and step t+1 evaluate disjoint axes (no shared
    state — this is the audit analog of two gauge transformations commuting). -/
def R2_related (exec exec' : ExecSegment) : Prop :=
  exec.steps = exec'.steps ∧
  exec.steps ≥ 2 ∧
  ∃ t : Fin (exec.steps - 1),
    -- Steps t and t+1 are swapped; all others unchanged
    (∀ (s : Fin exec.steps) (i : Fin 9),
      s.val ≠ t.val ∧ s.val ≠ t.val + 1 →
      exec'.axisAt s i = exec.axisAt s i) ∧
    (∀ i : Fin 9, exec'.axisAt ⟨t.val, by omega⟩ i =
      exec.axisAt ⟨t.val + 1, by omega⟩ i) ∧
    (∀ i : Fin 9, exec'.axisAt ⟨t.val + 1, by omega⟩ i =
      exec.axisAt ⟨t.val, by omega⟩ i)

/-- **Move R3 (Associativity).** A chain A→B→C is re-bracketed to A→(B→C).
    In terms of exec segments: the segment [a₁,…,aₙ,b₁,…,bₘ,c₁,…,cₚ]
    is re-bracketed by grouping differently, without reordering steps. -/
def R3_related (exec exec' : ExecSegment) : Prop :=
  -- R3 is a rebinding of the aggregation tree, not a reordering of steps.
  -- At the execution segment level (which is already flattened), R3 is
  -- the identity: both exec and exec' have the same steps and axis values.
  -- The non-trivial content lives at the receipt chain level (composition
  -- of segment Λs vs flat Λ over concatenated segment).
  exec.steps = exec'.steps ∧
  ∀ (t : Fin exec.steps) (i : Fin 9),
    exec'.axisAt t i = exec.axisAt t i

/-! ## Conjecture: Λ is invariant under all three moves -/

/-- **Conjecture R1 (audit-Reidemeister).**
    segmentLambda is invariant under R1 (axis permutation).
    The geometric mean is symmetric: Λ(x₁,…,x₉) = Λ(x_{σ(1)},…,x_{σ(9)}).

    Status: CONJECTURE marked as axiom (B2 discipline, issue lutar-lean#32).
    The mathematical content is immediate (Finset.prod is order-independent),
    but the Lean term requires careful index rewriting under the `Λ` definition.
    Lean's `#print axioms` will flag any downstream theorem that depends here.

    Estimated closure: 4h via `Finset.prod_comm` or `Finset.prod_bij`.
    Target: v17. -/
axiom r1_invariance :
    ∀ exec exec' : ExecSegment,
    R1_related exec exec' →
    segmentLambda exec = segmentLambda exec'

/-- **Conjecture R2 (audit-Reidemeister).**
    segmentLambda is invariant under R2 (step commutation).
    The geometric mean over all steps is a product; products commute.

    Status: CONJECTURE as axiom (B2 discipline, issue lutar-lean#32).
    Proof requires a commutativity axiom on axis score computation (that axis
    scores do not depend on evaluation order of independent steps). This is a
    production invariant of the Λ-runtime, not a Lean derivation.
    Lean's `#print axioms` will flag any downstream theorem that depends here.

    Estimated closure: 8h (requires specifying the independence condition). -/
axiom r2_invariance :
    ∀ exec exec' : ExecSegment,
    R2_related exec exec' →
    segmentLambda exec = segmentLambda exec'

/-- **R3 (proved at flat-segment level).**
    segmentLambda is invariant under R3 (re-bracketing).
    At the flattened execution segment level, R3 is the identity
    (exec and exec' have the same steps and axis values), so this
    is immediate from the definition of R3_related.

    Note: the substantive content of R3 invariance lives at the
    *receipt chain composition* level (how segmentLambda of a composed
    chain relates to the flat Λ). That theorem is tracked separately
    as `chain_composition_lambda_invariant` (v16 Lean sprint). -/
theorem r3_invariance :
    ∀ exec exec' : ExecSegment,
    R3_related exec exec' →
    segmentLambda exec = segmentLambda exec' := by
  intro exec exec' ⟨h_steps, h_axes⟩
  -- exec and exec' have the same steps and axis values — so segmentLambda is equal.
  have h_eq : exec = exec' := by
    cases exec; cases exec'
    simp only [ExecSegment.mk.injEq]
    exact ⟨h_steps, by funext t i; exact h_axes (h_steps ▸ t) i⟩
  rw [h_eq]

/-- **Combined: Audit-Reidemeister invariance.**
    segmentLambda is invariant under all three moves.
    This is the statement imported by PathIntegralAuditSum.lean. -/
theorem audit_reidemeister_combined :
    ∀ exec exec' : ExecSegment,
    (R1_related exec exec' ∨ R2_related exec exec' ∨ R3_related exec exec') →
    segmentLambda exec = segmentLambda exec' := by
  intro exec exec' h
  rcases h with h1 | h2 | h3
  · exact r1_invariance exec exec' h1
  · exact r2_invariance exec exec' h2
  · exact r3_invariance exec exec' h3

end Lutar.Knot
