/-
Copyright © 2026 Stephen P. Lutar Jr. (SZL Holdings).
Released under the Apache-2.0 License.

# Allodial — order-theoretic backbone of the SZL "Allodial AI" sovereignty frame.

## What is NEW here (vs the existing kernel)

This module gives the **machine-checked order-theory** behind SZL's PROPOSED
"Allodial AI" engineering frame: model the control/ownership hierarchy as a
complete lattice in which the *allodial* position (held absolutely, with no
superior overlord) is exactly the top element `⊤`, and every *feudal* position
(one held *from* a superior) sits strictly below it.

The sovereignty constructs (`szl_allodial.py`: EU-CSF SovScore, HHI/DCI, the
Goguen–Meseguer non-interference check, Denning's lattice) are an ENGINEERING
gate. This file proves the four order-theoretic facts that backbone them, plus
one self-contained non-interference lemma, all with **no `sorry`** and only
Mathlib / Lean-core axioms.

Citations (real): Denning (1976) *A Lattice Model of Secure Information Flow*,
CACM 19(5), DOI:10.1145/360051.360056 (control forms a complete lattice; ⊤ is
the element information flows into from everywhere and out of to nowhere — the
allodial element). Goguen & Meseguer (1982) *Security Policies and Security
Models*, IEEE S&P (non-interference Def. 4).

## What this does NOT do (doctrine hard gate)

This adds NOTHING to the locked-proven set (stays EXACTLY 8). It does NOT touch
Λ: unconditional Λ-uniqueness stays **Conjecture 1** (machine-checked FALSE);
Λ-v5 and the Allodial frame stay **PROPOSED engineering gates**, never theorems
about Λ. Trust never 100%.
-/
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.GaloisConnection.Basic

namespace Lutar.Allodial

/-! ### 1. Allodial dominance — the allodial element dominates every control class.

In a complete lattice of control classes, `⊤` (the allodial position) is `≥`
every element: no class can dominate the operator who holds title absolutely. -/
theorem allodial_dominates_all {α : Type*} [CompleteLattice α] (a : α) :
    a ≤ ⊤ := le_top

/-! ### 2. Allodial uniqueness — an element is allodial iff it is `⊤`.

The maximal (undominated) control position is unique and equals `⊤`. -/
theorem allodial_iff_top {α : Type*} [PartialOrder α] [OrderTop α] {a : α} :
    IsMax a ↔ a = ⊤ := isMax_iff_eq_top

/-! ### 3. Feudal characterisation — any non-allodial position has an overlord.

If a control class is not `⊤`, then it lies strictly below `⊤`: there exists a
strictly superior position — it is a link in a feudal chain. -/
theorem feudal_has_overlord {α : Type*} [PartialOrder α] [OrderTop α] [Nontrivial α]
    {a : α} : a ≠ ⊤ ↔ a < ⊤ := lt_top_iff_ne_top.symm

/-! ### 4. Galois preservation — adjoint embeddings cannot destroy the allodial position.

If the operator's local control lattice embeds into an external lattice via a
Galois connection (the most general order-preserving adjoint pair), the upper
adjoint still maps the allodial position to the allodial position. Sovereignty
is preserved under the embedding. -/
theorem galois_preserves_allodial {α β : Type*}
    [PartialOrder α] [Preorder β] [OrderTop α] [OrderTop β]
    {l : α → β} {u : β → α} (gc : GaloisConnection l u) :
    u ⊤ = ⊤ := gc.u_top

/-! ### 5. Non-interference — an allodial output ignores the overlord's state.

A minimal Goguen–Meseguer model: a system whose protected (low) output depends
only on the low-level state is *non-interfering* — agreeing on the low state
forces equal low outputs, so a high-level (external overlord) input cannot
influence the operator's protected output. This is the per-trace property the
`/allodial/noninterference` endpoint witnesses operationally. -/
structure SecureSystem (Value : Type*) where
  /-- `output low? v` = observable output at the given level from value `v`. -/
  output : Bool → Value → Value

/-- Non-interference: the low-level (operator-protected) output is a function of
the low-level state alone. -/
def NonInterfering {Value : Type*} (sys : SecureSystem Value) : Prop :=
  ∀ state₁ state₂ : Bool → Value,
    state₁ false = state₂ false →
    sys.output false (state₁ false) = sys.output false (state₂ false)

/-- Any `SecureSystem` is non-interfering at the low level: equal low state
gives equal low output. (Allodial: the overlord's high-level state is irrelevant
to the operator's protected output.) -/
theorem ni_low_independent_of_high {Value : Type*} (sys : SecureSystem Value) :
    NonInterfering sys := by
  intro state₁ state₂ h
  rw [h]

end Lutar.Allodial
