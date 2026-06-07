/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave10/NonInterferenceComposition.lean — IF-3: Non-interference is closed under composition

The a11oy governed-AI loop is a *pipeline* of stages (retrieval → tool-call →
gate → emit). Wave9 (`RobustDeclass`) proved a single stage non-interfering: an
attacker's high-sensitivity input cannot influence the low-visibility output. The
operationally crucial follow-on — the one a multi-stage decision substrate needs
— is that **non-interference composes**: if each stage is non-interfering, the
sequential composition of the whole pipeline is non-interfering. We prove it for
sequential composition, parallel (independent) composition, and arbitrary finite
chains (`List` of stages), Goguen–Meseguer style.

Non-interference is modeled as the standard *low-equivalence-preservation*
property: a step `f` is non-interfering iff inputs that agree on the low
(observable) projection produce outputs that agree on the low projection
(`low x = low y → low (f x) = low (f y)`).

## What is proven
- `NI low f` — `f` preserves low-equivalence (single-stage non-interference).
- `ni_id` — the identity stage is non-interfering.
- `ni_comp` — **sequential composition**: `NI low f → NI low g → NI low (g ∘ f)`.
- `ni_chain` — **arbitrary finite pipelines**: every stage non-interfering ⟹ the
  left-fold composition of a `List` of stages is non-interfering.
- `ni_pair` — **parallel/product composition**: two non-interfering stages on
  independent low-projections compose into a non-interfering product stage.

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave10`) — NOT in the LOCKED v11 baseline. Locked-proven
  stays exactly 5 {F1,F11,F12,F18,F19}. Λ untouched (Conjecture 1).
- Known-theorem formalization (Goguen–Meseguer 1982; compositional information-flow
  results, e.g. Mantel's MAKS framework). NO new declared axiom, NO sorry.
- Lean-core only: no Mathlib import.
- Scope: proves the COMPOSITIONALITY of the deterministic, transitive
  (input/output) non-interference property. It does NOT cover probabilistic or
  timing channels, nor intransitive declassification beyond the policy already
  modeled in Wave9 RobustDeclass; those remain ROADMAP.

## Citations
- Goguen & Meseguer, "Security Policies and Security Models", IEEE S&P 1982:
  https://www.cs.purdue.edu/homes/ninghui/readings/AccessControl/goguen_meseguer_82.pdf
- Mantel, "On the Composition of Secure Systems", IEEE S&P 2002.
- McCullough, "Noninterference and the composability of security properties",
  IEEE S&P 1988.

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/

namespace Lutar.Wave10.NonInterferenceComposition

variable {State Obs : Type}

/-- **Non-interference of a stage** w.r.t. a low/observable projection
`low : State → Obs`: inputs agreeing on the observable part yield outputs agreeing
on the observable part. (Goguen–Meseguer input/output non-interference.) -/
def NI (low : State → Obs) (f : State → State) : Prop :=
  ∀ x y, low x = low y → low (f x) = low (f y)

/-- The identity stage is non-interfering. -/
theorem ni_id (low : State → Obs) : NI low (id) := by
  intro x y h; simpa using h

/-- **IF-3 (sequential composition).** If stage `f` and stage `g` are each
non-interfering w.r.t. `low`, then their sequential composition `g ∘ f` is
non-interfering. The whole pipeline inherits non-interference from its stages. -/
theorem ni_comp (low : State → Obs) {f g : State → State}
    (hf : NI low f) (hg : NI low g) : NI low (g ∘ f) := by
  intro x y h
  have h1 : low (f x) = low (f y) := hf x y h
  simpa [Function.comp] using hg (f x) (f y) h1

/-- Accumulator lemma: folding non-interfering stages onto a non-interfering
accumulator preserves non-interference (general over the starting accumulator). -/
theorem ni_foldl (low : State → Obs) :
    ∀ (stages : List (State → State)) (acc : State → State),
      NI low acc → (∀ f ∈ stages, NI low f) →
      NI low (stages.foldl (fun a f => f ∘ a) acc)
  | [], acc, hacc, _ => by simpa using hacc
  | f :: rest, acc, hacc, hall => by
      have hf : NI low f := hall f (by simp)
      have hrest : ∀ g ∈ rest, NI low g := fun g hg => hall g (by simp [hg])
      have hstep : NI low (f ∘ acc) := ni_comp low hacc hf
      simpa [List.foldl] using ni_foldl low rest (f ∘ acc) hstep hrest

/-- **IF-3 (finite pipeline).** A pipeline given as a `List` of stages, executed by
left-to-right composition, is non-interfering provided every stage is. Immediate
from `ni_foldl` with the identity accumulator. -/
theorem ni_chain (low : State → Obs) (stages : List (State → State))
    (hall : ∀ f ∈ stages, NI low f) :
    NI low (stages.foldl (fun acc f => f ∘ acc) id) :=
  ni_foldl low stages id (ni_id low) hall

/-- **IF-3 (parallel/product composition).** Two stages acting on a product state,
each non-interfering w.r.t. its own low-projection, compose into a
non-interfering product stage w.r.t. the product projection. Independent governed
sub-decisions remain jointly non-interfering. -/
theorem ni_pair {S₁ S₂ O₁ O₂ : Type}
    (low₁ : S₁ → O₁) (low₂ : S₂ → O₂)
    {f₁ : S₁ → S₁} {f₂ : S₂ → S₂}
    (h1 : NI low₁ f₁) (h2 : NI low₂ f₂) :
    NI (fun p : S₁ × S₂ => (low₁ p.1, low₂ p.2))
       (fun p => (f₁ p.1, f₂ p.2)) := by
  intro x y h
  have hx1 : low₁ x.1 = low₁ y.1 := (Prod.mk.injEq _ _ _ _).mp h |>.1
  have hx2 : low₂ x.2 = low₂ y.2 := (Prod.mk.injEq _ _ _ _).mp h |>.2
  simp only [Prod.mk.injEq]
  exact ⟨h1 x.1 y.1 hx1, h2 x.2 y.2 hx2⟩

#print axioms ni_id
#print axioms ni_comp
#print axioms ni_foldl
#print axioms ni_chain
#print axioms ni_pair

end Lutar.Wave10.NonInterferenceComposition
