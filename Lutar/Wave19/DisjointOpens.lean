/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 19 — CUT-1 density engine: countably-many-disjoint-opens

## Mission (CUT-1 density step, sub-lemma A + C)
This file packages the *real engine* of Burai–Kiss–Szokol (arXiv:2208.07083) Lemma 6, Step 2
(the density of the dyadic image): a separable / second-countable line carries only **countably
many** pairwise-disjoint nonempty open sets. Hence an **injection from an uncountable index set**
into a family of pairwise-disjoint nonempty open intervals of `ℝ` is **impossible**.

This is exactly the contradiction the BKS density argument needs:
> "the cardinality of disjoint intervals as well as the cardinality of two-sided accumulation
>  points is uncountable, which gives a contradiction."  (BKS 2208.07083, p.6, third bullet.)

Mathlib v4.18.0 *does* package the separable-space half
(`Pairwise.countable_of_isOpen_disjoint`); what was missing — and what we add here — is the
keyed-to-this-construction wrapper turning it into the "uncountable index ⇒ `False`" engine that
the gap-to-disjoint-intervals map of BKS Step 2 consumes.

NO placeholder tactic, NO new axiom. `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.

## Sources
* Burai, Kiss, Szokol (2022), *A dichotomy result for strictly increasing bisymmetric maps*,
  arXiv:2208.07083 — https://arxiv.org/abs/2208.07083 — Lemma 6, Step 2 (density).
* Mathlib `Pairwise.countable_of_isOpen_disjoint` (separable space ⇒ countably many disjoint opens).
-/
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Bases
import Mathlib.Data.Real.Cardinality
import Mathlib.Data.Set.Pairwise.Basic

open Set Function

namespace Lutar.Wave19

/-- **Sub-lemma A (brief signature).** In a separable space, an *injective* family `U : ι → Set α`
of pairwise-disjoint nonempty open sets has a **countable** index type `ι`.

This is the brief's `countable_of_pairwiseDisjoint_open`, stated for a general separable space
(`ℝ` is such). It is a thin re-export of Mathlib's `Pairwise.countable_of_isOpen_disjoint`; the
`Injective U` hypothesis is recorded to match the brief even though the Mathlib primitive does not
need it. -/
theorem countable_of_pairwiseDisjoint_open {α : Type*} [TopologicalSpace α]
    [TopologicalSpace.SeparableSpace α] {ι : Type*} {U : ι → Set α}
    (hopen : ∀ i, IsOpen (U i)) (hne : ∀ i, (U i).Nonempty)
    (_hinj : Function.Injective U) (hdisj : Pairwise (Disjoint on U)) : Countable ι :=
  hdisj.countable_of_isOpen_disjoint hopen hne

/-- **Sub-lemma C (the contradiction engine).** If the index type `ι` is **`Uncountable`** but `U`
is a family of pairwise-disjoint nonempty open sets in a separable space, we reach `False`.

This is the precise BKS Step-2 contradiction: an uncountable supply of pairwise-disjoint nonempty
open intervals cannot live on a separable line. -/
theorem false_of_uncountable_pairwiseDisjoint_open {α : Type*} [TopologicalSpace α]
    [TopologicalSpace.SeparableSpace α] {ι : Type*} [Uncountable ι] {U : ι → Set α}
    (hopen : ∀ i, IsOpen (U i)) (hne : ∀ i, (U i).Nonempty)
    (hdisj : Pairwise (Disjoint on U)) : False := by
  have hcount : Countable ι := hdisj.countable_of_isOpen_disjoint hopen hne
  exact (not_countable_iff.2 ‹Uncountable ι›) hcount

/-- **Sub-lemma C, set form.** Phrased over an *uncountable subset* `s : Set α` of indices, each
producing a nonempty disjoint open set `U i`. The set of indices then must be countable —
contradicting uncountability. Convenient when the index "set" is a subset of `ℝ` (e.g. the
two-sided accumulation points). -/
theorem not_uncountable_of_pairwiseDisjoint_open_on {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace.SeparableSpace α] {s : Set β} {U : β → Set α}
    (hopen : ∀ i ∈ s, IsOpen (U i)) (hne : ∀ i ∈ s, (U i).Nonempty)
    (hdisj : s.PairwiseDisjoint U) : s.Countable :=
  hdisj.countable_of_isOpen hopen hne

/-- **Sub-lemma C, explicit interval form for `ℝ`.** A family of open intervals `]L i, R i[`,
indexed by a set `s ⊆ ℝ`, that are pairwise disjoint and each nonempty (`L i < R i`), forces `s`
countable. This is the literal shape of the BKS map
`α ↦ ]F(X,α), F(Y,α)[` over two-sided accumulation points `α`. -/
theorem countable_of_pairwiseDisjoint_Ioo {β : Type*} {s : Set β} {L R : β → ℝ}
    (hlt : ∀ i ∈ s, L i < R i)
    (hdisj : s.PairwiseDisjoint fun i => Ioo (L i) (R i)) : s.Countable :=
  hdisj.countable_of_isOpen (fun _ _ => isOpen_Ioo) (fun i hi => nonempty_Ioo.2 (hlt i hi))

/-- The same, in `False`-producing form: an **uncountable** set `s ⊆ ℝ` cannot index a pairwise
-disjoint family of nonempty open intervals. This is what the density contradiction calls. -/
theorem false_of_uncountable_pairwiseDisjoint_Ioo {β : Type*} {s : Set β} {L R : β → ℝ}
    (hunc : ¬ s.Countable) (hlt : ∀ i ∈ s, L i < R i)
    (hdisj : s.PairwiseDisjoint fun i => Ioo (L i) (R i)) : False :=
  hunc (countable_of_pairwiseDisjoint_Ioo hlt hdisj)

end Lutar.Wave19
