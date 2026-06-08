/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 20 — PRIMITIVE A: pairwise-disjoint nonempty open sets are countable

## Mission (the density "engine", standalone & reusable)
This file proves — as **independent, general, Mathlib-style primitives** — the fact that powers
Step 2 of Burai–Kiss–Szokol (arXiv:2208.07083) Lemma 6:

> A family of **pairwise-disjoint nonempty open** sets in a separable space (in particular `ℝ`, or
> any second-countable / separable order topology) is **countable**; equivalently, an *uncountable*
> index cannot inject into such a family.

Two complementary developments are given:

1. **Self-contained route over `ℝ`.** We do NOT merely re-export a Mathlib black box: we give the
   elementary rational-injection proof the brief asks for — each nonempty open set of `ℝ` contains
   a rational (`Rat.isDenseEmbedding_coe_real.dense.exists_mem_open`), pairwise-disjointness makes
   the choice `i ↦ qᵢ` injective, and `ℚ` is countable, so the index is countable. This is the
   "give Mathlib the theory" elementary proof; it depends on nothing but core Mathlib.

2. **General separable-space route.** We also package the statement for an arbitrary
   `SeparableSpace` via Mathlib's `Pairwise.countable_of_isOpen_disjoint`, plus the
   contrapositive / `False`-producing corollaries and the concrete `Set.Ioo` interval form that the
   BKS gap-to-disjoint-intervals map consumes.

Wave 19 owns the BKS-specific assembly; this Wave 20 file deliberately keeps the primitives
**construction-agnostic** so they are independently reusable (and independently mergeable to
Mathlib-style).  It imports only core Mathlib — NO Wave18/Wave19 dependency.

NO `sorry`, NO new axiom. `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.

## Sources
* Burai, Kiss, Szokol (2022), *A dichotomy result for strictly increasing bisymmetric maps*,
  arXiv:2208.07083 — https://arxiv.org/abs/2208.07083 — Lemma 6, Step 2 (density), p. 6, bullet 3:
  "the cardinality of disjoint intervals … is uncountable, which gives a contradiction."
* Mathlib `Pairwise.countable_of_isOpen_disjoint` (separable space ⇒ countably many disjoint opens),
  `PairwiseDisjoint.countable_of_isOpen`, `Rat.isDenseEmbedding_coe_real`, `DenseRange.exists_mem_open`.
-/
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Set.Pairwise.Basic

open Set Function

namespace Lutar.Wave20

/-! ## Part 1 — the self-contained rational-injection proof over `ℝ` -/

/-- **Each nonempty open subset of `ℝ` contains a rational.**  The atomic fact behind the
self-contained countability proof: `ℚ` (cast into `ℝ`) is dense, so it meets every nonempty open
set.  (`exists_rat_btwn` is the order-theoretic shadow of this.) -/
theorem exists_rat_mem_of_isOpen {U : Set ℝ} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ q : ℚ, (q : ℝ) ∈ U :=
  Rat.isDenseEmbedding_coe_real.dense.exists_mem_open hU hne

/-- **Primitive A (self-contained, `ℝ`).** A pairwise-disjoint, injective family `U : ι → Set ℝ`
of nonempty open sets has a **countable** index type `ι`.

Proof route (exactly the brief's): choose a rational `q i ∈ U i` for every `i` (Part 1); if
`q i = q j` then `(q i : ℝ)` lies in both `U i` and `U j`, so `U i ∩ U j ≠ ∅`, so by
pairwise-disjointness `i = j`.  Hence `i ↦ q i` is injective into the countable `ℚ`, so `ι` is
countable.  No appeal to the packaged Mathlib lemma — only `ℚ` countable + disjointness. -/
theorem countable_of_pairwiseDisjoint_isOpen_real {ι : Type*} {U : ι → Set ℝ}
    (hopen : ∀ i, IsOpen (U i)) (hne : ∀ i, (U i).Nonempty)
    (hdisj : Pairwise (Disjoint on U)) : Countable ι := by
  -- choose a rational witness in each `U i`
  choose q hq using fun i => exists_rat_mem_of_isOpen (hopen i) (hne i)
  -- the choice is injective: equal rationals force overlapping (hence equal) sets
  have hinjq : Function.Injective q := by
    intro i j hij
    by_contra hne'
    have hdij : Disjoint (U i) (U j) := hdisj hne'
    have hmem_i : (q i : ℝ) ∈ U i := hq i
    have hmem_j : (q i : ℝ) ∈ U j := by rw [hij]; exact hq j
    exact (hdij.ne_of_mem hmem_i hmem_j) rfl
  -- inject into countable ℚ
  exact hinjq.countable

/-- **Primitive A, `Function.onFun` spelling (self-contained, `ℝ`).** Identical content with the
brief's exact `Pairwise (Function.onFun Disjoint U)` hypothesis spelling and an explicit
`Function.Injective U` hypothesis (recorded to match the brief signature; not needed by the proof,
since disjointness already yields the injection). -/
theorem countable_of_pairwiseDisjoint_isOpen {ι : Type*} {U : ι → Set ℝ}
    (hopen : ∀ i, IsOpen (U i)) (hne : ∀ i, (U i).Nonempty)
    (hdisj : Pairwise (Function.onFun Disjoint U)) (_hinj : Function.Injective U) :
    Countable ι :=
  countable_of_pairwiseDisjoint_isOpen_real hopen hne hdisj

/-! ## Part 2 — the general separable-space packaging + corollaries -/

/-- **Primitive A (general separable space).** In any `SeparableSpace`, a pairwise-disjoint family
`U : ι → Set α` of nonempty open sets has a **countable** index type.  `ℝ` is separable, so this
recovers `countable_of_pairwiseDisjoint_isOpen_real`; stating it generally makes the primitive
reusable on any separable / second-countable carrier (the brief's "order topology" instances are
separable). -/
theorem countable_of_pairwiseDisjoint_isOpen_sep {α : Type*} [TopologicalSpace α]
    [TopologicalSpace.SeparableSpace α] {ι : Type*} {U : ι → Set α}
    (hopen : ∀ i, IsOpen (U i)) (hne : ∀ i, (U i).Nonempty)
    (hdisj : Pairwise (Disjoint on U)) : Countable ι :=
  hdisj.countable_of_isOpen_disjoint hopen hne

/-- **Contrapositive corollary (the contradiction engine).** If `ι` is `Uncountable`, then `U`
*cannot* be a pairwise-disjoint family of nonempty open sets in a separable space. This is the exact
shape consumed by the BKS Step-2 density contradiction. -/
theorem false_of_uncountable_pairwiseDisjoint_isOpen {α : Type*} [TopologicalSpace α]
    [TopologicalSpace.SeparableSpace α] {ι : Type*} [Uncountable ι] {U : ι → Set α}
    (hopen : ∀ i, IsOpen (U i)) (hne : ∀ i, (U i).Nonempty)
    (hdisj : Pairwise (Disjoint on U)) : False :=
  (not_countable_iff.2 ‹Uncountable ι›) (countable_of_pairwiseDisjoint_isOpen_sep hopen hne hdisj)

/-- **Set-indexed form.** For a subset `s ⊆ β` whose members each produce a nonempty open `U i`
that are pairwise disjoint over `s`, the index set `s` is countable. -/
theorem countable_of_pairwiseDisjoint_isOpen_on {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace.SeparableSpace α] {s : Set β} {U : β → Set α}
    (hopen : ∀ i ∈ s, IsOpen (U i)) (hne : ∀ i ∈ s, (U i).Nonempty)
    (hdisj : s.PairwiseDisjoint U) : s.Countable :=
  hdisj.countable_of_isOpen hopen hne

/-- **Concrete interval form for `ℝ` (what the BKS map literally produces).** A family of open
intervals `Ioo (L i) (R i)` indexed by `s ⊆ β`, pairwise disjoint and each nonempty (`L i < R i`),
forces `s` countable. This is the literal shape of `α ↦ ]F(X,α), F(Y,α)[`. -/
theorem countable_of_pairwiseDisjoint_Ioo {β : Type*} {s : Set β} {L R : β → ℝ}
    (hlt : ∀ i ∈ s, L i < R i)
    (hdisj : s.PairwiseDisjoint fun i => Ioo (L i) (R i)) : s.Countable :=
  hdisj.countable_of_isOpen (fun _ _ => isOpen_Ioo) (fun i hi => nonempty_Ioo.2 (hlt i hi))

/-- The interval form in `False`-producing shape: an **uncountable** `s ⊆ β` cannot index a
pairwise-disjoint family of nonempty open real intervals. -/
theorem false_of_uncountable_pairwiseDisjoint_Ioo {β : Type*} {s : Set β} {L R : β → ℝ}
    (hunc : ¬ s.Countable) (hlt : ∀ i ∈ s, L i < R i)
    (hdisj : s.PairwiseDisjoint fun i => Ioo (L i) (R i)) : False :=
  hunc (countable_of_pairwiseDisjoint_Ioo hlt hdisj)

end Lutar.Wave20
