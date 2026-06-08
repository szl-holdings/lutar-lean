/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 21 — CUT-1 FINAL: closing the (B-residual) via the light monotone-extension route

## Mission
Wave19/Wave20 reduced the BKS Lemma 6 Step-2 density lemma (`dyadic_image_dense`) to two
documented residuals. The heavier-looking one was **(B-residual)** = "the closure of the dyadic
image contains a nonempty PERFECT set of two-sided accumulation points". The research team
established that the parent paper arXiv:2107.07391 Theorem 8 obtains uncountability by the much
LIGHTER route — **monotone extension ⇒ injectivity ⇒ continuum image** — with NO perfect-set /
Cantor–Bendixson machinery. This file closes (B-residual) along that light route, fully
kernel-clean:

1. `countable_rightGap` / `countable_leftGap` — for ANY `H ⊆ ℝ`, the points of `H` that have an
   empty one-sided punctured gap inject into `ℚ`, hence are countable. (This is the BKS "at most
   countably many isolated / one-sided points" fact, made precise: a rational chosen in each gap
   is an injection because two distinct gap-points would force one to lie in the other's gap.)
2. `leftOrRight_of_not_twoSided` — a point of `H` that is NOT a two-sided accumulation point is a
   left-gap or right-gap point.
3. `twoSidedInH_not_countable` — therefore, if `H` is uncountable, the two-sided accumulation
   points of `H` lying in `H` are uncountable (`H` = two-sided ∪ left-gap ∪ right-gap, the last
   two countable).
4. `accSet_not_countable_of_uncountable` — the exact `(B)` hypothesis Wave19's `dyadic_image_dense`
   consumes: if `H` is uncountable and `accSet` contains the two-sided points of `H` in `H`, then
   `accSet` is uncountable.
5. `range_not_countable_of_strictMono` — and the source of uncountability for the BKS generator:
   a STRICTLY monotone `g : ℝ → ℝ` has uncountable range (it injects the continuum `Ioo 0 1`,
   `Cardinal.mk_Ioo_real`). This is the parent-paper "monotone extension ⇒ injective ⇒ image
   uncountable" step, with no perfect sets.

No proof placeholders, NO new axiom. `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.

## Sources
* Burai, Kiss, Szokol (2021), *Characterization of quasi-arithmetic means without regularity
  condition*, arXiv:2107.07391 — Theorem 8, First+Second step (the light uncountability route).
  https://arxiv.org/abs/2107.07391
* Burai, Kiss, Szokol (2022), arXiv:2208.07083 — Lemma 6, bullet 2.  https://arxiv.org/abs/2208.07083
* Mathlib v4.18.0: `Cardinal.mk_Ioo_real`, `aleph0_lt_continuum`, `Cardinal.mk_image_eq_of_injOn`,
  `StrictMono.injective`, `Function.Injective.countable`, `exists_rat_btwn`.
-/
import Lutar.Wave19.Density
import Mathlib.Data.Real.Cardinality
import Mathlib.Data.Rat.Encodable

open Set Function Cardinal

namespace Lutar.Wave21

/-- A **right-gap point** of `H`: a point `α ∈ H` with an empty right punctured neighbourhood,
i.e. some `Ioo α (α+ε)` is disjoint from `H`. In BKS terms, an isolated-on-the-right point. -/
def RightGapPt (H : Set ℝ) (α : ℝ) : Prop :=
  α ∈ H ∧ ∃ ε : ℝ, 0 < ε ∧ Disjoint (Ioo α (α + ε)) H

/-- A **left-gap point** of `H`: a point `α ∈ H` with an empty left punctured neighbourhood,
i.e. some `Ioo (α-ε) α` is disjoint from `H`. -/
def LeftGapPt (H : Set ℝ) (α : ℝ) : Prop :=
  α ∈ H ∧ ∃ ε : ℝ, 0 < ε ∧ Disjoint (Ioo (α - ε) α) H

/-- **The right-gap points of any `H ⊆ ℝ` are countable.** Pick a rational `qₐ ∈ Ioo α (α+εₐ)`
in each right gap; the map `α ↦ qₐ` is injective, because if `α < β` shared a rational `q`, then
`β ∈ H` would lie in `Ioo α (α+εₐ)` (as `α < β < q < α+εₐ`), contradicting disjointness from `H`.
An injection into the countable `ℚ` makes the set countable. (BKS: at most countably many points
isolated on the right.) -/
theorem countable_rightGap (H : Set ℝ) : {α | RightGapPt H α}.Countable := by
  rw [← Set.countable_coe_iff]
  choose ε hε hdisj using fun (p : {α // RightGapPt H α}) => p.2.2
  choose q hq1 hq2 using fun (p : {α // RightGapPt H α}) =>
    exists_rat_btwn (show (p.1 : ℝ) < p.1 + ε p by linarith [hε p])
  have hinj : Injective q := by
    intro a b hab
    rcases lt_trichotomy a.1 b.1 with hlt | heq | hgt
    · exfalso
      have hb_in : (b.1 : ℝ) ∈ Ioo a.1 (a.1 + ε a) := by
        refine ⟨hlt, ?_⟩
        have : (q b : ℝ) < a.1 + ε a := by rw [← hab]; exact hq2 a
        exact lt_trans (hq1 b) this
      exact (Set.disjoint_left.1 (hdisj a)) hb_in b.2.1
    · exact Subtype.ext heq
    · exfalso
      have ha_in : (a.1 : ℝ) ∈ Ioo b.1 (b.1 + ε b) := by
        refine ⟨hgt, ?_⟩
        have : (q a : ℝ) < b.1 + ε b := by rw [hab]; exact hq2 b
        exact lt_trans (hq1 a) this
      exact (Set.disjoint_left.1 (hdisj b)) ha_in a.2.1
  exact hinj.countable

/-- **The left-gap points of any `H ⊆ ℝ` are countable** — the mirror of `countable_rightGap`.
(BKS: at most countably many points isolated on the left.) -/
theorem countable_leftGap (H : Set ℝ) : {α | LeftGapPt H α}.Countable := by
  rw [← Set.countable_coe_iff]
  choose ε hε hdisj using fun (p : {α // LeftGapPt H α}) => p.2.2
  choose q hq1 hq2 using fun (p : {α // LeftGapPt H α}) =>
    exists_rat_btwn (show (p.1 : ℝ) - ε p < p.1 by linarith [hε p])
  have hinj : Injective q := by
    intro a b hab
    rcases lt_trichotomy a.1 b.1 with hlt | heq | hgt
    · exfalso
      have ha_in : (a.1 : ℝ) ∈ Ioo (b.1 - ε b) b.1 := by
        refine ⟨?_, hlt⟩
        have h1 : (b.1 : ℝ) - ε b < q b := hq1 b
        have h2 : (q a : ℝ) < a.1 := hq2 a
        rw [hab] at h2
        exact lt_trans h1 h2
      exact (Set.disjoint_left.1 (hdisj b)) ha_in a.2.1
    · exact Subtype.ext heq
    · exfalso
      have hb_in : (b.1 : ℝ) ∈ Ioo (a.1 - ε a) a.1 := by
        refine ⟨?_, hgt⟩
        have h1 : (a.1 : ℝ) - ε a < q a := hq1 a
        have h2 : (q b : ℝ) < b.1 := hq2 b
        rw [← hab] at h2
        exact lt_trans h1 h2
      exact (Set.disjoint_left.1 (hdisj a)) hb_in b.2.1
  exact hinj.countable

/-- **A non-two-sided point of `H` is a left- or right-gap point.** If `α ∈ H` fails the
`IsTwoSidedAccPt` predicate, some `ε > 0` makes one of the punctured half-intervals miss `H`. -/
theorem leftOrRight_of_not_twoSided {H : Set ℝ} {α : ℝ} (hα : α ∈ H)
    (h : ¬ Lutar.Wave19.IsTwoSidedAccPt H α) : LeftGapPt H α ∨ RightGapPt H α := by
  unfold Lutar.Wave19.IsTwoSidedAccPt at h
  push_neg at h
  obtain ⟨ε, hε, hcase⟩ := h
  by_cases hL : (Ioo (α - ε) α ∩ H).Nonempty
  · right
    refine ⟨hα, ε, hε, ?_⟩
    rw [Set.disjoint_iff_inter_eq_empty]
    exact hcase hL
  · left
    refine ⟨hα, ε, hε, ?_⟩
    rw [Set.disjoint_iff_inter_eq_empty]
    exact Set.not_nonempty_iff_eq_empty.1 hL

/-- **(B-residual) CLOSED — light route.** If `H ⊆ ℝ` is **uncountable**, then the set of two-sided
accumulation points of `H` that lie in `H` is uncountable. Proof: `H` is covered by these
two-sided points together with the left- and right-gap points, the latter two countable
(`countable_leftGap`, `countable_rightGap`); an uncountable set cannot be a union of two countable
sets and a countable set, so the two-sided part is uncountable. This is BKS bullet 2 with NO
perfect-set machinery — exactly the parent-paper Theorem 8 second step. -/
theorem twoSidedInH_not_countable {H : Set ℝ} (hH : ¬ H.Countable) :
    ¬ {α | α ∈ H ∧ Lutar.Wave19.IsTwoSidedAccPt H α}.Countable := by
  intro hc
  apply hH
  have hcover : H ⊆
      {α | α ∈ H ∧ Lutar.Wave19.IsTwoSidedAccPt H α} ∪ {α | LeftGapPt H α} ∪ {α | RightGapPt H α} := by
    intro α hα
    by_cases ht : Lutar.Wave19.IsTwoSidedAccPt H α
    · exact Or.inl (Or.inl ⟨hα, ht⟩)
    · rcases leftOrRight_of_not_twoSided hα ht with hl | hr
      · exact Or.inl (Or.inr hl)
      · exact Or.inr hr
  exact ((hc.union (countable_leftGap H)).union (countable_rightGap H)).mono hcover

/-- **The `(B)` hypothesis of `dyadic_image_dense`, discharged from uncountability of `H`.**
If `H` is uncountable and `accSet` contains every two-sided accumulation point of `H` lying in `H`
(true of the genuine two-sided accumulation set), then `accSet` is uncountable. -/
theorem accSet_not_countable_of_uncountable {H accSet : Set ℝ} (hH : ¬ H.Countable)
    (hsub : {α | α ∈ H ∧ Lutar.Wave19.IsTwoSidedAccPt H α} ⊆ accSet) : ¬ accSet.Countable :=
  fun hc => twoSidedInH_not_countable hH (hc.mono hsub)

/-- **The source of uncountability — monotone extension ⇒ uncountable image.** A **strictly
monotone** `g : ℝ → ℝ` has uncountable range: it is injective (`StrictMono.injective`), so its
restriction to the continuum interval `Ioo 0 1` has image of cardinality `𝔠`
(`Cardinal.mk_image_eq_of_injOn` + `Cardinal.mk_Ioo_real`), which cannot be countable
(`aleph0_lt_continuum`). This is the parent-paper Theorem 8 First step: the strictly-increasing
`[0,1]`-extension of the dyadic generator forces `closure (f(D))` to be uncountable, with NO
Cantor / perfect-set construction. -/
theorem range_not_countable_of_strictMono {g : ℝ → ℝ} (hg : StrictMono g) :
    ¬ (Set.range g).Countable := by
  intro hc
  have hsub : g '' (Ioo (0:ℝ) 1) ⊆ Set.range g := Set.image_subset_range g _
  have hcimg : (g '' (Ioo (0:ℝ) 1)).Countable := hc.mono hsub
  have hinj : Set.InjOn g (Ioo (0:ℝ) 1) := hg.injective.injOn
  have hcard : #(g '' (Ioo (0:ℝ) 1)) = #(Ioo (0:ℝ) 1) :=
    Cardinal.mk_image_eq_of_injOn g _ hinj
  rw [Cardinal.mk_Ioo_real (by norm_num : (0:ℝ) < 1)] at hcard
  rw [← Set.countable_coe_iff, ← Cardinal.mk_le_aleph0_iff, hcard] at hcimg
  exact absurd hcimg (not_le.2 aleph0_lt_continuum)

end Lutar.Wave21
