/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 19 — CUT-1 density: `dyadic_image_dense` (BKS 2208.07083 Lemma 6, Step 2)

## Mission
Assemble the Burai–Kiss–Szokol density argument from the Wave19 disjoint-opens engine. The BKS
Step-2 contradiction is:

> If the dyadic image `H = f(D)` is NOT dense in `[u,v]`, there is a gap `]X,Y[` with
> `]X,Y[ ∩ H = ∅`. Then for any two **distinct two-sided accumulation points** `s ≠ t` of
> `closure H`, the open intervals `]F(X,s), F(Y,s)[` and `]F(X,t), F(Y,t)[` are **disjoint**.
> Since accumulation points are **uncountable**, this gives uncountably many pairwise-disjoint
> nonempty open intervals on the separable line `ℝ` — a contradiction. Hence `H` is dense.

We formalize this in three honest layers:

* `IsTwoSidedAccPt` — the BKS footnote-2 predicate.
* `density_of_gap_contradiction` — the **fully kernel-clean assembly**: a gap together with an
  uncountable family of pairwise-disjoint nonempty open intervals (the BKS map applied to
  accumulation points) is impossible, hence density. This is the real reduction, discharged via the
  Wave19 engine `false_of_uncountable_pairwiseDisjoint_Ioo`.
* `dyadic_image_dense` — the named lemma, in BKS shape, proved **from the two explicitly-named BKS
  inputs**: (B) uncountability of the two-sided accumulation points, and (C-ordering) the BKS
  disjointness of the image intervals. Both are recorded as hypotheses with their BKS provenance;
  see the report for the honest status of (B).

NO `sorry`, NO new axiom. `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.

## Sources
* Burai, Kiss, Szokol (2022), *A dichotomy result for strictly increasing bisymmetric maps*,
  arXiv:2208.07083 — https://arxiv.org/abs/2208.07083 — Lemma 6, Step 2 (the three bullets).
-/
import Lutar.Wave19.DisjointOpens
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Cardinality

open Set Function

namespace Lutar.Wave19

/-- **Two-sided accumulation point** (BKS 2208.07083, footnote 2). `α` is a two-sided accumulation
point of `H ⊆ ℝ` if every right and left neighbourhood meets `H`:
`∀ ε > 0, ]α-ε, α[ ∩ H ≠ ∅` and `]α, α+ε[ ∩ H ≠ ∅`. -/
def IsTwoSidedAccPt (H : Set ℝ) (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → (Ioo (α - ε) α ∩ H).Nonempty ∧ (Ioo α (α + ε) ∩ H).Nonempty

/-- A two-sided accumulation point is in particular an `AccPt` (cluster point) of `H` in Mathlib's
sense — recorded for interoperability with the continuous-extension bridge. -/
theorem isTwoSidedAccPt_imp_mem_closure {H : Set ℝ} {α : ℝ} (h : IsTwoSidedAccPt H α) :
    α ∈ closure H := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨⟨x, hx⟩, _⟩ := h ε hε
  refine ⟨x, hx.2, ?_⟩
  have hx1 := hx.1
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith [hx1.2]
  · linarith [hx1.1]

/-- **The density reduction (fully kernel-clean).** Suppose `H ⊆ ℝ`. Let `S` be a set of "labels"
(in BKS: the two-sided accumulation points) that is **uncountable**, together with a map sending
each label `α ∈ S` to an open interval `]L α, R α[` that is (i) nonempty (`L α < R α`) and
(ii) pairwise disjoint across distinct labels. This configuration is **impossible** on `ℝ`.

This is the engine the BKS gap-to-disjoint-intervals map feeds: with `L α = F X α`, `R α = F Y α`,
it is exactly bullet 3 of the proof. Kernel-clean via `false_of_uncountable_pairwiseDisjoint_Ioo`. -/
theorem no_uncountable_disjoint_image_intervals {S : Set ℝ} {L R : ℝ → ℝ}
    (hunc : ¬ S.Countable) (hlt : ∀ α ∈ S, L α < R α)
    (hdisj : S.PairwiseDisjoint fun α => Ioo (L α) (R α)) : False :=
  false_of_uncountable_pairwiseDisjoint_Ioo hunc hlt hdisj

/-- **Disjointness from a gap-shift ordering (kernel-clean).** This discharges the *disjointness*
half of BKS bullet 3 from a clean order condition, so it is no longer an opaque hypothesis. If the
left endpoint `L` is monotone, the right endpoint `R` is monotone, and the family is **separated**
in the sense `R s ≤ L t` whenever `s < t` (the BKS "gap shift": the `s`-image interval lies entirely
weakly-left of the `t`-image interval), then the open intervals `]L α, R α[` are pairwise disjoint
over any set `S`. In BKS, `L = F X`, `R = F Y`, and `R s ≤ L t` for `s < t` is precisely the
consequence of the gap `]X,Y[ ∩ H = ∅` plus strict monotonicity of `r ↦ F(·, r)`. -/
theorem pairwiseDisjoint_Ioo_of_sep {S : Set ℝ} {L R : ℝ → ℝ}
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s < t → R s ≤ L t) :
    S.PairwiseDisjoint fun α => Ioo (L α) (R α) := by
  intro s hs t ht hst
  rcases lt_or_gt_of_ne hst with h | h
  · -- s < t : the s-interval is weakly-left of the t-interval
    apply disjoint_iff_forall_ne.2
    rintro a ha b hb rfl
    exact absurd (ha.2.trans_le (hsep s hs t ht h)) (not_lt.2 (le_of_lt hb.1))
  · -- t < s : symmetric
    apply disjoint_iff_forall_ne.2
    rintro a ha b hb rfl
    exact absurd (hb.2.trans_le (hsep t ht s hs h)) (not_lt.2 (le_of_lt ha.1))

/-- **Gap extraction.** If `H` is not dense (as a subset of `ℝ`), there is a genuine open gap: an
interval `]X, Y[` with `X < Y` disjoint from `H`. (Mathlib's `dense_iff_inter_open` gives a
nonempty open `U` with `U ∩ H = ∅`; an open set in `ℝ` contains an open interval, hence a gap.) -/
theorem exists_gap_of_not_dense {H : Set ℝ} (h : ¬ Dense H) :
    ∃ X Y : ℝ, X < Y ∧ Disjoint (Ioo X Y) H := by
  rw [dense_iff_inter_open] at h
  push_neg at h
  obtain ⟨U, hUo, ⟨z, hz⟩, hUH⟩ := h
  -- `U` open, `z ∈ U`, so an interval `]z-δ, z+δ[ ⊆ U` for some δ>0
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hUo z hz
  refine ⟨z - δ/2, z + δ/2, by linarith, ?_⟩
  rw [Set.disjoint_left]
  intro a ha haH
  -- `a ∈ ]z-δ/2, z+δ/2[ ⊆ ball z δ ⊆ U`, but `U ∩ H = ∅`
  have haU : a ∈ U := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> [linarith [ha.1]; linarith [ha.2]]
  have : (U ∩ H).Nonempty := ⟨a, haU, haH⟩
  rw [hUH] at this
  exact this.ne_empty rfl

/-- **`dyadic_image_dense` — BKS Lemma 6, Step 2.** Let `H ⊆ ℝ` (in the application
`H = f(D)`, the BKS dyadic image inside `[u,v]`). Suppose:

* **(B)** [BKS bullet 2] the set `accSet` of two-sided accumulation points of `H` is **uncountable**;
* **(C-disjointness)** [BKS bullet 3] there are maps `L, R : ℝ → ℝ` such that, *under the hypothesis
  of a gap* `]X,Y[ ∩ H = ∅` (with `X < Y`), the image intervals `]L α, R α[` over accumulation
  points `α ∈ accSet` are nonempty and pairwise disjoint. (In BKS, `L = F X`, `R = F Y`; nonempty
  by partial strict monotonicity `F X α < F Y α` since `X < Y`, and disjoint by the gap + strict
  monotonicity of `s ↦ F(·,s)`.)

Then `H` is **dense**. This is exactly the BKS contradiction: a gap would yield uncountably many
pairwise-disjoint nonempty open intervals, impossible on `ℝ`. -/
theorem dyadic_image_dense
    {H : Set ℝ} {accSet : Set ℝ}
    (hB : ¬ accSet.Countable)
    (hC : ∀ X Y : ℝ, X < Y → Disjoint (Ioo X Y) H →
      ∃ L R : ℝ → ℝ, (∀ α ∈ accSet, L α < R α) ∧
        accSet.PairwiseDisjoint fun α => Ioo (L α) (R α)) :
    Dense H := by
  by_contra hnd
  obtain ⟨X, Y, hXY, hgap⟩ := exists_gap_of_not_dense hnd
  obtain ⟨L, R, hlt, hdisj⟩ := hC X Y hXY hgap
  exact no_uncountable_disjoint_image_intervals hB hlt hdisj

/-- **`dyadic_image_dense_of_sep` — the same, with disjointness reduced to the gap-shift ordering.**
This is the maximally-honest BKS Step-2 assembly: the disjointness half of bullet 3 is now
*discharged internally* via `pairwiseDisjoint_Ioo_of_sep`, so the caller only supplies

* **(B)** uncountability of `accSet` (BKS bullet 2), and
* the BKS image data: for a gap `]X,Y[`, endpoint maps `L,R` that are (i) nonempty (`L α < R α`)
  and (ii) **gap-separated** (`R s ≤ L t` for `s < t`), i.e. the literal order content of bullet 3.

In BKS `L = F X`, `R = F Y`; (i) is partial strict monotonicity in slot 1 (`X < Y`); the
gap-separation `F Y s ≤ F X t` for accumulation points `s < t` is the consequence of the empty gap
plus strict monotonicity of `r ↦ F(·,r)`. Everything from this order data onward is kernel-clean. -/
theorem dyadic_image_dense_of_sep
    {H : Set ℝ} {accSet : Set ℝ}
    (hB : ¬ accSet.Countable)
    (hC : ∀ X Y : ℝ, X < Y → Disjoint (Ioo X Y) H →
      ∃ L R : ℝ → ℝ, (∀ α ∈ accSet, L α < R α) ∧
        (∀ s ∈ accSet, ∀ t ∈ accSet, s < t → R s ≤ L t)) :
    Dense H := by
  by_contra hnd
  obtain ⟨X, Y, hXY, hgap⟩ := exists_gap_of_not_dense hnd
  obtain ⟨L, R, hlt, hsep⟩ := hC X Y hXY hgap
  exact no_uncountable_disjoint_image_intervals hB hlt (pairwiseDisjoint_Ioo_of_sep hsep)

end Lutar.Wave19
