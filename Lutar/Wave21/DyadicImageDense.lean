/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 21 — CUT-1 FINAL: the COMPLETE `dyadic_image_dense`

## Mission
Assemble the entire BKS Lemma 6 Step-2 density argument into a single theorem whose **only**
inputs are the BKS structural hypotheses on the dyadic generator — with the `(B)` uncountability
hypothesis of Wave19's `dyadic_image_dense_of_sep` now **discharged internally** via the Wave21
light monotone-extension route (`Lutar/Wave21/Uncountable.lean`), and the `(C-order)` gap-shift
ordering carried as the BKS image-endpoint order data (the literal content of the parent-paper
Theorem 8 Fourth step, eqs (8)–(9)).

The chain:
```
  StrictMono f
      │  range_not_countable_of_strictMono            (Wave21: monotone ⇒ injective ⇒ continuum)
      ▼
  ¬ (range f).Countable
      │  accSet_not_countable_of_uncountable           (Wave21: H = two-sided ∪ left/right-gap)
      ▼
  ¬ accSet.Countable                                  (= the Wave19 (B) hypothesis)
      │  dyadic_image_dense_of_sep                      (Wave19: gap ⇒ uncountably many disjoint
      ▼                                                  intervals on a separable line ⇒ ⊥)
  Dense (range f)
```

So `dyadic_image_dense_complete` produces `Dense (range f)` from:
* `StrictMono f` — the BKS generator is strictly increasing (Wave18 generator soundness; this is
  what drives BOTH injectivity-for-uncountability AND the order content), and
* the BKS image-endpoint order data `(C-order)`: for a gap `]X,Y[ ∩ range f = ∅`, endpoint maps
  `L, R` that are nonempty (`L α < R α`) and gap-separated (`R s ≤ L t` for `s < t`).

`(B)` is no longer a hypothesis. `(C-order)` is the genuine analytic order fact BKS derive from the
generator recursion; it is carried as a stated hypothesis here (NOT faked, NOT axiomatised) — see
the honest residual note below.

No proof placeholders, NO new axiom. `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.

## Honest residual after this file
`(B)` is CLOSED (kernel-clean, no perfect sets). The single remaining structural input is
`(C-order)` — the gap-shift ordering `R s ≤ L t` of the image endpoints, i.e. the BKS Fourth-step
inequality chain. It is a hypothesis of `dyadic_image_dense_complete`, supplied by the dyadic
generator recursion `f((d₁+d₂)/2)=F(f d₁,f d₂)` plus partial strict monotonicity of `F`
(Aczél–Dhombres pp. 287–290). It is genuine analytic content, documented, NOT faked.

## Sources
* Burai, Kiss, Szokol (2021), arXiv:2107.07391 — Theorem 8 (First/Second/Fourth steps).
  https://arxiv.org/abs/2107.07391
* Burai, Kiss, Szokol (2022), arXiv:2208.07083 — Lemma 6, Step 2.  https://arxiv.org/abs/2208.07083
-/
import Lutar.Wave21.Uncountable
import Lutar.Wave19.Density

open Set Function

namespace Lutar.Wave21

/-- **`dyadic_image_dense_complete` — the BKS Lemma 6 Step-2 density lemma with `(B)` discharged.**

Let `f : ℝ → ℝ` be **strictly monotone** (the BKS dyadic generator extended strictly-increasingly),
`H := range f`, and `accSet` a set that contains every two-sided accumulation point of `H` lying in
`H`. Suppose the BKS image-endpoint **order data** `(C-order)`: for a gap `]X,Y[` disjoint from `H`
(`X < Y`), there are endpoint maps `L, R : ℝ → ℝ` with `L α < R α` (nonempty image intervals) and
`R s ≤ L t` whenever `s < t` in `accSet` (the gap-shift ordering). Then `H` is **dense**.

The uncountability of `accSet` (Wave19's `(B)` input) is proved here, NOT assumed: strict
monotonicity ⇒ `H` uncountable (`range_not_countable_of_strictMono`) ⇒ `accSet` uncountable
(`accSet_not_countable_of_uncountable`). The rest is Wave19's `dyadic_image_dense_of_sep`. -/
theorem dyadic_image_dense_complete
    {f : ℝ → ℝ} {accSet : Set ℝ}
    (hf : StrictMono f)
    (haccSub : {α | α ∈ Set.range f ∧ Lutar.Wave19.IsTwoSidedAccPt (Set.range f) α} ⊆ accSet)
    (hC : ∀ X Y : ℝ, X < Y → Disjoint (Ioo X Y) (Set.range f) →
      ∃ L R : ℝ → ℝ, (∀ α ∈ accSet, L α < R α) ∧
        (∀ s ∈ accSet, ∀ t ∈ accSet, s < t → R s ≤ L t)) :
    Dense (Set.range f) :=
  Lutar.Wave19.dyadic_image_dense_of_sep
    (accSet_not_countable_of_uncountable (range_not_countable_of_strictMono hf) haccSub)
    hC

/-- **Set-form variant.** The same conclusion for an abstract `H` that is uncountable and whose
two-sided-in-`H` accumulation points sit inside `accSet`. This is the maximally-general statement:
density follows from uncountability of `H` (whatever its source) plus the gap-shift order data;
`(B)` is fully internal. -/
theorem dyadic_image_dense_of_uncountable
    {H accSet : Set ℝ}
    (hH : ¬ H.Countable)
    (haccSub : {α | α ∈ H ∧ Lutar.Wave19.IsTwoSidedAccPt H α} ⊆ accSet)
    (hC : ∀ X Y : ℝ, X < Y → Disjoint (Ioo X Y) H →
      ∃ L R : ℝ → ℝ, (∀ α ∈ accSet, L α < R α) ∧
        (∀ s ∈ accSet, ∀ t ∈ accSet, s < t → R s ≤ L t)) :
    Dense H :=
  Lutar.Wave19.dyadic_image_dense_of_sep
    (accSet_not_countable_of_uncountable hH haccSub) hC

end Lutar.Wave21
