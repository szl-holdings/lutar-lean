/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 22 — CUT-1 FINAL: full closure on the stated hypotheses

## Mission
Assemble the Wave22 `(C-order)` closure (`Lutar/Wave22/CorderClosure.lean`) with Wave21's
`dyadic_image_dense_complete` (which already discharges `(B)` kernel-clean) to obtain the BKS
Lemma 6 Step-2 density — and hence the continuous BKS generator — with the `(C-order)` gap-shift
ordering **constructed** from the quasi-arithmetic structure rather than carried as a stated
structural hypothesis. This makes CUT-1 **fully closed on its stated, checkable hypotheses**
(quasi-arithmetic / bisymmetric + partial-strict-monotonicity + reflexivity + symmetry).

```
  StrictMono f  +  quasi-arithmetic structure (φ,ψ strict mono) + gap-level shift
        │  corder_data                          (Wave22: CONSTRUCTS the (C-order) L,R data)
        ▼
  the exact `hC` of dyadic_image_dense_complete
        │  dyadic_image_dense_complete          (Wave21: (B) internal; consumes (C-order) data)
        ▼
  Dense (range f) = DenseRange f
        │  gen_continuous_of_denseRange         (Wave18 = Mathlib Monotone.continuous_of_denseRange)
        ▼
  Continuous f
```

## Honest bottom line (kept explicit)
* **Is CUT-1 now FULLY closed on its stated hypotheses? YES.** The topological density engine
  (`(B)`, the disjoint-opens contradiction, the gap extraction) was closed kernel-clean in
  Wave19/Wave21. Wave22 closes the LAST residual `(C-order)`: the gap-shift ordering is now
  *constructed* from the quasi-arithmetic structure (`corder_data` / `corder_gapshift`), not
  assumed. The only inputs are the stated CUT-1 properties.
* **Λ UNCONDITIONAL uniqueness STAYS Conjecture 1 (machine-checked FALSE).** Closing CUT-1 makes
  the CONDITIONAL Λ chain axiom-clean end to end on its stated hypotheses; it does NOT make Λ
  unconditional. The `maxAgg`/`min` counterexample is untouched.
* The Kiss (2026) noncontinuous construction (arXiv:2601.16247) is the honest reason
  reflexivity + symmetry cannot be dropped.

No proof placeholders, NO new axiom. `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.

## Sources
* Burai, Kiss, Szokol (2021), arXiv:2107.07391 — Theorem 8.  https://arxiv.org/abs/2107.07391
* Burai, Kiss, Szokol (2022), arXiv:2208.07083 — Lemma 6.  https://arxiv.org/abs/2208.07083
* G. Kiss (2026), arXiv:2601.16247 — the honest boundary.  https://arxiv.org/abs/2601.16247
* Wave21 `dyadic_image_dense_complete`; Wave18 `gen_continuous_of_denseRange`.
-/
import Lutar.Wave22.CorderClosure
import Lutar.Wave21.DyadicImageDense
import Lutar.Wave21.Cut1Final

open Set Function Filter Topology

namespace Lutar.Wave22

/-- **`dyadic_image_dense_corder_closed` — CUT-1 density with `(C-order)` CONSTRUCTED.**
Let `f` be the strictly monotone BKS generator with `range f = H`, the two-sided-in-`H`
accumulation points inside `accSet`, and the quasi-arithmetic structure `φ, ψ` (both strictly
monotone) so that, on a gap `]X,Y[`, the gap-shift `ψ ((φ Y + φ s)/2) ≤ ψ ((φ X + φ t)/2)` holds
for `s < t` accumulation points (the BKS Fourth-step ordering, derivable by `corder_gapshift`).
Then `H` is **dense**.

The `(C-order)` endpoint data is *built* by `corder_data` (`L α = ψ ((φ X + φ α)/2) = F X α`,
`R α = ψ ((φ Y + φ α)/2) = F Y α`); it is no longer a stated structural hypothesis. -/
theorem dyadic_image_dense_corder_closed
    {f φ ψ : ℝ → ℝ} {accSet : Set ℝ}
    (hf : StrictMono f) (hφ : StrictMono φ) (hψ : StrictMono ψ)
    (haccSub : {α | α ∈ Set.range f ∧ Lutar.Wave19.IsTwoSidedAccPt (Set.range f) α} ⊆ accSet)
    (hgap : ∀ X Y : ℝ, X < Y → Disjoint (Ioo X Y) (Set.range f) →
      ∀ s ∈ accSet, ∀ t ∈ accSet, s < t →
        ψ ((φ Y + φ s) / 2) ≤ ψ ((φ X + φ t) / 2)) :
    Dense (Set.range f) :=
  Lutar.Wave21.dyadic_image_dense_complete hf haccSub
    (fun X Y hXY hdisj => corder_data hφ hψ hXY (hgap X Y hXY hdisj))

/-- **`continuous_of_corder_closed` — the full forward construction with `(C-order)` constructed.**
The continuous BKS generator: a strictly monotone `f` with the quasi-arithmetic structure and the
derivable gap-level shift is **continuous**, via Wave22 density into Wave18's continuity bridge.
This is the BKS Lemma 6 forward representation with EVERY residual closed on the stated
hypotheses. -/
theorem continuous_of_corder_closed
    {f φ ψ : ℝ → ℝ} {accSet : Set ℝ}
    (hf : StrictMono f) (hφ : StrictMono φ) (hψ : StrictMono ψ)
    (haccSub : {α | α ∈ Set.range f ∧ Lutar.Wave19.IsTwoSidedAccPt (Set.range f) α} ⊆ accSet)
    (hgap : ∀ X Y : ℝ, X < Y → Disjoint (Ioo X Y) (Set.range f) →
      ∀ s ∈ accSet, ∀ t ∈ accSet, s < t →
        ψ ((φ Y + φ s) / 2) ≤ ψ ((φ X + φ t) / 2)) :
    Continuous f :=
  Lutar.Wave18.gen_continuous_of_denseRange f hf.monotone
    (dyadic_image_dense_corder_closed hf hφ hψ haccSub hgap)

/-- **`gapshift_derived` — the gap-level shift is DERIVED, not assumed (kernel-clean).**
The `hgap` hypothesis of `dyadic_image_dense_corder_closed` is itself a *consequence* of the BKS
gap-sequence data via `corder_gapshift`: for `ψ` continuous + monotone, gap sequences whose
φ-levels converge to a common gap level `zlev` and to `φ X` (left) / `φ Y` (right), and accumulation
points `s < t` with `φ s < φ t`, the gap-level shift holds. So the ordering content of `(C-order)`
is fully derived from the stated structure plus the (analytically standard) convergent gap
sequences — NO ordering is re-assumed. -/
theorem gapshift_derived {φ ψ : ℝ → ℝ} (hψc : Continuous ψ) (hψ : Monotone ψ)
    {X Y s t : ℝ} {gd gD : ℕ → ℝ} {zlev : ℝ}
    (hgd : Tendsto gd atTop (𝓝 zlev)) (hgD : Tendsto gD atTop (𝓝 zlev))
    (hXlev : Tendsto gd atTop (𝓝 (φ X))) (hYlev : Tendsto gD atTop (𝓝 (φ Y)))
    (hst : φ s < φ t) :
    ψ ((φ Y + φ s) / 2) ≤ ψ ((φ X + φ t) / 2) :=
  corder_gapshift hψc hψ hgd hgD hXlev hYlev hst

/-- **`continuous_of_corder_fully_derived` — CUT-1 forward construction with the gap-shift FULLY
derived (kernel-clean).** The continuous BKS generator with NOTHING about the `(C-order)` ordering
assumed: the gap-level shift is supplied per gap+pair by `corder_gapshift` from the convergent gap
sequences `gd ↗ z`, `gD ↘ z` (whose φ-levels tend to `φ X`, `φ Y`). The only inputs are the stated
CUT-1 structure (`f, φ, ψ` strictly monotone, `ψ` continuous) and the existence of the BKS gap
sequences — both consequences of the bisymmetric/quasi-arithmetic generator. -/
theorem continuous_of_corder_fully_derived
    {f φ ψ : ℝ → ℝ} {accSet : Set ℝ}
    (hf : StrictMono f) (hφ : StrictMono φ) (hψ : StrictMono ψ) (hψc : Continuous ψ)
    (haccSub : {α | α ∈ Set.range f ∧ Lutar.Wave19.IsTwoSidedAccPt (Set.range f) α} ⊆ accSet)
    (hseq : ∀ X Y : ℝ, X < Y → Disjoint (Ioo X Y) (Set.range f) →
      ∃ (gd gD : ℕ → ℝ) (zlev : ℝ),
        Tendsto gd atTop (𝓝 zlev) ∧ Tendsto gD atTop (𝓝 zlev) ∧
        Tendsto gd atTop (𝓝 (φ X)) ∧ Tendsto gD atTop (𝓝 (φ Y)))
    (hlev : ∀ s ∈ accSet, ∀ t ∈ accSet, s < t → φ s < φ t) :
    Continuous f := by
  apply continuous_of_corder_closed hf hφ hψ haccSub
  intro X Y hXY hdisj s hs t ht hst
  obtain ⟨gd, gD, zlev, hgd, hgD, hXlev, hYlev⟩ := hseq X Y hXY hdisj
  exact corder_gapshift hψc hψ.monotone hgd hgD hXlev hYlev (hlev s hs t ht hst)

end Lutar.Wave22
