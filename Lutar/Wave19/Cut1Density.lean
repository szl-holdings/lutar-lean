/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 19 — CUT-1 density → continuity bridge (BKS Lemma 6, Steps 2→4)

## Mission (sub-lemma D: assembly)
Connect the Wave19 density assembly to the Wave18 continuous-extension bridge, closing the BKS
Step-2 → Step-4 hand-off **end to end, kernel-clean**:

```
  dyadic_image_dense  (Wave19, BKS Step 2)         ── gives ──▶  Dense (range f) = DenseRange f
        │                                                                  │
        ▼                                                                  ▼
  gen_continuous_of_denseRange  (Wave18, Mathlib Monotone.continuous_of_denseRange, BKS Step 4)
        │
        ▼
  Continuous f   (the BKS strictly-increasing continuous generator)
```

The point: `DenseRange f` is *definitionally* `Dense (Set.range f)`. So the moment the BKS
density argument produces `Dense (range f)` for the dyadic generator `f`, the monotone generator
extends continuously — with NO extra hypotheses beyond monotonicity. This file makes that splice a
single kernel-clean theorem, exhibiting that Wave19's `dyadic_image_dense` plugs *exactly* into the
Wave18 bridge that "begins where the density lemma ends".

NO `sorry`, NO new axiom. `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.

## Sources
* Burai, Kiss, Szokol (2022), arXiv:2208.07083 — Lemma 6, Steps 2 (density) and 4 (continuity).
* Wave18 `gen_continuous_of_denseRange` (= Mathlib `Monotone.continuous_of_denseRange`).
-/
import Lutar.Wave19.Density
import Lutar.Wave18.AczelRepresentation

open Set Function Lutar.Wave18

namespace Lutar.Wave19

/-- `DenseRange f` is exactly `Dense (range f)`: the Wave19 density output is the Wave18 bridge
input, with nothing lost. -/
theorem denseRange_iff_dense_range {f : ℝ → ℝ} : DenseRange f ↔ Dense (Set.range f) := Iff.rfl

/-- **The Step-2 → Step-4 splice (kernel-clean).** A monotone dyadic generator `f : ℝ → ℝ` whose
**range is dense** (the Wave19 `dyadic_image_dense` conclusion, with `H = range f`) is
**continuous**, via the Wave18 bridge `gen_continuous_of_denseRange`. This is the literal BKS
"if `f(D)` is dense then `f` extends continuously" step, fully discharged once density is in hand. -/
theorem continuous_of_dense_range {f : ℝ → ℝ} (hmono : Monotone f)
    (hdense : Dense (Set.range f)) : Continuous f :=
  gen_continuous_of_denseRange f hmono hdense

/-- **End-to-end forward splice.** Bundles Wave19 density (in the maximally-honest
`dyadic_image_dense_of_sep` form, `H = range f`) with the Wave18 continuity bridge: given the BKS
order data (uncountable accumulation points + gap-separated image endpoints), a monotone dyadic
generator is continuous. This is the BKS Step-2-and-4 conclusion as one kernel-clean theorem; the
only inputs are the two named BKS order facts (B) and the gap-separation, exactly as documented. -/
theorem continuous_of_bks_density_data
    {f : ℝ → ℝ} {accSet : Set ℝ}
    (hmono : Monotone f)
    (hB : ¬ accSet.Countable)
    (hC : ∀ X Y : ℝ, X < Y → Disjoint (Ioo X Y) (Set.range f) →
      ∃ L R : ℝ → ℝ, (∀ α ∈ accSet, L α < R α) ∧
        (∀ s ∈ accSet, ∀ t ∈ accSet, s < t → R s ≤ L t)) :
    Continuous f :=
  gen_continuous_of_denseRange f hmono (dyadic_image_dense_of_sep hB hC)

end Lutar.Wave19
