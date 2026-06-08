/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 19 — CUT-1 capstone: `dyadic_image_dense` reduced to its honest residual core

## Mission
Assemble the entire Wave19 chain into the strongest **kernel-clean** statement of the BKS Lemma 6
Step-2 density lemma. After this file, the residual of `dyadic_image_dense` is reduced to exactly
**two named BKS facts**, both with explicit literature provenance, and **nothing else**:

* **(B-residual)** [BKS bullet 2 / Aczél–Dhombres pp. 287–290] the closure of the dyadic image
  contains a nonempty **perfect** subset of two-sided accumulation points; and
* **(C-order)** [BKS bullet 3] for a gap `]X,Y[`, the image endpoints `L = F X`, `R = F Y` are
  nonempty (`L α < R α`) and gap-separated (`R s ≤ L t` for `s < t`).

Given these, density holds — fully kernel-clean — via:
`accSet_not_countable_of_perfect_subset` (B engine) → `pairwiseDisjoint_Ioo_of_sep` (C disjointness)
→ `false_of_uncountable_pairwiseDisjoint_Ioo` (the separable-line contradiction). The "uncountably
many disjoint intervals on a separable line is impossible" engine and the "perfect ⇒ uncountable"
engine are BOTH proven in Wave19; only the two literature facts above are taken as inputs.

NO `sorry`, NO new axiom. `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.

## Sources
* Burai, Kiss, Szokol (2022), arXiv:2208.07083 — Lemma 6, bullets 2–3.
* Aczél, Dhombres, *Functional Equations in Several Variables*, pp. 287–290 (dyadic generator).
-/
import Lutar.Wave19.AccumulationUncountable
import Lutar.Wave19.Cut1Density

open Set Function

namespace Lutar.Wave19

/-- **`dyadic_image_dense_via_perfect` — capstone.** The BKS Step-2 density lemma reduced to its two
honest residual inputs (B-residual: a nonempty perfect subset of the two-sided accumulation set;
C-order: the gap-separated image endpoints). Fully kernel-clean from these.

`H` is the dyadic image `f(D)`; `accSet` its two-sided accumulation set; `C` the perfect subset. -/
theorem dyadic_image_dense_via_perfect
    {H accSet C : Set ℝ}
    (hCsub : C ⊆ accSet) (hCperf : Perfect C) (hCne : C.Nonempty)
    (hC : ∀ X Y : ℝ, X < Y → Disjoint (Ioo X Y) H →
      ∃ L R : ℝ → ℝ, (∀ α ∈ accSet, L α < R α) ∧
        (∀ s ∈ accSet, ∀ t ∈ accSet, s < t → R s ≤ L t)) :
    Dense H :=
  dyadic_image_dense_of_sep
    (accSet_not_countable_of_perfect_subset hCsub hCperf hCne) hC

/-- **Full forward splice via the perfect-subset residual.** Combines the capstone density with the
Wave18 continuity bridge: a monotone dyadic generator `f` whose two-sided accumulation set contains
a nonempty perfect subset and whose image endpoints are gap-separated is **continuous** — the BKS
Steps 2+4 conclusion, kernel-clean from the two named residual facts. -/
theorem continuous_of_perfect_accumulation
    {f : ℝ → ℝ} {accSet C : Set ℝ}
    (hmono : Monotone f)
    (hCsub : C ⊆ accSet) (hCperf : Perfect C) (hCne : C.Nonempty)
    (hC : ∀ X Y : ℝ, X < Y → Disjoint (Ioo X Y) (Set.range f) →
      ∃ L R : ℝ → ℝ, (∀ α ∈ accSet, L α < R α) ∧
        (∀ s ∈ accSet, ∀ t ∈ accSet, s < t → R s ≤ L t)) :
    Continuous f :=
  Lutar.Wave18.gen_continuous_of_denseRange f hmono
    (dyadic_image_dense_via_perfect hCsub hCperf hCne hC)

end Lutar.Wave19
