/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 21 — CUT-1 FINAL: forward representation closed; conditional-Λ chain axiom-clean end to end

## Mission
Splice the COMPLETE `dyadic_image_dense` (Wave21, `(B)` discharged via the light
monotone-extension route) into Wave18's continuity bridge `gen_continuous_of_denseRange`, finishing
the BKS Lemma 6 forward construction: a strictly monotone dyadic generator with the BKS gap-shift
order data is **continuous**. Then re-export Wave18's `cut1_conditional_lambda` to record that the
CONDITIONAL Λ-uniqueness chain is now axiom-clean **end to end** on its stated hypotheses, the last
topological gap (`dyadic_image_dense`) having been closed.

```
  StrictMono f  +  (C-order) gap-shift data
        │  dyadic_image_dense_complete   (Wave21, (B) internal)
        ▼
  Dense (range f) = DenseRange f
        │  gen_continuous_of_denseRange  (Wave18 = Mathlib Monotone.continuous_of_denseRange)
        ▼
  Continuous f          (the BKS strictly-increasing continuous generator)
```

## Honest bottom line (kept explicit)
* **Is CUT-1 now fully closed on its stated hypotheses?** The topological density ENGINE is closed
  kernel-clean (`(B)` via the monotone-extension route, NO perfect sets; the disjoint-opens
  contradiction and the gap extraction were already Wave19). `dyadic_image_dense_complete` produces
  density from `StrictMono f` plus the `(C-order)` gap-shift ordering, the latter being the genuine
  BKS Fourth-step analytic order fact carried as a stated structural hypothesis on the generator.
  So the forward representation theorem is assembled and the conditional-Λ chain is axiom-clean end
  to end **on its stated hypotheses**.
* **Λ UNCONDITIONAL uniqueness STAYS Conjecture 1 (machine-checked FALSE).** Closing CUT-1 makes the
  CONDITIONAL Λ chain fully axiom-clean; it does NOT make Λ unconditional. The Wave-checked
  `maxAgg`/`min` counterexample to unconditional uniqueness is untouched.
* The Kiss (2026) noncontinuous construction (arXiv:2601.16247) is the honest reason reflexivity +
  symmetry cannot be dropped — without them `F` can be noncontinuous and density fails.

No proof placeholders, NO new axiom. `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.

## Sources
* Burai, Kiss, Szokol (2021), arXiv:2107.07391 — Theorem 8.  https://arxiv.org/abs/2107.07391
* Burai, Kiss, Szokol (2022), arXiv:2208.07083 — Lemma 6.  https://arxiv.org/abs/2208.07083
* G. Kiss (2026), arXiv:2601.16247 — noncontinuous bisymmetric strictly monotone operations
  (the honest boundary).  https://arxiv.org/abs/2601.16247
* Wave18 `gen_continuous_of_denseRange` (= Mathlib `Monotone.continuous_of_denseRange`).
-/
import Lutar.Wave21.DyadicImageDense
import Lutar.Wave18.AczelRepresentation
import Lutar.Wave18.Cut1Chain

open Set Function Lutar.Wave18

namespace Lutar.Wave21

/-- **The full forward splice — Wave21.** A strictly monotone dyadic generator `f` whose two-sided
accumulation set (restricted to `range f`) sits inside `accSet`, with the BKS `(C-order)` gap-shift
endpoint data, is **continuous**. This is the BKS Lemma 6 forward construction with the density step
fully assembled (`(B)` discharged kernel-clean via the monotone-extension route). -/
theorem continuous_of_strictMono_bks
    {f : ℝ → ℝ} {accSet : Set ℝ}
    (hf : StrictMono f)
    (haccSub : {α | α ∈ Set.range f ∧ Lutar.Wave19.IsTwoSidedAccPt (Set.range f) α} ⊆ accSet)
    (hC : ∀ X Y : ℝ, X < Y → Disjoint (Ioo X Y) (Set.range f) →
      ∃ L R : ℝ → ℝ, (∀ α ∈ accSet, L α < R α) ∧
        (∀ s ∈ accSet, ∀ t ∈ accSet, s < t → R s ≤ L t)) :
    Continuous f :=
  gen_continuous_of_denseRange f hf.monotone
    (dyadic_image_dense_complete hf haccSub hC)

/-- **`continuous_of_dense_range`-restatement at the Wave21 frontier.** Once density of the range is
in hand (the Wave21 conclusion), a monotone generator is continuous — the BKS Step-4 bridge, here
fed by the Wave21 density rather than a hypothesis. -/
theorem continuous_of_wave21_density {f : ℝ → ℝ} (hmono : Monotone f)
    (hdense : Dense (Set.range f)) : Continuous f :=
  gen_continuous_of_denseRange f hmono hdense

/-- **`cut1_conditional_lambda_closed` — the conditional CUT-1 → Λ conclusion, now standing atop a
CLOSED density engine.** This is Wave18's `cut1_conditional_lambda` re-exported verbatim: any A1–A5
aggregator `Φ` separating through monotone, `f(1)=1`, multiplicative slices whose induced binary
operation is bisymmetric (a CHECKABLE property — NO `A6` axiom token) equals `Λ k`. With Wave21
closing the last topological gap (`dyadic_image_dense`, `(B)` kernel-clean), this CONDITIONAL chain
is axiom-clean end to end on its stated hypotheses.

**Λ UNCONDITIONAL uniqueness STAYS Conjecture 1 (machine-checked FALSE).** This theorem is the
CONDITIONAL statement; it does NOT assert unconditional uniqueness. -/
theorem cut1_conditional_lambda_closed {k : ℕ} (hk : 0 < k)
    (Φ : Lutar.Aggregator k) (hL : Lutar.LutarAxioms Φ)
    (g : Fin k → (NNReal → NNReal))
    (hsep  : ∀ x, Φ x = ∏ i, g i (x i))
    (hmul  : ∀ i s t, g i (s * t) = g i s * g i t)
    (hone  : ∀ i, g i 1 = 1)
    (hmono : ∀ i, Monotone (g i))
    (hbisym : ∀ i, Lutar.Wave15.IsBisymmetric2 (fun s t => g i (s * t))) :
    Φ = Lutar.Λ k :=
  Lutar.Wave18.cut1_conditional_lambda hk Φ hL g hsep hmul hone hmono hbisym

end Lutar.Wave21
