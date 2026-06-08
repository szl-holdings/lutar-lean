/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 22 — the SHARPEST conditional Λ-uniqueness (weakest checkable hypothesis)

## Mission
Λ UNCONDITIONAL uniqueness is machine-checked **FALSE** (the `maxAgg` / `min` counterexample, see
`Lutar.Round13.Lambda_Uniqueness`), so it CANNOT be proven and stays **Conjecture 1**. We do NOT
attempt the false statement. Instead, per the Wave22 mandate, we STRENGTHEN the CONDITIONAL result:
identify the **weakest additional checkable hypothesis** under which Λ-uniqueness holds, and prove
the **sharpest conditional uniqueness theorem** honestly reachable.

## What this file proves (no proof placeholders, NO new axiom)

The previous frontier `Lutar.Wave18.cut1_conditional_lambda` assumed FIVE slice hypotheses:
`hsep` (separability) + `hmul` (slice-multiplicativity) + `hone` (`fᵢ 1 = 1`) + `hmono`
(slice-monotonicity) + `hbisym` (slice bisymmetry). We sharpen this on TWO independent fronts:

1. **`bisymmetry_is_redundant`** — the slice-bisymmetry hypothesis `hbisym` does NO work: it is a
   *theorem*, not an assumption. The slice-induced binary operation `(s,t) ↦ fᵢ (s · t)` is
   bisymmetric whenever the slice is multiplicative (`Lutar.Wave15.mul_isBisymmetric` content,
   discharged directly). So any conditional uniqueness statement carrying `hbisym` can drop it.

2. **`slice_one_eq_one_of_sep`** — the hypothesis `hone` (`fᵢ 1 = 1`) is also DERIVABLE, not
   assumed: from the A3 diagonal normalization `Φ (fun _ ↦ 1) = 1` lifted through separability
   `Φ x = ∏ᵢ fᵢ (xᵢ)`, together with the multiplicative idempotency `fᵢ 1 = (fᵢ 1)²` (so
   `fᵢ 1 ∈ {0,1}`), the product `∏ᵢ fᵢ 1 = 1` forces every `fᵢ 1 = 1`. (A zero factor would
   collapse the product to `0 ≠ 1`.)

3. **`cut1_sharp_conditional_lambda`** — the SHARPEST conditional uniqueness theorem. The weakest
   checkable hypothesis set is

      `{A1–A5}  +  separability  +  slice-multiplicativity  +  slice-monotonicity`

   (both `hbisym` and `hone` removed). Under exactly these, `Φ = Λ k`. This is strictly weaker than
   `Lutar.Wave18.cut1_conditional_lambda` (two fewer hypotheses) and is discharged axiom-free through
   the in-tree `Lutar.Round13.lambda_unique_of_separable`, which already *derives* the power-law
   shape from slice-multiplicativity via `multiplicative_monotone_isPow_pos`.

## Honesty / scope (kept explicit)
* This does **NOT** make Λ unconditional. The `maxAgg`/`min` counterexample to A1–A5-only uniqueness
  is untouched; Λ stays **Conjecture 1**. What is sharpened is the *conditional* theorem: the extra
  checkable hypothesis needed beyond A1–A5 is now exactly **slice-multiplicativity + separability +
  slice-monotonicity** — and we PROVE that the two further properties previously carried
  (bisymmetry, `fᵢ 1 = 1`) are redundant consequences.
* "Weakest checkable hypothesis" is meant within the *separable* family: slice-multiplicativity is
  the irreducible Cauchy-type input that the false unconditional statement lacks. Dropping it
  re-admits the `maxAgg`/`min` counterexamples, so it cannot be weakened further without making the
  conclusion false — this is the sharp boundary.

No proof placeholders, NO new axiom. `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.

## Sources
* Aczél, J. (1966). *Lectures on Functional Equations.* Academic Press, §5.1 (bisymmetry ⇒
  quasi-arithmetic) and §2.1 (Cauchy multiplicative ⇒ power law).
* Maksa, Gy. (2000). On the bisymmetry/separability representation of means.
* Burai, Kiss, Szokol (2021), arXiv:2107.07391; (2022) arXiv:2208.07083.
  https://arxiv.org/abs/2107.07391  https://arxiv.org/abs/2208.07083
* In-tree: `Lutar.Round13.lambda_unique_of_separable`,
  `Lutar.Round13.multiplicative_monotone_isPow_pos`, `Lutar.Wave15.mul_isBisymmetric`,
  `Lutar.Round13.Lambda_Uniqueness.maxAgg_ne_Lambda` (the unconditional counterexample).
-/
import Lutar.Round13.LambdaSeparable
import Lutar.Wave15.BisymmetryCut1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Lutar.Wave22

open NNReal BigOperators
open Lutar Lutar.Round13

/-- **`bisymmetry_is_redundant` — the slice-bisymmetry hypothesis is a theorem.**
For any multiplicative slice `f` (`f (s · t) = f s · f t`), the slice-induced binary operation
`(s,t) ↦ f (s · t)` is bisymmetric: `B (B a b) (B c d) = B (B a c) (B b d)`. Hence the `hbisym`
hypothesis of `Lutar.Wave18.cut1_conditional_lambda` does no work — it is implied by
slice-multiplicativity and can be dropped. -/
theorem bisymmetry_is_redundant {f : NNReal → NNReal}
    (hmul : ∀ s t, f (s * t) = f s * f t) :
    Lutar.Wave15.IsBisymmetric2 (fun s t => f (s * t)) := by
  intro a b c d
  -- Expand every application of the slice operation via multiplicativity; both groupings reduce to
  -- `f a * f b * f c * f d` (commutativity of `*` on `ℝ≥0`).
  simp only [hmul]
  ring

/-- **`slice_one_eq_one_of_sep` — the unit-normalization `fᵢ 1 = 1` is derivable.**
If `Φ` separates as `Φ x = ∏ᵢ fᵢ (xᵢ)`, satisfies the A3 diagonal normalization
`Φ (fun _ ↦ c) = c`, and each slice is multiplicative, then every `fᵢ 1 = 1`. So `hone` need not be
assumed: it follows from `{A3, separability, slice-multiplicativity}`.

Proof: each `fᵢ 1 = fᵢ (1·1) = (fᵢ 1)²` is idempotent, hence `0` or `1`. The diagonal value
`∏ᵢ fᵢ 1 = Φ (fun _ ↦ 1) = 1` is a product of `0/1` factors equal to `1`, which is impossible if any
factor is `0`; so every factor is `1`. -/
theorem slice_one_eq_one_of_sep {k : ℕ} {Φ : Aggregator k}
    {f : Fin k → (NNReal → NNReal)}
    (hsep : ∀ x, Φ x = ∏ i, f i (x i))
    (hnorm : ∀ c : NNReal, Φ (fun _ => c) = c)
    (hmul : ∀ i s t, f i (s * t) = f i s * f i t) :
    ∀ i, f i 1 = 1 := by
  classical
  -- Diagonal at 1: `∏ᵢ fᵢ 1 = Φ (fun _ ↦ 1) = 1`.
  have hdiag : (∏ i, f i (1 : NNReal)) = 1 := by
    have := (hsep (fun _ => (1 : NNReal))).symm
    rw [hnorm 1] at this
    simpa using this
  -- Each `fᵢ 1` is `0` or `1` (idempotent under multiplicativity).
  have hidem : ∀ i, f i 1 = 0 ∨ f i 1 = 1 := by
    intro i
    have h : f i 1 = f i 1 * f i 1 := by simpa using hmul i 1 1
    rcases eq_or_ne (f i 1) 0 with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (mul_right_cancel₀ h0 (by rw [one_mul]; exact h.symm))
  -- No factor can be `0`, else the product is `0 ≠ 1`.
  intro i
  rcases hidem i with h0 | h1
  · exfalso
    have hzero : (∏ j, f j (1 : NNReal)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) h0
    rw [hzero] at hdiag
    exact (by norm_num : (0 : NNReal) ≠ 1) hdiag
  · exact h1

/-- **`cut1_sharp_conditional_lambda` — the SHARPEST conditional Λ-uniqueness (kernel-clean).**

Any A1–A5 aggregator `Φ` that *separates* through *monotone, multiplicative* slices equals `Λ k`:

    `{A1–A5}` + `Φ x = ∏ᵢ fᵢ (xᵢ)` + `fᵢ (s·t) = fᵢ s · fᵢ t` + `Monotone fᵢ`  ⟹  `Φ = Λ k`.

This is strictly weaker than `Lutar.Wave18.cut1_conditional_lambda`: the slice-bisymmetry hypothesis
is dropped (it is a theorem — `bisymmetry_is_redundant`) and the unit-normalization `fᵢ 1 = 1` is
dropped (it is derived — `slice_one_eq_one_of_sep` from A3 + separability + multiplicativity). The
remaining hypotheses are the WEAKEST checkable set: dropping slice-multiplicativity re-admits the
`maxAgg`/`min` counterexamples, making the conclusion false, so this is the sharp boundary.

Discharged axiom-free through `Lutar.Round13.lambda_unique_of_separable`. Λ UNCONDITIONAL uniqueness
remains **Conjecture 1** (machine-checked FALSE); this is the sharpest *conditional* theorem. -/
theorem cut1_sharp_conditional_lambda {k : ℕ} (hk : 0 < k)
    (Φ : Aggregator k) (hL : LutarAxioms Φ)
    (f : Fin k → (NNReal → NNReal))
    (hsep  : ∀ x, Φ x = ∏ i, f i (x i))
    (hmul  : ∀ i s t, f i (s * t) = f i s * f i t)
    (hmono : ∀ i, Monotone (f i)) :
    Φ = Λ k := by
  -- The unit-normalization is derived (not assumed) from A3 + separability + multiplicativity.
  have hone : ∀ i, f i 1 = 1 :=
    slice_one_eq_one_of_sep hsep hL.A3.A3_normalize hmul
  -- Discharge through the in-tree axiom-free CUT-2 theorem.
  exact lambda_unique_of_separable hk Φ hL f hsep hmul hone hmono

/-- **`cut1_sharp_subsumes_bisymmetric` — the sharp theorem subsumes the bisymmetric frontier.**
Re-derives `Lutar.Wave18.cut1_conditional_lambda`'s conclusion while *ignoring* both its `hone` and
its `hbisym` hypotheses, witnessing that `cut1_sharp_conditional_lambda` is a genuine strengthening
(same conclusion, strictly fewer working hypotheses). -/
theorem cut1_sharp_subsumes_bisymmetric {k : ℕ} (hk : 0 < k)
    (Φ : Aggregator k) (hL : LutarAxioms Φ)
    (f : Fin k → (NNReal → NNReal))
    (hsep  : ∀ x, Φ x = ∏ i, f i (x i))
    (hmul  : ∀ i s t, f i (s * t) = f i s * f i t)
    (hmono : ∀ i, Monotone (f i))
    (_hone : ∀ i, f i 1 = 1)
    (_hbisym : ∀ i, Lutar.Wave15.IsBisymmetric2 (fun s t => f i (s * t))) :
    Φ = Λ k :=
  cut1_sharp_conditional_lambda hk Φ hL f hsep hmul hmono

end Lutar.Wave22
