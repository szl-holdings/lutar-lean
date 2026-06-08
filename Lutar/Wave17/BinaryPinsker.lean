/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 17 — CF-23 advance: FULL binary (2-bin) Pinsker inequality, axiom-free

## Honesty verdict first (philosophers' enforcement)

The in-tree DPO axiom `Lutar.DPOFeasibility.pinsker` is **FALSE-as-stated** (no simplex
hypothesis) and its token is **UNTOUCHED** by this file.  This file proves the **conditional,
binary (two-bin) Pinsker bound** as a genuine kernel-clean theorem:

    `binary_pinsker` :  `2·(p−q)² ≤ KL_bin(p,q)`   for `p,q ∈ (0,1)`,

where `KL_bin(p,q) = p·log(p/q) + (1−p)·log((1−p)/(1−q))`.  This is the textbook binary case of
Pinsker's inequality (Cover–Thomas Lemma 11.6.1), and it strictly upgrades the Wave16 result
`binary_inv_sum_ge_four` (the `g″ ≥ 0` convexity crux) into the full binary bound by assembling
the mean-value / monotone-derivative chain.

## What is proven here (NO sorry, NO new axiom)

* `gapBin q p`            — the Pinsker gap `KL_bin(p,q) − 2(p−q)²`, written with `log p − log q`.
* `hasDerivAt_gapBin`     — `gapBin' q p = log p − log q − log(1−p) + log(1−q) − 4(p−q)`.
* `hasDerivAt_gapBinDeriv`— `gapBin″ q p = 1/p + 1/(1−p) − 4`  (≥ 0 by `binary_inv_sum_ge_four`).
* `gapBinDeriv_q`         — `gapBin'(q) = 0`.
* `gapBin_nonneg`         — `gapBin q p ≥ 0`, i.e. the binary Pinsker bound, via:
    `gapBin'` is monotone-increasing on `(0,1)` (second derivative ≥ 0), `gapBin'(q)=0`, hence
    `gapBin` decreases on `(0,q]` and increases on `[q,1)`, with minimum `gapBin q q = 0`.
* `binary_pinsker`        — the headline `2·(p−q)² ≤ KL_bin(p,q)`.

## Honesty / scope
- EXPERIMENTAL companion (`Lutar/Wave17/`). NO new axiom; NO sorry. Locked-proven set unchanged.
- This is the BINARY (two-bin) case. Full simplex Pinsker `½‖p−q‖₁² ≤ KL(p‖q)` requires a
  data-processing reduction from the binary case (partition the alphabet into `{pᵢ≥qᵢ}` / rest);
  that reduction is the remaining CF-23-FULL gap and is NOT proven here.
- DPO `pinsker` stays FALSE-as-stated, token UNTOUCHED. Λ unchanged (Conjecture 1).

## References
- Pinsker, M.S. (1964). *Information and Information Stability*. §2.2.
- Cover, T.M. & Thomas, J.A. (2006). *Elements of Information Theory*, 2nd ed., Wiley.
  Thm 11.6.1 (Pinsker), Lemma 11.6.1 (binary reduction). ISBN 978-0-471-24195-9.

Signed-off-by: SZL CTO <cto@szl-holdings.com>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Lutar.Wave17

open Real Set

/-- The binary Pinsker gap, with `log(p/q)` expanded as `log p − log q`. -/
noncomputable def gapBin (q p : ℝ) : ℝ :=
  p * (Real.log p - Real.log q) + (1 - p) * (Real.log (1 - p) - Real.log (1 - q))
    - 2 * (p - q) ^ 2

/-- The first derivative of `gapBin q`. -/
noncomputable def gapBinDeriv (q p : ℝ) : ℝ :=
  Real.log p - Real.log q - Real.log (1 - p) + Real.log (1 - q) - 4 * (p - q)

/-- `gapBin q` has derivative `gapBinDeriv q p` at `p ∈ (0,1)`. -/
theorem hasDerivAt_gapBin (q p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    HasDerivAt (gapBin q) (gapBinDeriv q p) p := by
  unfold gapBin gapBinDeriv
  have h1p : (0 : ℝ) < 1 - p := by linarith
  have hlp : HasDerivAt (fun x => x * (Real.log x - Real.log q))
      (Real.log p - Real.log q + 1) p := by
    have := (hasDerivAt_id p).mul ((Real.hasDerivAt_log (ne_of_gt hp)).sub_const (Real.log q))
    convert this using 1; field_simp
  have hrp : HasDerivAt (fun x => (1 - x) * (Real.log (1 - x) - Real.log (1 - q)))
      (-(Real.log (1 - p) - Real.log (1 - q) + 1)) p := by
    have hin : HasDerivAt (fun x : ℝ => 1 - x) (-1) p := by
      simpa using (hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)
    have hlog : HasDerivAt (fun x => Real.log (1 - x) - Real.log (1 - q)) ((1 - p)⁻¹ * (-1)) p :=
      ((Real.hasDerivAt_log (ne_of_gt h1p)).comp p hin).sub_const (Real.log (1 - q))
    have := hin.mul hlog
    convert this using 1; field_simp; ring
  have hquad : HasDerivAt (fun x => 2 * (x - q) ^ 2) (4 * (p - q)) p := by
    have hb : HasDerivAt (fun x : ℝ => x - q) 1 p := (hasDerivAt_id p).sub_const q
    have := (hb.pow 2).const_mul (2 : ℝ)
    convert this using 1; ring
  have := (hlp.add hrp).sub hquad
  convert this using 1; ring

/-- The second derivative of `gapBin q`: `gapBinDeriv q` has derivative `1/p + 1/(1−p) − 4`. -/
theorem hasDerivAt_gapBinDeriv (q p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    HasDerivAt (gapBinDeriv q) (p⁻¹ + (1 - p)⁻¹ - 4) p := by
  unfold gapBinDeriv
  have h1p : (0 : ℝ) < 1 - p := by linarith
  have hlog1 : HasDerivAt (fun x => Real.log x) p⁻¹ p := Real.hasDerivAt_log (ne_of_gt hp)
  have hin : HasDerivAt (fun x : ℝ => 1 - x) (-1) p := by
    simpa using (hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)
  have hlog2 : HasDerivAt (fun x => Real.log (1 - x)) ((1 - p)⁻¹ * (-1)) p :=
    (Real.hasDerivAt_log (ne_of_gt h1p)).comp p hin
  have hquad : HasDerivAt (fun x : ℝ => 4 * (x - q)) 4 p := by
    have hb : HasDerivAt (fun x : ℝ => x - q) 1 p := (hasDerivAt_id p).sub_const q
    simpa using hb.const_mul 4
  have step1 : HasDerivAt (fun x => Real.log x - Real.log q) p⁻¹ p := hlog1.sub_const _
  have step2 : HasDerivAt (fun x => Real.log x - Real.log q - Real.log (1 - x))
      (p⁻¹ - (1 - p)⁻¹ * (-1)) p := step1.sub hlog2
  have step3 : HasDerivAt (fun x => Real.log x - Real.log q - Real.log (1 - x) + Real.log (1 - q))
      (p⁻¹ - (1 - p)⁻¹ * (-1)) p := step2.add_const _
  have step4 := step3.sub hquad
  convert step4 using 1; ring

/-- `gapBinDeriv q q = 0`. -/
theorem gapBinDeriv_q (q : ℝ) : gapBinDeriv q q = 0 := by
  unfold gapBinDeriv; ring

/-- `gapBin q q = 0`. -/
theorem gapBin_q (q : ℝ) : gapBin q q = 0 := by
  unfold gapBin; ring

/-- The Wave16 convexity crux, restated: `4 ≤ 1/p + 1/(1−p)` on `(0,1)`. -/
theorem inv_add_inv_ge_four (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    4 ≤ p⁻¹ + (1 - p)⁻¹ := by
  have h1p : (0 : ℝ) < 1 - p := by linarith
  rw [inv_eq_one_div, inv_eq_one_div, div_add_div _ _ (ne_of_gt hp) (ne_of_gt h1p),
    le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (2 * p - 1)]

/-- `gapBin q` is differentiable at every `p ∈ (0,1)`. -/
theorem differentiableAt_gapBin (q p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    DifferentiableAt ℝ (gapBin q) p :=
  (hasDerivAt_gapBin q p hp hp1).differentiableAt

/-- `gapBinDeriv q` is differentiable at every `p ∈ (0,1)`. -/
theorem differentiableAt_gapBinDeriv (q p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    DifferentiableAt ℝ (gapBinDeriv q) p :=
  (hasDerivAt_gapBinDeriv q p hp hp1).differentiableAt

/-- On the open interval `(0,1)`, `deriv (gapBin q) = gapBinDeriv q`. -/
theorem deriv_gapBin (q p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    deriv (gapBin q) p = gapBinDeriv q p :=
  (hasDerivAt_gapBin q p hp hp1).deriv

/-- On the open interval `(0,1)`, `deriv (gapBinDeriv q) = 1/p + 1/(1−p) − 4 ≥ 0`. -/
theorem deriv_gapBinDeriv_nonneg (q p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    0 ≤ deriv (gapBinDeriv q) p := by
  rw [(hasDerivAt_gapBinDeriv q p hp hp1).deriv]
  have := inv_add_inv_ge_four p hp hp1
  linarith

/-- `gapBinDeriv q` is monotone-increasing on any `Icc a b ⊆ (0,1)`. -/
theorem monotoneOn_gapBinDeriv {a b q : ℝ} (ha : 0 < a) (hb : b < 1) :
    MonotoneOn (gapBinDeriv q) (Set.Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
  · -- continuity on Icc a b
    intro x hx
    rw [Set.mem_Icc] at hx
    exact ((hasDerivAt_gapBinDeriv q x (by linarith [hx.1]) (by linarith [hx.2])).continuousAt).continuousWithinAt
  · -- differentiable on interior = Ioo a b
    rw [interior_Icc]
    intro x hx
    rw [Set.mem_Ioo] at hx
    exact (differentiableAt_gapBinDeriv q x (by linarith [hx.1]) (by linarith [hx.2])).differentiableWithinAt
  · rw [interior_Icc]
    intro x hx
    rw [Set.mem_Ioo] at hx
    exact deriv_gapBinDeriv_nonneg q x (by linarith [hx.1]) (by linarith [hx.2])

/-- **Binary Pinsker gap is nonnegative** for `p, q ∈ (0,1)`. -/
theorem gapBin_nonneg (q p : ℝ) (hq : 0 < q) (hq1 : q < 1) (hp : 0 < p) (hp1 : p < 1) :
    0 ≤ gapBin q p := by
  rcases le_total q p with hqp | hpq
  · -- q ≤ p : gapBinDeriv ≥ 0 on [q,p], so gapBin monotone on [q,p]; gapBin q q ≤ gapBin q p
    have hderiv_nonneg : ∀ x ∈ Set.Ioo q p, 0 ≤ deriv (gapBin q) x := by
      intro x hx
      rw [Set.mem_Ioo] at hx
      have hx0 : 0 < x := lt_trans hq hx.1
      have hx1 : x < 1 := lt_trans hx.2 hp1
      rw [deriv_gapBin q x hx0 hx1]
      have hmono := monotoneOn_gapBinDeriv (a := q) (b := p) (q := q) hq hp1
      have : gapBinDeriv q q ≤ gapBinDeriv q x :=
        hmono (Set.mem_Icc.mpr ⟨le_refl q, hqp⟩) (Set.mem_Icc.mpr ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
          (le_of_lt hx.1)
      rwa [gapBinDeriv_q] at this
    have hmono : MonotoneOn (gapBin q) (Set.Icc q p) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc q p)
      · intro x hx
        rw [Set.mem_Icc] at hx
        exact ((hasDerivAt_gapBin q x (by linarith [hx.1]) (by linarith [hx.2])).continuousAt).continuousWithinAt
      · rw [interior_Icc]; intro x hx
        rw [Set.mem_Ioo] at hx
        exact (differentiableAt_gapBin q x (by linarith [hx.1]) (by linarith [hx.2])).differentiableWithinAt
      · rw [interior_Icc]; exact hderiv_nonneg
    have := hmono (Set.mem_Icc.mpr ⟨le_refl q, hqp⟩) (Set.mem_Icc.mpr ⟨hqp, le_refl p⟩) hqp
    rwa [gapBin_q] at this
  · -- p ≤ q : gapBinDeriv ≤ 0 on [p,q], so gapBin antitone on [p,q]; gapBin q q ≤ gapBin q p
    have hderiv_nonpos : ∀ x ∈ Set.Ioo p q, deriv (gapBin q) x ≤ 0 := by
      intro x hx
      rw [Set.mem_Ioo] at hx
      have hx0 : 0 < x := lt_trans hp hx.1
      have hx1 : x < 1 := lt_trans hx.2 hq1
      rw [deriv_gapBin q x hx0 hx1]
      have hmono := monotoneOn_gapBinDeriv (a := p) (b := q) (q := q) hp hq1
      have : gapBinDeriv q x ≤ gapBinDeriv q q :=
        hmono (Set.mem_Icc.mpr ⟨le_of_lt hx.1, le_of_lt hx.2⟩) (Set.mem_Icc.mpr ⟨hpq, le_refl q⟩)
          (le_of_lt hx.2)
      rwa [gapBinDeriv_q] at this
    have hanti : AntitoneOn (gapBin q) (Set.Icc p q) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc p q)
      · intro x hx
        rw [Set.mem_Icc] at hx
        exact ((hasDerivAt_gapBin q x (by linarith [hx.1]) (by linarith [hx.2])).continuousAt).continuousWithinAt
      · rw [interior_Icc]; intro x hx
        rw [Set.mem_Ioo] at hx
        exact (differentiableAt_gapBin q x (by linarith [hx.1]) (by linarith [hx.2])).differentiableWithinAt
      · rw [interior_Icc]; exact hderiv_nonpos
    have := hanti (Set.mem_Icc.mpr ⟨le_refl p, hpq⟩) (Set.mem_Icc.mpr ⟨hpq, le_refl q⟩) hpq
    rwa [gapBin_q] at this

/-- **Binary (two-bin) Pinsker inequality.**  For `p, q ∈ (0,1)`,
    `2·(p−q)² ≤ p·log(p/q) + (1−p)·log((1−p)/(1−q))`. -/
theorem binary_pinsker (q p : ℝ) (hq : 0 < q) (hq1 : q < 1) (hp : 0 < p) (hp1 : p < 1) :
    2 * (p - q) ^ 2 ≤
      p * (Real.log p - Real.log q) + (1 - p) * (Real.log (1 - p) - Real.log (1 - q)) := by
  have := gapBin_nonneg q p hq hq1 hp hp1
  unfold gapBin at this
  linarith

end Lutar.Wave17
