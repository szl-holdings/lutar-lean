/-
# Lutar.Scaling.MetabolicScalingDeep

## What this file proves (and what it does NOT)

This is **round 2** of the scaling cores: DEEPER, harder mathematical
properties of the same power-law functions studied in
`Lutar.Scaling.MetabolicScaling`.  It proves, sorry-free and kernel-verified:

  * **strict convexity** of the compute-allometry loss curve
    `L(N) = L0 · N^(-α)` on `(0, ∞)` (via the first derivative being strictly
    monotone);
  * the **asymptotic limits** `L0 · N^(-α) → 0` as `N → ∞` and
    `L0 · N^(-α) → +∞` as `N → 0⁺`;
  * the **WBE / Banavar-Maritan-Rinaldo network-dimension exponent formula**
    `β(D) = D/(D+1)`: it equals `3/4` at `D = 3`, is strictly increasing in `D`,
    and lies in `(0,1)` for every `D ≥ 1`;
  * the exact **linear relations among the canonical quarter-power exponents**
    `{3/4, -1/4, 1/4}` (heartbeat invariance `(-1/4)+(1/4)=0`,
    `metabolic - lifespan = 1/2`, etc.);
  * **joint monotonicity / continuity of SZL-Φ**: strict monotonicity in body
    mass `M` (for `β > 0`) and continuity of Φ on its positive domain.

As in round 1, under HONESTY DOCTRINE v11 "proven" means a SORRY-FREE,
kernel-verified Lean theorem with disclosed axioms (`#print axioms` after each
result).  These are theorems about the SHAPE of the functions — convexity,
limits, the algebra of the exponent formula — NOT empirical claims that real
organisms obey Kleiber's law, that the WBE fractal-network derivation is
biologically correct, or that neural loss curves follow a power law.  Those
empirical sources are cited ONLY as motivation:

  * Kleiber 1932, *Hilgardia* 6:315-353 (3/4-power metabolic law);
  * West, Brown & Enquist 1997, *Science* 276:122-126 (fractal network);
  * Banavar, Maritan & Rinaldo 1999, *Nature* 399:130-132 (transportation
    network dimension `D/(D+1)`);
  * Brown, Gillooly, Allen, Savage & West 2004, *Ecology* 85:1771-1789 (MTE);
  * Kaplan et al. 2020, arXiv:2001.08361 (neural scaling laws).

The Lutar Invariant Λ remains **Conjecture 1**; nothing here promotes it.
-/

import Lutar.Scaling.MetabolicScaling
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Lutar.Scaling.Deep

open Real Filter Topology Set

/-! ## 1. Loss-curve strict convexity

`L(N) = L0 · N^(-α)` with `L0 > 0`, `α > 0` is **strictly convex** on
`(0, ∞)`.  We use `StrictMonoOn.strictConvexOn_of_deriv`: it suffices that `L`
is continuous on the closed-up domain and that its derivative is strictly
monotone on the interior.  The derivative is
`deriv L (N) = L0 · (-α) · N^(-α-1)`, and since the exponent `-α-1 < 0`, the
factor `N^(-α-1)` is strictly *decreasing*, so multiplying by the negative
constant `L0·(-α)` makes the derivative strictly *increasing*. -/

/-- The compute-allometry loss law `L(N) = L0 · N^(-α)`, restated locally
(same shape as `Lutar.Scaling.computeLoss`). -/
noncomputable def lossCurve (L0 α N : ℝ) : ℝ := L0 * N ^ (-α)

/-- The derivative of `lossCurve L0 α` at a point `N ≠ 0` is
`L0 * (-α * N^(-α-1))`. -/
theorem lossCurve_hasDerivAt {L0 α N : ℝ} (hN : N ≠ 0) :
    HasDerivAt (fun x => lossCurve L0 α x) (L0 * (-α * N ^ (-α - 1))) N := by
  have hb : HasDerivAt (fun x : ℝ => x ^ (-α)) (-α * N ^ (-α - 1)) N := by
    simpa using Real.hasDerivAt_rpow_const (p := -α) (Or.inl hN)
  exact (hb.const_mul L0)

/-- **Loss-curve strict convexity.**  For `L0 > 0`, `α > 0`, the loss curve
`L(N) = L0 · N^(-α)` is strictly convex on the positive ray `(0,∞)`.
(The closed ray `[0,∞)` is not usable: `N^(-α)` blows up at `0`.) -/
theorem lossCurve_strictConvexOn {L0 α : ℝ} (hL0 : 0 < L0) (hα : 0 < α) :
    StrictConvexOn ℝ (Ioi (0 : ℝ)) (fun N => lossCurve L0 α N) := by
  -- Domain is convex and open, so interior (Ioi 0) = Ioi 0.
  have hconv : Convex ℝ (Ioi (0 : ℝ)) := convex_Ioi 0
  -- Continuity on Ioi 0 : N ↦ L0 * N^(-α), with N ≠ 0 on the domain.
  have hcont : ContinuousOn (fun N => lossCurve L0 α N) (Ioi (0 : ℝ)) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.rpow_const continuousOn_id
    intro x hx
    exact Or.inl (ne_of_gt hx)
  -- The derivative on the interior equals g(N) = L0 * (-α * N^(-α-1)).
  have hint : interior (Ioi (0 : ℝ)) = Ioi (0 : ℝ) := interior_Ioi
  -- deriv of lossCurve agrees with this g on Ioi 0
  have hderiv : ∀ N ∈ Ioi (0 : ℝ),
      deriv (fun x => lossCurve L0 α x) N = L0 * (-α * N ^ (-α - 1)) := by
    intro N hN
    exact (lossCurve_hasDerivAt (ne_of_gt hN)).deriv
  -- g is strictly monotone increasing on Ioi 0.
  have hmono : StrictMonoOn (deriv (fun x => lossCurve L0 α x))
      (interior (Ioi (0 : ℝ))) := by
    rw [hint]
    intro a ha b hb hab
    rw [hderiv a ha, hderiv b hb]
    -- want: L0*(-α * a^(-α-1)) < L0*(-α * b^(-α-1))
    -- since a < b and exponent (-α-1)<0, a^(-α-1) > b^(-α-1);
    -- multiply by negative (-α) flips, then by positive L0.
    have hapos : (0:ℝ) < a := ha
    have hexp : (-α - 1) < 0 := by linarith
    -- a^(-α-1) and b^(-α-1): strictly antitone in base for negative exponent
    have hpow : b ^ (-α - 1) < a ^ (-α - 1) :=
      Real.rpow_lt_rpow_of_neg hapos hab hexp
    -- multiply by -α < 0 (flips), then by L0 > 0 (preserves)
    have hnegmul : -α * a ^ (-α - 1) < -α * b ^ (-α - 1) := by
      have hnα : -α < 0 := by linarith
      nlinarith [hpow, hnα]
    exact (mul_lt_mul_left hL0).mpr hnegmul
  exact hmono.strictConvexOn_of_deriv hconv hcont

/-! ## 2. Asymptotic limits of the loss curve

`L0 · N^(-α) → 0` as `N → ∞` (the loss can be driven arbitrarily low) and
`L0 · N^(-α) → +∞` as `N → 0⁺` (the loss blows up).  Core facts:
`Real.tendsto_rpow_neg_atTop`, `tendsto_inv_nhdsGT_zero`, and continuity of
`N ↦ N^α` to push `N → 0⁺` through to `N^α → 0⁺`. -/

/-- **Loss → 0 at scale → ∞.**  For `L0` arbitrary and `α > 0`,
`L0 · N^(-α) → 0` as `N → ∞`. -/
theorem lossCurve_tendsto_zero_atTop {L0 α : ℝ} (hα : 0 < α) :
    Tendsto (fun N => lossCurve L0 α N) atTop (𝓝 0) := by
  unfold lossCurve
  have h : Tendsto (fun N : ℝ => N ^ (-α)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop hα
  have := h.const_mul L0
  simpa using this

/-- **Loss → +∞ as scale → 0⁺.**  For `L0 > 0` and `α > 0`,
`L0 · N^(-α) → +∞` as `N → 0⁺` (through positive `N`). -/
theorem lossCurve_tendsto_atTop_nhdsGT_zero {L0 α : ℝ} (hL0 : 0 < L0)
    (hα : 0 < α) :
    Tendsto (fun N => lossCurve L0 α N) (𝓝[>] 0) atTop := by
  -- N^α → 0⁺ as N → 0⁺ (continuity + positivity of the power).
  have hpow_to_zero : Tendsto (fun N : ℝ => N ^ α) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousWithinAt (fun N : ℝ => N ^ α) (Ici 0) 0 := by
      apply ContinuousWithinAt.rpow_const
      · exact (continuous_id.continuousWithinAt)
      · exact Or.inr hα.le
    have h2 : Tendsto (fun N : ℝ => N ^ α) (𝓝[≥] 0) (𝓝 ((0:ℝ) ^ α)) := hc.tendsto
    have h3 : Tendsto (fun N : ℝ => N ^ α) (𝓝[>] 0) (𝓝 ((0:ℝ) ^ α)) :=
      h2.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    simpa [Real.zero_rpow (ne_of_gt hα)] using h3
  -- Through positive N, N^α > 0, so it tends to 0 within (0,∞); invert.
  have hpow_pos : ∀ᶠ N in 𝓝[>] (0:ℝ), (0:ℝ) < N ^ α := by
    filter_upwards [self_mem_nhdsWithin] with N hN
    exact Real.rpow_pos_of_pos hN α
  have hpow_to_zero' : Tendsto (fun N : ℝ => N ^ α) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hpow_to_zero, hpow_pos⟩
  -- (N^α)⁻¹ → +∞.
  have hinv : Tendsto (fun N : ℝ => (N ^ α)⁻¹) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.comp hpow_to_zero'
  -- N^(-α) = (N^α)⁻¹, and multiplying by L0 > 0 preserves the +∞ limit.
  have hneg : (fun N : ℝ => N ^ (-α)) =ᶠ[𝓝[>] 0] (fun N : ℝ => (N ^ α)⁻¹) := by
    filter_upwards [self_mem_nhdsWithin] with N hN
    rw [← Real.rpow_neg hN.le]
  have hinv' : Tendsto (fun N : ℝ => N ^ (-α)) (𝓝[>] 0) atTop :=
    hinv.congr' hneg.symm
  have := hinv'.const_mul_atTop hL0
  simpa [lossCurve] using this

/-! ## 3. WBE / Banavar-Maritan-Rinaldo network-dimension exponent

The transportation-network argument predicts the metabolic exponent
`β(D) = D/(D+1)` where `D` is the effective network dimension.  We prove the
**properties of this formula**: it equals `3/4` at `D = 3`, it is strictly
increasing in `D` (for `D ≥ 1`), and it always lies in `(0,1)` for `D ≥ 1`.
We do NOT claim organisms are `D`-dimensional fractal networks. -/

/-- The network-dimension metabolic exponent `β(D) = D/(D+1)`. -/
noncomputable def wbeExp (D : ℝ) : ℝ := D / (D + 1)

/-- **WBE 3/4 at `D = 3`.**  The exponent formula yields exactly `3/4` when the
network dimension is `3`. -/
theorem wbeExp_three : wbeExp 3 = 3 / 4 := by
  unfold wbeExp; norm_num

/-- **WBE exponent strictly increasing in `D`.**  For `1 ≤ D₁ < D₂`,
`β(D₁) < β(D₂)`.  (Holds in fact for all `D₁, D₂ > -1`; we state it on the
physically relevant `D ≥ 1` regime.) -/
theorem wbeExp_strictMono {D1 D2 : ℝ} (hD1 : 1 ≤ D1) (hlt : D1 < D2) :
    wbeExp D1 < wbeExp D2 := by
  unfold wbeExp
  have h1 : (0:ℝ) < D1 + 1 := by linarith
  have h2 : (0:ℝ) < D2 + 1 := by linarith
  rw [div_lt_div_iff₀ h1 h2]
  nlinarith [hlt, h1, h2]

/-- **WBE exponent strictly between 0 and 1.**  For every `D ≥ 1`,
`0 < β(D) < 1`. -/
theorem wbeExp_mem_Ioo {D : ℝ} (hD : 1 ≤ D) :
    wbeExp D ∈ Ioo (0 : ℝ) 1 := by
  unfold wbeExp
  have h1 : (0:ℝ) < D + 1 := by linarith
  have hDpos : (0:ℝ) < D := by linarith
  constructor
  · exact div_pos hDpos h1
  · rw [div_lt_one h1]; linarith

/-! ## 4. Quarter-power exponent family: exact linear relations

The canonical metabolic/allometric exponents are
`β_metabolic = 3/4`, `β_heart = -1/4`, `β_lifespan = 1/4`.  These satisfy exact
linear identities as real numbers.  These are pure rational-arithmetic facts
about the EXPONENTS (not claims that organisms obey them). -/

/-- Canonical metabolic exponent. -/
noncomputable def βmetabolic : ℝ := 3 / 4
/-- Canonical heart-rate exponent. -/
noncomputable def βheart : ℝ := -(1 / 4)
/-- Canonical lifespan exponent. -/
noncomputable def βlifespan : ℝ := 1 / 4

/-- **Heartbeat invariance (exponent form).**  `β_heart + β_lifespan = 0`:
the heart-rate and lifespan exponents are exact negatives. -/
theorem heart_lifespan_sum_zero : βheart + βlifespan = 0 := by
  unfold βheart βlifespan; norm_num

/-- **Metabolic minus lifespan equals one half.** `β_metabolic - β_lifespan = 1/2`. -/
theorem metabolic_minus_lifespan : βmetabolic - βlifespan = 1 / 2 := by
  unfold βmetabolic βlifespan; norm_num

/-- **Metabolic plus heart equals one half.** `β_metabolic + β_heart = 1/2`. -/
theorem metabolic_plus_heart : βmetabolic + βheart = 1 / 2 := by
  unfold βmetabolic βheart; norm_num

/-- **Three-times-lifespan equals metabolic.** `3 · β_lifespan = β_metabolic`,
i.e. the metabolic 3/4 exponent is exactly three quarter-power units. -/
theorem three_lifespan_eq_metabolic : 3 * βlifespan = βmetabolic := by
  unfold βlifespan βmetabolic; norm_num

/-- **Full closure relation.**  `β_metabolic + β_heart + β_lifespan = 3/4`:
adding all three canonical exponents recovers the metabolic exponent (since
heart and lifespan cancel). -/
theorem quarter_power_family_closure :
    βmetabolic + βheart + βlifespan = 3 / 4 := by
  unfold βmetabolic βheart βlifespan; norm_num

/-! ## 5. SZL-Φ joint properties: strict monotonicity in `M` and continuity

We reuse the SZL-Φ construct from `Lutar.Scaling`:
`Φ = Φ0 · M^β · exp(c·Δp) · (τc/τ0)^(1/4)`.  Round 1 proved positivity and
strict monotonicity in the proton-motive force `Δp`.  Here we add: strict
monotonicity in body mass `M` (for `β > 0`), and continuity of Φ in `M` on the
positive domain. -/

open Lutar.Scaling in
/-- **SZL-Φ strict monotonicity in body mass.**  With `β > 0` and the structural
quantities positive, increasing the mass `M` strictly increases Φ. -/
theorem szlPhi_strictMono_mass {Φ0 β c Δp τc τ0 : ℝ}
    (hΦ0 : 0 < Φ0) (hβ : 0 < β) (hτc : 0 < τc) (hτ0 : 0 < τ0)
    {M1 M2 : ℝ} (hM1 : 0 < M1) (hlt : M1 < M2) :
    Lutar.Scaling.szlPhi Φ0 β M1 c Δp τc τ0
      < Lutar.Scaling.szlPhi Φ0 β M2 c Δp τc τ0 := by
  unfold Lutar.Scaling.szlPhi
  have hexp : 0 < Real.exp (c * Δp) := Real.exp_pos _
  have hratio : 0 < τc / τ0 := div_pos hτc hτ0
  have hA : 0 < (τc / τ0) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hratio _
  -- M^β strictly increases since β > 0.
  have hpow : M1 ^ β < M2 ^ β := Real.rpow_lt_rpow hM1.le hlt hβ
  have h1 : Φ0 * M1 ^ β < Φ0 * M2 ^ β := (mul_lt_mul_left hΦ0).mpr hpow
  have h2 : Φ0 * M1 ^ β * Real.exp (c * Δp)
          < Φ0 * M2 ^ β * Real.exp (c * Δp) :=
    (mul_lt_mul_right hexp).mpr h1
  exact (mul_lt_mul_right hA).mpr h2

open Lutar.Scaling in
/-- **SZL-Φ continuity in body mass.**  On the positive domain `(0,∞)`, the map
`M ↦ Φ(M)` is continuous (for any real `β`), since it is a product of a
constant, the continuous power `M ↦ M^β` (continuous away from 0), and constant
factors. -/
theorem szlPhi_continuousOn_mass {Φ0 β c Δp τc τ0 : ℝ} :
    ContinuousOn (fun M => Lutar.Scaling.szlPhi Φ0 β M c Δp τc τ0)
      (Ioi (0 : ℝ)) := by
  unfold Lutar.Scaling.szlPhi
  apply ContinuousOn.mul
  apply ContinuousOn.mul
  apply ContinuousOn.mul continuousOn_const
  · -- M ↦ M^β continuous on (0,∞) since M ≠ 0 there
    apply ContinuousOn.rpow_const continuousOn_id
    intro x hx
    exact Or.inl (ne_of_gt hx)
  · exact continuousOn_const
  · exact continuousOn_const

/-! ## Axiom footprints (HONESTY DOCTRINE v11 disclosure) -/

#print axioms lossCurve_hasDerivAt
#print axioms lossCurve_strictConvexOn
#print axioms lossCurve_tendsto_zero_atTop
#print axioms lossCurve_tendsto_atTop_nhdsGT_zero
#print axioms wbeExp_three
#print axioms wbeExp_strictMono
#print axioms wbeExp_mem_Ioo
#print axioms heart_lifespan_sum_zero
#print axioms metabolic_minus_lifespan
#print axioms metabolic_plus_heart
#print axioms three_lifespan_eq_metabolic
#print axioms quarter_power_family_closure
#print axioms szlPhi_strictMono_mass
#print axioms szlPhi_continuousOn_mass

end Lutar.Scaling.Deep
