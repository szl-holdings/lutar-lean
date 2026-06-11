/-
# Lutar.Scaling.MetabolicScaling

## What this file proves (and what it does NOT)

This file proves rigorous, kernel-verified **MATHEMATICAL PROPERTIES** of the
power-law functions that appear in metabolic / allometric scaling and in the
SZL-Φ construct: positivity, strict monotonicity, and the lifetime-heartbeats
**algebraic invariance identity**.

It does **NOT** prove the empirical scaling laws themselves. In particular it
does NOT assert that:
  * Kleiber's 3/4-power metabolic law holds for real organisms
    [Kleiber 1932, *Hilgardia* 6:315-353];
  * the West-Brown-Enquist fractal-network derivation is biologically correct
    [West, Brown & Enquist 1997, *Science* 276:122-126];
  * the Metabolic Theory of Ecology is empirically validated
    [Brown, Gillooly, Allen, Savage & West 2004, *Ecology* 85:1771-1789];
  * neural-scaling / compute-allometry loss curves obey a particular power law
    [Kaplan et al. 2020, *Scaling Laws for Neural Language Models*,
    arXiv:2001.08361].

Those are EMPIRICAL claims about biology and machine learning and are cited
ONLY as the motivation for the function shapes. Under HONESTY DOCTRINE v11,
"proven" means a SORRY-FREE, kernel-verified Lean theorem with disclosed
axioms. What is proven below are theorems of the form "the function
`B0 * M^β` is positive / monotone" and the identity "`f0*M^(-1/4)` times
`L0*M^(1/4)` equals `f0*L0`, independent of `M`". These are honest
mathematical cores of the engineering analogies.

The Lutar Invariant Λ remains **Conjecture 1**; nothing here promotes it.
This file is a candidate experimental→locked promotion ONLY for the specific
named theorems below that genuinely prove out sorry-free.

All real exponents use `Real.rpow`. Each theorem is followed by
`#print axioms` so the axiom footprint is disclosed.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp

namespace Lutar.Scaling

open Real

/-! ## 1. Power-law positivity

For `M > 0`, `B0 > 0`, and any real exponent `β`, the power law
`B(M) = B0 * M^β` is strictly positive.  Core fact:
`Real.rpow_pos_of_pos`. -/

/-- A power-law metabolic rate `B(M) = B0 · M^β` is strictly positive
whenever `B0 > 0` and `M > 0`, for ANY real exponent `β`. -/
theorem powerLaw_pos {B0 M : ℝ} (β : ℝ) (hB0 : 0 < B0) (hM : 0 < M) :
    0 < B0 * M ^ β := by
  have hpow : 0 < M ^ β := Real.rpow_pos_of_pos hM β
  exact mul_pos hB0 hpow

#print axioms powerLaw_pos

/-! ## 2. Power-law strict monotonicity

For `B0 > 0`, `β > 0`, and `0 < M₁ < M₂`, the power law is strictly
increasing.  Core fact: `Real.rpow_lt_rpow`. -/

/-- A power law `B0 · M^β` with positive coefficient and positive exponent is
strictly increasing in `M` on the positive reals. -/
theorem powerLaw_strictMono {B0 β M1 M2 : ℝ} (hB0 : 0 < B0) (hβ : 0 < β)
    (hM1 : 0 < M1) (hlt : M1 < M2) :
    B0 * M1 ^ β < B0 * M2 ^ β := by
  have hpow : M1 ^ β < M2 ^ β := Real.rpow_lt_rpow hM1.le hlt hβ
  exact (mul_lt_mul_left hB0).mpr hpow

#print axioms powerLaw_strictMono

/-! ## 3. THE HEADLINE — lifetime-heartbeats invariance

Define heart rate `f(M) = f0 · M^(-1/4)` and lifespan `L(M) = L0 · M^(1/4)`.
Then for ALL `M > 0`:

  `f(M) · L(M) = f0 · L0`,

i.e. the product is **independent of body mass `M`**.  The exponents
`-1/4` and `+1/4` cancel exactly: `M^(-1/4) · M^(1/4) = M^0 = 1`.
Core facts: `Real.rpow_add` (or `rpow_neg` + `rpow_natCast`) and
`Real.rpow_zero`.

This is the strongest result in the file: the slogan "total lifetime
heartbeats ≈ constant across mammals" has a genuine algebraic theorem
behind it (the product of the two power laws does not depend on `M`). -/

/-- Heart rate as a quarter-power *decreasing* law. -/
noncomputable def heartRate (f0 M : ℝ) : ℝ := f0 * M ^ (-(1 : ℝ) / 4)

/-- Lifespan as a quarter-power *increasing* law. -/
noncomputable def lifespan (L0 M : ℝ) : ℝ := L0 * M ^ ((1 : ℝ) / 4)

/-- **Lifetime-heartbeats invariance.**  For every `M > 0`,
`heartRate f0 M · lifespan L0 M = f0 · L0`; the product is independent of
the body mass `M`. -/
theorem lifetime_heartbeats_invariant (f0 L0 : ℝ) {M : ℝ} (hM : 0 < M) :
    heartRate f0 M * lifespan L0 M = f0 * L0 := by
  unfold heartRate lifespan
  have hMne : M ≠ 0 := ne_of_gt hM
  -- M^(-1/4) * M^(1/4) = M^(-1/4 + 1/4) = M^0 = 1
  have hcancel : M ^ (-(1 : ℝ) / 4) * M ^ ((1 : ℝ) / 4) = 1 := by
    rw [← Real.rpow_add hM]
    norm_num
  calc f0 * M ^ (-(1 : ℝ) / 4) * (L0 * M ^ ((1 : ℝ) / 4))
      = f0 * L0 * (M ^ (-(1 : ℝ) / 4) * M ^ ((1 : ℝ) / 4)) := by ring
    _ = f0 * L0 * 1 := by rw [hcancel]
    _ = f0 * L0 := by ring

#print axioms lifetime_heartbeats_invariant

/-! ## 4. Compute-allometry monotonic decrease

For `L0 > 0`, `α > 0`, the loss-style allometry `L(N) = L0 · N^(-α)` is
strictly **decreasing** (strict antitone) on `(0, ∞)`, and positive there.
Core facts: `Real.rpow_neg`, `Real.rpow_lt_rpow`, `Real.rpow_pos_of_pos`. -/

/-- Compute-allometry loss law `L(N) = L0 · N^(-α)`. -/
noncomputable def computeLoss (L0 α N : ℝ) : ℝ := L0 * N ^ (-α)

/-- The compute-allometry law is strictly positive on the positive reals. -/
theorem computeLoss_pos {L0 α N : ℝ} (hL0 : 0 < L0) (hN : 0 < N) :
    0 < computeLoss L0 α N := by
  unfold computeLoss
  exact mul_pos hL0 (Real.rpow_pos_of_pos hN (-α))

/-- The compute-allometry law `L0 · N^(-α)` with `L0 > 0`, `α > 0` is
**strictly decreasing** in `N` on the positive reals. -/
theorem computeLoss_strictAnti {L0 α : ℝ} (hL0 : 0 < L0) (hα : 0 < α)
    {N1 N2 : ℝ} (hN1 : 0 < N1) (hlt : N1 < N2) :
    computeLoss L0 α N2 < computeLoss L0 α N1 := by
  unfold computeLoss
  -- N^(-α) = (N^α)⁻¹; larger N ⇒ larger N^α ⇒ smaller inverse.
  have hpos1 : 0 < N1 ^ α := Real.rpow_pos_of_pos hN1 α
  have hN2 : 0 < N2 := hN1.trans hlt
  have hposlt : N1 ^ α < N2 ^ α := Real.rpow_lt_rpow hN1.le hlt hα
  have hinv : N2 ^ (-α) < N1 ^ (-α) := by
    rw [Real.rpow_neg hN1.le, Real.rpow_neg hN2.le]
    exact inv_strictAnti₀ hpos1 hposlt
  exact (mul_lt_mul_left hL0).mpr hinv

#print axioms computeLoss_pos
#print axioms computeLoss_strictAnti

/-! ## 5. Exponent additivity (comparator core)

For `M > 0` and any real exponents `a, b`:  `M^a · M^b = M^(a+b)`.
This is `Real.rpow_add`, the law that makes the exponent comparator's
cancellation/composition rules valid. -/

/-- **Exponent additivity.**  `M^a · M^b = M^(a+b)` for `M > 0`.  This is the
algebraic backbone of the exponent comparator (composing/cancelling
scaling exponents). -/
theorem exponent_additivity {M : ℝ} (hM : 0 < M) (a b : ℝ) :
    M ^ a * M ^ b = M ^ (a + b) := (Real.rpow_add hM a b).symm

#print axioms exponent_additivity

/-! ## 6. SZL-Φ positivity and PMF monotonicity (our own construct)

The SZL-Φ rate construct:

  `Φ = Φ0 · M^β · exp(η · Δp_eV / (k · T)) · (τc / τ0)^(1/4)`.

With `Φ0 > 0`, `M > 0`, `T > 0`, `τc > 0`, `τ0 > 0` (and any real `β, η, k,
Δp`) we prove `Φ > 0` (product of positives; `exp > 0`).  We also prove the
**PMF monotonicity** structural property: with the kinetic prefactor
`η/(k·T) > 0`, Φ is strictly increasing as the proton-motive force `Δp`
increases — the exp factor strictly rises.

These are honestly-provable STRUCTURAL properties of OUR construct, not
empirical claims about biology. -/

/-- The SZL-Φ rate construct. `c := η/(k·T)` is the kinetic coefficient on the
proton-motive force `Δp`; `A := (τc/τ0)^(1/4)` is the coherence-time factor. -/
noncomputable def szlPhi (Φ0 β M c Δp τc τ0 : ℝ) : ℝ :=
  Φ0 * M ^ β * Real.exp (c * Δp) * (τc / τ0) ^ ((1 : ℝ) / 4)

/-- **SZL-Φ positivity.**  With all the structural quantities positive,
`Φ > 0`, for ANY real `β`, kinetic coefficient `c`, and PMF `Δp`. -/
theorem szlPhi_pos {Φ0 β M c Δp τc τ0 : ℝ}
    (hΦ0 : 0 < Φ0) (hM : 0 < M) (hτc : 0 < τc) (hτ0 : 0 < τ0) :
    0 < szlPhi Φ0 β M c Δp τc τ0 := by
  unfold szlPhi
  have hMpow : 0 < M ^ β := Real.rpow_pos_of_pos hM β
  have hexp : 0 < Real.exp (c * Δp) := Real.exp_pos _
  have hratio : 0 < τc / τ0 := div_pos hτc hτ0
  have hA : 0 < (τc / τ0) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hratio _
  have h1 : 0 < Φ0 * M ^ β := mul_pos hΦ0 hMpow
  have h2 : 0 < Φ0 * M ^ β * Real.exp (c * Δp) := mul_pos h1 hexp
  exact mul_pos h2 hA

/-- **SZL-Φ PMF monotonicity.**  With a positive kinetic coefficient
`c = η/(k·T) > 0` and the structural quantities positive, raising the
proton-motive force `Δp` strictly increases Φ. -/
theorem szlPhi_strictMono_pmf {Φ0 β M c τc τ0 : ℝ}
    (hΦ0 : 0 < Φ0) (hM : 0 < M) (hc : 0 < c) (hτc : 0 < τc) (hτ0 : 0 < τ0)
    {Δp1 Δp2 : ℝ} (hΔp : Δp1 < Δp2) :
    szlPhi Φ0 β M c Δp1 τc τ0 < szlPhi Φ0 β M c Δp2 τc τ0 := by
  unfold szlPhi
  -- The positive constant prefactor and suffix factor.
  have hMpow : 0 < M ^ β := Real.rpow_pos_of_pos hM β
  have hpre : 0 < Φ0 * M ^ β := mul_pos hΦ0 hMpow
  have hratio : 0 < τc / τ0 := div_pos hτc hτ0
  have hA : 0 < (τc / τ0) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hratio _
  -- exp is strictly monotone, and c > 0 so c*Δp is strictly monotone in Δp.
  have hargs : c * Δp1 < c * Δp2 := (mul_lt_mul_left hc).mpr hΔp
  have hexp : Real.exp (c * Δp1) < Real.exp (c * Δp2) := Real.exp_lt_exp.mpr hargs
  -- Multiply through by the positive prefactor, then by the positive suffix.
  have step1 : Φ0 * M ^ β * Real.exp (c * Δp1)
             < Φ0 * M ^ β * Real.exp (c * Δp2) :=
    (mul_lt_mul_left hpre).mpr hexp
  exact (mul_lt_mul_right hA).mpr step1

#print axioms szlPhi_pos
#print axioms szlPhi_strictMono_pmf

end Lutar.Scaling
