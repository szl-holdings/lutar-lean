/-
Copyright © 2026 Stephen P. Lutar Jr. (SZL Holdings).
Released under the Apache-2.0 License.

# CoherenceDecay — strict monotone decay of the l₁ coherence monotone under
# pure-dephasing Lindblad (GKSL) dynamics, and its single-crossing corollary
# for the Λ-v5 engineering gate.  (Wave24, NEW — staged PROPOSED.)

## What is NEW here (vs the existing kernel)

`Lutar/QuantumBio/SZL_v5.lean` already proves *static* properties of the
Λ-v5 ENGINEERING gate `lambdaVal = coherence * charge`:
  - `decohered_never_closes`, `uncharged_never_closes`, `lambda_mono_in_coherence`.

This module proves the *time-dynamics* those statics never touched: under a
pure-dephasing Lindblad channel the off-diagonal "coherence mass" obeys
    C(t) = C₀ · e^(−γ t),  γ > 0,
and we prove this is **strictly antitone** in t (coherence only ever decreases),
and that a positive closure floor `lamMin` (with charge held at a constant
q > 0) is crossed at a **unique finite time** t* = (1/γ)·ln(q·C₀ / lamMin).

This is the rigorous monotone-decay backbone behind the τ_c = 1/γ parameter in
the live `/api/<ns>/v1/qbio/coherence` endpoint.  It does NOT touch Conjecture 1:
Λ-v5 stays a PROPOSED engineering gate, the locked-proven set stays EXACTLY 8,
and Λ unconditional uniqueness stays Conjecture 1 (machine-checked FALSE).

## Honest status
PROPOSED / Wave24 candidate.  Becomes a CI-green EXPERIMENTAL theorem only when
`lake build` passes with no `sorry` and Lean-core axioms only.  Never folded
into the locked 8 by this file.

## Citations (load-bearing math)
  - Lindblad, G. (1976). "On the generators of quantum dynamical semigroups."
    Commun. Math. Phys. 48, 119–130.  doi:10.1007/BF01608499
  - Gorini, Kossakowski, Sudarshan (1976). J. Math. Phys. 17, 821.
    doi:10.1063/1.522979
  - Baumgratz, Cramer, Plenio (2014). "Quantifying Coherence."
    Phys. Rev. Lett. 113, 140401.  doi:10.1103/PhysRevLett.113.140401
    (l₁-norm coherence monotone C_{l₁}).
-/
import Mathlib

namespace Lutar.QuantumBio.CoherenceDecay

open Real

/-- l₁-norm coherence of a single qubit under pure dephasing:
    `C(t) = C₀ · exp (−γ t)`, the off-diagonal coherence mass.
    `C₀ = 2|ρ₁₂(0)| ≥ 0` is the initial coherence; `γ > 0` the dephasing rate
    (τ_c = 1/γ). -/
noncomputable def coh (C0 γ t : ℝ) : ℝ := C0 * Real.exp (-(γ * t))

/-- **Strict antitonicity.** With initial coherence `C₀ > 0` and dephasing rate
    `γ > 0`, the coherence `C(t)` is *strictly decreasing* in `t`: coherence is
    only ever lost, never spontaneously regained. -/
theorem coh_strictAnti (C0 γ : ℝ) (hC : 0 < C0) (hγ : 0 < γ) :
    StrictAnti (coh C0 γ) := by
  intro a b hab
  unfold coh
  -- exp is strictly monotone; -(γ * ·) is strictly antitone since γ > 0
  have hexp : Real.exp (-(γ * b)) < Real.exp (-(γ * a)) := by
    apply Real.exp_lt_exp.mpr
    have : γ * a < γ * b := by exact (mul_lt_mul_left hγ).mpr hab
    linarith
  exact (mul_lt_mul_left hC).mpr hexp

/-- Coherence is always nonnegative when the initial coherence is nonnegative. -/
theorem coh_nonneg (C0 γ t : ℝ) (hC : 0 ≤ C0) : 0 ≤ coh C0 γ t := by
  unfold coh
  exact mul_nonneg hC (le_of_lt (Real.exp_pos _))

/-- Coherence at `t = 0` equals the initial coherence. -/
@[simp] theorem coh_zero (C0 γ : ℝ) : coh C0 γ 0 = C0 := by
  unfold coh; simp

/-- **Limit:** coherence decays to `0` as `t → ∞` (for `γ > 0`). -/
theorem coh_tendsto_zero (C0 γ : ℝ) (hγ : 0 < γ) :
    Filter.Tendsto (coh C0 γ) Filter.atTop (nhds 0) := by
  unfold coh
  have h1 : Filter.Tendsto (fun t : ℝ => -(γ * t)) Filter.atTop Filter.atBot := by
    have : Filter.Tendsto (fun t : ℝ => γ * t) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hγ Filter.tendsto_id
    exact Filter.tendsto_neg_atTop_atBot.comp this
  have h2 : Filter.Tendsto (fun t : ℝ => Real.exp (-(γ * t))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp h1
  simpa using h2.const_mul C0

/-- The Λ-v5 engineering gate value at time `t` with charge held constant
    at `q`: `lambdaVal(t) = q · C(t)`. -/
noncomputable def lambdaAt (C0 γ q t : ℝ) : ℝ := q * coh C0 γ t

/-- **Single-crossing of the closure floor.** With `C₀ > 0`, `γ > 0`, charge
    `q > 0`, and a closure floor `lamMin` strictly between `0` and the initial
    gate value `q·C₀`, there is a *unique* time `t⋆` at which the Λ-v5 gate value
    exactly meets the floor, and `t⋆ = (1/γ)·ln(q·C₀ / lamMin) > 0`.
    Past `t⋆` the gate has fallen below the floor and never recovers
    (strict antitonicity) — the honest dynamical content behind
    `closureOk`/`decohered_never_closes`. -/
theorem lambda_single_crossing
    (C0 γ q lamMin : ℝ) (hC : 0 < C0) (hγ : 0 < γ) (hq : 0 < q)
    (hlo : 0 < lamMin) (hhi : lamMin < q * C0) :
    ∃ tStar : ℝ, 0 < tStar ∧ lambdaAt C0 γ q tStar = lamMin := by
  refine ⟨(1 / γ) * Real.log (q * C0 / lamMin), ?_, ?_⟩
  · -- t⋆ > 0 since the log of a quantity > 1 is positive and 1/γ > 0
    have hratio : 1 < q * C0 / lamMin := by
      rw [lt_div_iff hlo]; linarith
    have hlogpos : 0 < Real.log (q * C0 / lamMin) := Real.log_pos hratio
    positivity
  · -- evaluate q · C₀ · exp(−γ · t⋆) = lamMin
    unfold lambdaAt coh
    have hγ0 : γ ≠ 0 := ne_of_gt hγ
    have hpos : 0 < q * C0 / lamMin := by positivity
    -- −(γ * ((1/γ) * log r)) = − log r
    have hexp : Real.exp (-(γ * ((1 / γ) * Real.log (q * C0 / lamMin))))
        = lamMin / (q * C0) := by
      have : γ * ((1 / γ) * Real.log (q * C0 / lamMin))
          = Real.log (q * C0 / lamMin) := by
        field_simp
      rw [this, ← Real.log_inv, Real.exp_log]
      · rw [inv_div]
      · rw [inv_div]; positivity
    rw [hexp]
    have hq0 : q ≠ 0 := ne_of_gt hq
    have hC0' : C0 ≠ 0 := ne_of_gt hC
    field_simp
    ring

end Lutar.QuantumBio.CoherenceDecay
