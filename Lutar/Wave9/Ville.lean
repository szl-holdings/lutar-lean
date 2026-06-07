/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave9/Ville.lean — MC-4: Ville / Markov anytime-valid bound

The probabilistic heart of Ville's inequality for nonnegative supermartingales,
the workhorse of anytime-valid sequential inference and "betting" e-processes.
If `Z` is a nonnegative process with `𝔼[Z n] ≤ 1` (the supermartingale
expectation-decrease property gives `𝔼[Z n] ≤ 𝔼[Z 0] = 1`), then for any
threshold `α > 0` the chance the process reaches `1/α` at time `n` is at most `α`:

  `μ {ω | 1/α ≤ Z n ω} ≤ α`.

This is the **fixed-time** Ville/Markov bound, proven rigorously in Mathlib's
measure-theory framework from `mul_meas_ge_le_integral_of_nonneg` (Markov's
inequality) together with the supermartingale expectation bound
`Supermartingale.expectation_le_one` (derived from `Supermartingale.setIntegral_le`
over the whole space). The full TIME-UNIFORM supremum form
`μ {ω | ∃ n, 1/α ≤ Z n ω} ≤ α` (the maximal-inequality / optional-stopping
upgrade) is the documented ROADMAP extension; it requires Doob's maximal
inequality for supermartingales, which Mathlib currently states only for
submartingales (`maximal_ineq`). We ship the rigorous fixed-time core rather than
fabricate the supremum step.

## What is proven
- `Supermartingale.expectation_le_one` — a real-valued supermartingale `Z` with
  `∫ Z 0 ≤ 1` satisfies `∫ Z n ≤ 1` for every `n` (expectation is non-increasing).
- `ville_markov_bound` — for a NONNEGATIVE integrable `g` with `∫ g ≤ 1` and
  `α > 0`: `(μ {ω | 1/α ≤ g ω}).toReal ≤ α`. (Markov, the engine of Ville.)
- `ville_fixed_time` — packaged for a supermartingale `Z` with `∫ Z 0 ≤ 1` and
  `0 ≤ Z n`: `(μ {ω | 1/α ≤ Z n ω}).toReal ≤ α`.

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave9`) — NOT in the LOCKED v11 baseline. Locked-proven
  stays exactly 5 {F1,F11,F12,F18,F19}. Λ untouched (Conjecture 1).
- Known-theorem formalization (Ville 1939; Markov/Chebyshev). Backed by Mathlib.
- NO new declared axiom, NO sorry in any theorem body.
- Scope: the FIXED-TIME bound is fully proven; the TIME-UNIFORM supremum form is
  ROADMAP (see `ville_time_uniform_ROADMAP` note at the foot of the file). The
  nonnegative-supermartingale structure (independence, bounded increments, etc.)
  is a separate modeling obligation, per the MC-4 risk note.

## Citations
- Ville, "Étude critique de la notion de collectif" (1939) — Ville's inequality.
- "Admissible anytime-valid sequential inference must rely on nonnegative
  martingales", arXiv:2009.03167: https://arxiv.org/abs/2009.03167
- Howard et al., "Time-uniform Chernoff bounds via nonnegative supermartingales",
  Probability Surveys 17 (2020): https://projecteuclid.org/journals/probability-surveys/volume-17/issue-none/10.1214/18-PS321.full
- Mathlib martingale / Markov inequality:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Martingale/Basic.html

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Bochner

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Lutar.Wave9.Ville

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
variable {ℱ : Filtration ℕ m0}

/-- **Supermartingale expectation is non-increasing.** For a real-valued
supermartingale `Z` with `∫ Z 0 ∂μ ≤ 1`, every later expectation is `≤ 1`.
Uses `Supermartingale.setIntegral_le` over the whole space (`s = univ`). -/
theorem Supermartingale.expectation_le_one [SigmaFiniteFiltration μ ℱ]
    {Z : ℕ → Ω → ℝ} (hZ : Supermartingale Z ℱ μ) (h0 : ∫ ω, Z 0 ω ∂μ ≤ 1) :
    ∀ n, ∫ ω, Z n ω ∂μ ≤ 1 := by
  intro n
  have hmono : ∫ ω, Z n ω ∂μ ≤ ∫ ω, Z 0 ω ∂μ := by
    have h := hZ.setIntegral_le (i := 0) (j := n) (Nat.zero_le n)
      (s := Set.univ) MeasurableSet.univ
    simpa [setIntegral_univ] using h
  exact le_trans hmono h0

/-- **Markov bound (the engine of Ville's inequality).** For a nonnegative
integrable `g` with `∫ g ∂μ ≤ 1` and `α > 0`, the measure of `{1/α ≤ g}` is at
most `α`. Direct from Markov's inequality `mul_meas_ge_le_integral_of_nonneg`
with `ε = 1/α`. -/
theorem ville_markov_bound
    {g : Ω → ℝ} (hg_nonneg : 0 ≤ᵐ[μ] g) (hg_int : Integrable g μ)
    (hg_exp : ∫ ω, g ω ∂μ ≤ 1) {α : ℝ} (hα : 0 < α) :
    (μ {ω | 1 / α ≤ g ω}).toReal ≤ α := by
  -- Markov: (1/α) * (μ {1/α ≤ g}).toReal ≤ ∫ g ≤ 1.
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hg_nonneg hg_int (1 / α)
  -- so (1/α) * m ≤ 1, hence m ≤ α.
  have hle1 : (1 / α) * (μ {ω | 1 / α ≤ g ω}).toReal ≤ 1 := le_trans hmarkov hg_exp
  -- multiply both sides by α > 0:  m = α * ((1/α) * m) ≤ α * 1 = α.
  have hstep : α * ((1 / α) * (μ {ω | 1 / α ≤ g ω}).toReal) ≤ α * 1 :=
    mul_le_mul_of_nonneg_left hle1 hα.le
  calc (μ {ω | 1 / α ≤ g ω}).toReal
      = α * ((1 / α) * (μ {ω | 1 / α ≤ g ω}).toReal) := by
        field_simp
    _ ≤ α * 1 := hstep
    _ = α := by ring

/-- **MC-4 — Ville's inequality, fixed-time form.** For a nonnegative
supermartingale `Z` (normalized via `∫ Z 0 ∂μ ≤ 1`) and any `α > 0`, the
probability that `Z` reaches the level `1/α` at time `n` is at most `α`. -/
theorem ville_fixed_time [SigmaFiniteFiltration μ ℱ]
    {Z : ℕ → Ω → ℝ} (hZ : Supermartingale Z ℱ μ)
    (h0 : ∫ ω, Z 0 ω ∂μ ≤ 1) (n : ℕ) (hnonneg : 0 ≤ᵐ[μ] Z n)
    {α : ℝ} (hα : 0 < α) :
    (μ {ω | 1 / α ≤ Z n ω}).toReal ≤ α :=
  ville_markov_bound hnonneg (hZ.integrable n)
    (Supermartingale.expectation_le_one hZ h0 n) hα

#print axioms Supermartingale.expectation_le_one
#print axioms ville_markov_bound
#print axioms ville_fixed_time

/-
## ROADMAP (NOT in the proven set, intentionally not stated as a theorem)

`ville_time_uniform_ROADMAP`:
    μ {ω | ∃ n, 1/α ≤ Z n ω} ≤ α
is the TIME-UNIFORM (anytime-valid) supremum form. It upgrades the fixed-time
bound above via Doob's maximal inequality / optional stopping applied to the
nonnegative supermartingale. Mathlib currently provides `maximal_ineq` only for
nonnegative SUBmartingales (Mathlib/Probability/Martingale/OptionalStopping.lean),
so closing the supermartingale supremum form cleanly needs an auxiliary maximal
inequality. We do NOT ship a fabricated proof of this step.
-/

end Lutar.Wave9.Ville
