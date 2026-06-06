/-
# WAVE 6 — C3 Hoeffding / C4 Azuma–Hoeffding / C5 Gibbs (KL ≥ 0)

  (Mathlib-DEPENDENT — verified by lutar-lean CI `lake build`, NOT by bare `lean`
   here: Mathlib does not fit the sandbox disk.)

These three were honestly BLOCKED at the prior pinned Mathlib `d7317655` (v4.13.0)
because the two modules that DEFINE the needed API were HTTP 404 there:
  * `Mathlib.Probability.Moments.SubGaussian`            (added after v4.13.0)
  * `Mathlib.InformationTheory.KullbackLeibler.Basic`    (added after v4.13.0)

This module lands them after the toolchain bump to **Mathlib v4.18.0**
(rev `aa936c36e8484abd300577139faf8e945850831a`, Lean `v4.18.0`), the EARLIEST tagged
release that contains BOTH files (HTTP-200 evidence in team/MATHLIB_BUMP_REPORT.md):
  * SubGaussian.lean           first present at v4.18.0
  * KullbackLeibler/Basic.lean first present at v4.17.0

Each result is a pure term-mode re-export: signature verified character-for-character
against the v4.18.0 source. Zero new mathematical risk — the math is machine-checked in
standard Mathlib; we only instantiate. Expected `#print axioms` dependencies are the
standard Mathlib trio `[propext, Classical.choice, Quot.sound]` (NO `sorryAx`, NO declared
Lutar axioms). The actual `#print axioms` output is captured in the CI build log.

## Honesty / doctrine (Doctrine v11)
- Locked v11 kernel (749/14/163 @ c7c0ba17) is SEPARATE and UNCHANGED; `locked_proven` = 5.
  This module is the EXPERIMENTAL scope (wave-6), not folded into the locked baseline.
- Λ (F23) stays Conjecture 1 unconditionally; nothing here touches it.
- `proven` ONLY once CI `lake build` is green (Mathlib-dependent).

## Citations & Mathlib paths (verified present at v4.18.0 = aa936c36)
- C3 Hoeffding: `ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`
  (Mathlib.Probability.Moments.SubGaussian). Hoeffding (1963), JASA 58:13–30,
  doi:10.1080/01621459.1963.10500830.
- C4 Azuma–Hoeffding:
  `ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_HasCondSubgaussianMGF`
  (same file). Azuma (1967), Tôhoku Math. J. 19:357–367, doi:10.2748/tmj/1178243286;
  Hoeffding (1963).
- C5 Gibbs (KL ≥ 0): `InformationTheory.integral_llr_add_sub_measure_univ_nonneg`
  (Mathlib.InformationTheory.KullbackLeibler.Basic). Gibbs' inequality; Kullback–Leibler
  (1951), Ann. Math. Statist. 22:79–86, doi:10.1214/aoms/1177729694.

## Substrate use
- C3 Hoeffding: a11oy/killinchu finite-sample trust concentration — the empirical sum of
  independent bounded-difference (sub-Gaussian) trust signals exceeds its mean by `ε`
  with probability ≤ `exp(-ε²/(2 Σcᵢ))` (distribution-free tail bound for trust estimates).
- C4 Azuma–Hoeffding: UDS receipt-stream / sequential-audit concentration — for a
  martingale-difference (conditionally sub-Gaussian) accumulator adapted to the audit
  filtration, the running sum has the same sub-Gaussian tail (anti-gaming bound for
  adaptively-generated receipt streams).
- C5 Gibbs (KL ≥ 0): a11oy active-inference / DPO grounding — the Kullback–Leibler
  divergence between the policy and the reference measure is nonnegative (the integral
  form `∫ llr dμ + ν(univ) − μ(univ) ≥ 0`), the variational floor underneath the
  free-energy / ELBO objective.
-/
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.InformationTheory.KullbackLeibler.Basic

namespace Wave6.SubGaussianKL

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal BigOperators

/-! ## C3 — Hoeffding's inequality for sums of independent sub-Gaussian variables. -/

/-- **C3 — Hoeffding inequality.** For a finite family `X : ι → Ω → ℝ` of independent
    random variables, each sub-Gaussian with parameter `c i`, the probability that the
    sum `∑ i ∈ s, X i` is at least `ε ≥ 0` is bounded by `exp(-ε² / (2 ∑ i ∈ s, c i))`.
    Direct instantiation of
    `ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`. -/
theorem c3_hoeffding_sum_ge_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {c : ι → ℝ≥0} {s : Finset ι}
    (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ) {ε : ℝ} (hε : 0 ≤ ε) :
    (μ {ω | ε ≤ ∑ i ∈ s, X i ω}).toReal ≤ Real.exp (- ε ^ 2 / (2 * ∑ i ∈ s, c i)) :=
  HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun h_indep h_subG hε

/-! ## C4 — Azuma–Hoeffding inequality for sub-Gaussian martingale differences. -/

/-- **C4 — Azuma–Hoeffding inequality.** Let `Y : ℕ → Ω → ℝ` be a process adapted to a
    filtration `ℱ`, with `Y 0` sub-Gaussian (parameter `cY 0`) and each later increment
    `Y (i+1)` conditionally sub-Gaussian (parameter `cY (i+1)`) given `ℱ i`. Then the
    running sum over `range n` exceeds `ε ≥ 0` with probability
    ≤ `exp(-ε² / (2 ∑ i ∈ range n, cY i))`. Direct instantiation of
    `ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_HasCondSubgaussianMGF`. -/
theorem c4_azuma_hoeffding_sum_ge_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [StandardBorelSpace Ω] [IsZeroOrProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {cY : ℕ → ℝ≥0} {ℱ : Filtration ℕ mΩ}
    (h_adapted : Adapted ℱ Y) (h0 : HasSubgaussianMGF (Y 0) (cY 0) μ) (n : ℕ)
    (h_subG : ∀ i < n - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (cY (i + 1)) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μ {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω}).toReal
      ≤ Real.exp (- ε ^ 2 / (2 * ∑ i ∈ Finset.range n, cY i)) :=
  -- NOTE: this lemma lives directly in `ProbabilityTheory` (in `section Martingale`,
  -- AFTER `end HasSubgaussianMGF`), NOT under the `HasSubgaussianMGF` namespace —
  -- unlike the C3 Hoeffding lemma. So it is referenced WITHOUT the `HasSubgaussianMGF.`
  -- prefix (we `open ProbabilityTheory`).
  measure_sum_ge_le_of_HasCondSubgaussianMGF h_adapted h0 n h_subG hε

/-! ## C5 — Gibbs' inequality: the Kullback–Leibler divergence is nonnegative. -/

/-- **C5 — Gibbs inequality (KL ≥ 0).** For finite measures `μ ≪ ν` with `llr μ ν`
    integrable, the integral form of the Kullback–Leibler divergence is nonnegative:
    `0 ≤ ∫ x, llr μ ν x ∂μ + (ν univ).toReal − (μ univ).toReal`. Direct instantiation of
    `InformationTheory.integral_llr_add_sub_measure_univ_nonneg`. -/
theorem c5_gibbs_kl_nonneg
    {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    0 ≤ ∫ x, llr μ ν x ∂μ + (ν Set.univ).toReal - (μ Set.univ).toReal :=
  InformationTheory.integral_llr_add_sub_measure_univ_nonneg hμν h_int

end Wave6.SubGaussianKL

-- ## Axiom disclosure (CI prints these in the build log).
-- All three are pure instantiations of Mathlib theorems; expected dependencies are the
-- standard Mathlib trio [propext, Classical.choice, Quot.sound] (NO sorryAx, NO declared
-- Lutar axioms). The #print axioms output is captured in the CI build log.
#print axioms Wave6.SubGaussianKL.c3_hoeffding_sum_ge_le
#print axioms Wave6.SubGaussianKL.c4_azuma_hoeffding_sum_ge_le
#print axioms Wave6.SubGaussianKL.c5_gibbs_kl_nonneg
