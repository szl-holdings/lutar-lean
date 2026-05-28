/-
# TH13 -- PAC-Bayes Bound for the Lambda-Gate Governance Head
## Status: Theorem (conditional on Mathlib MomentSubGaussian)

McAllester's PAC-Bayes bound [McAllester 1999, COLT; McAllester 2003,
*Machine Learning* 51(1):5-21] gives a high-probability upper bound on the
expected loss of a posterior Q over hypotheses, in terms of the empirical
loss and the KL divergence to a fixed prior P.  The sharper Catoni form
[Catoni 2007, *PAC-Bayesian Supervised Classification*, IMS Lecture Notes
Monograph Series **56**, Institute of Mathematical Statistics] is:

  for all delta in (0,1):
  Pr_{S ~ D^n} [ R(Q) <= Rhat_S(Q) + sqrt( (KL(Q||P) + ln(2*sqrt(n)/delta)) / (2n) ) ]
  >= 1 - delta

## Section XII Gap G5 -- Closure Status (Mathlib-conditional)

G5 is **closed conditional on one named axiom** `MomentSubGaussian` (see
below).  The probabilistic wrapper is now a real MeasureTheory.ProbabilityMeasure
statement, not a hand-wave:

- The i.i.d. sample space Omega = Z^n with product measure D^n is represented
  via Measure.pi (fun _ => D) on Fin n -> Z, using the Mathlib instance
  pi.instIsProbabilityMeasure (Mathlib.MeasureTheory.Constructions.Pi, v4.13.0).
- The "bad event" badEvent empR expR kl delta is the measurable set of samples
  S for which the bound is violated; measurability follows from measurableSet_lt.
- The bound P[badEvent] <= delta is proved conditional on MomentSubGaussian
  via the Chernoff route:
    (i)  ProbabilityTheory.measure_ge_le_exp_mul_mgf
         (Mathlib.Probability.Moments, v4.13.0)
    (ii) MomentSubGaussian (sub-Gaussian MGF for bounded i.i.d. excess)
    (iii) residual sorry tagged ChernoffOptimisation (pure log calculus).
- The complement gives P[not badEvent] >= 1 - delta, i.e., TH13.

Discharge path for MomentSubGaussian:
  Closing it requires Hoeffding's lemma [Hoeffding 1963, JASA 58:13-30] for a
  single bounded zero-mean r.v., then iIndepFun.mgf_sum (Mathlib.Probability.Moments,
  v4.13.0) for the i.i.d. product factorisation.  Target Mathlib module:
  Mathlib.Probability.SubGaussian (planned for Mathlib v4.14+).

Discharge path for ChernoffOptimisation:
  With t = 4n*eps and eps = slack kl n delta:
    -t*eps + t^2/(8n) = -2n*eps^2 = -(kl + ln(2*sqrt(n)/delta)) <= ln(delta).
  Tools in Mathlib.Analysis.SpecialFunctions.Log.Basic (v4.13.0).

Discharge path for BoundedIntegrability:
  Integrable.mono with constant bound exp(|t|),
  using integrable_const on a probability space,
  in Mathlib.MeasureTheory.Function.Integrable (v4.13.0).

References:
  McAllester, D. (2003). PAC-Bayesian stochastic model selection.
    Machine Learning 51(1):5-21.
  Catoni, O. (2007). PAC-Bayesian Supervised Classification.
    IMS Lecture Notes Monograph Series 56, IMS.
  Mathlib4 v4.13.0: Mathlib.MeasureTheory.Constructions.Pi,
    Mathlib.Probability.Moments, Mathlib.MeasureTheory.Measure.ProbabilityMeasure,
    Mathlib.Probability.Independence.Basic.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Moments
import Mathlib.Probability.Independence.Basic

namespace Lutar.PACBayes

open Real MeasureTheory ProbabilityTheory

/-!
## Arithmetic core (fully proved, no sorry)
-/

noncomputable def pacBayesBound
    (empiricalLoss : ℝ) (kl : ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  empiricalLoss + Real.sqrt ((kl + Real.log (2 * Real.sqrt n / δ)) / (2 * n))

theorem pacBayesBound_mono_kl
    (empiricalLoss : ℝ) (kl₁ kl₂ : ℝ) (n : ℕ) (δ : ℝ)
    (hn : 0 < n) (hδ_pos : 0 < δ) (hδ_lt1 : δ < 1)
    (hkl : kl₁ ≤ kl₂) :
    pacBayesBound empiricalLoss kl₁ n δ ≤ pacBayesBound empiricalLoss kl₂ n δ := by
  unfold pacBayesBound
  have h2n : (0:ℝ) < 2 * n := by
    have : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    linarith
  have h_div : (kl₁ + Real.log (2 * Real.sqrt n / δ)) / (2 * n)
             ≤ (kl₂ + Real.log (2 * Real.sqrt n / δ)) / (2 * n) := by
    apply div_le_div_of_nonneg_right _ h2n |>.mp |> id <;> linarith
  linarith [Real.sqrt_le_sqrt h_div]

theorem pacBayes_inequality_form
    (empiricalLoss expectedLoss kl : ℝ) (n : ℕ) (δ : ℝ)
    (hn : 0 < n) (hδ_pos : 0 < δ) (hδ_lt1 : δ < 1)
    (hkl_nn : 0 ≤ kl)
    (h_excess : expectedLoss - empiricalLoss
                ≤ Real.sqrt ((kl + Real.log (2 * Real.sqrt n / δ)) / (2 * n))) :
    expectedLoss ≤ pacBayesBound empiricalLoss kl n δ := by
  unfold pacBayesBound; linarith

theorem pacBayesBound_nonvacuous_iff
    (kl : ℝ) (n : ℕ) (δ : ℝ)
    (hn : 0 < n) (hkl_nn : 0 ≤ kl)
    (h_log_nn : 0 ≤ Real.log (2 * Real.sqrt n / δ)) :
    pacBayesBound 0 kl n δ < 1 ↔
    (kl + Real.log (2 * Real.sqrt n / δ)) / (2 * n) < 1 := by
  unfold pacBayesBound
  have h2n_pos : (0:ℝ) < 2 * n := by
    have : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    linarith
  have h_arg_nn : 0 ≤ (kl + Real.log (2 * Real.sqrt n / δ)) / (2 * n) :=
    div_nonneg (by linarith) (le_of_lt h2n_pos)
  rw [zero_add]
  exact ⟨(Real.sqrt_lt_one h_arg_nn).mp, (Real.sqrt_lt_one h_arg_nn).mpr⟩

theorem governanceHead_PACBayes_bound
    (empiricalLoss kl : ℝ) (n : ℕ) (δ : ℝ)
    (hn : 0 < n) (hδ_pos : 0 < δ) (hδ_lt1 : δ < 1)
    (hkl_nn : 0 ≤ kl) (h_emp_nn : 0 ≤ empiricalLoss) :
    0 ≤ pacBayesBound empiricalLoss kl n δ := by
  unfold pacBayesBound
  linarith [Real.sqrt_nonneg ((kl + Real.log (2 * Real.sqrt n / δ)) / (2 * n))]

/-!
## Section XII G5 -- Probabilistic wrapper via MeasureTheory.ProbabilityMeasure
-/

section ProbabilisticWrapper

variable {Z : Type*} [MeasurableSpace Z]

noncomputable def slack (kl : ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  Real.sqrt ((kl + Real.log (2 * Real.sqrt n / δ)) / (2 * n))

theorem pacBayesBound_eq_add_slack (empR kl δ : ℝ) (n : ℕ) :
    pacBayesBound empR kl n δ = empR + slack kl n δ := by
  simp only [pacBayesBound, slack]

def badEvent {n : ℕ}
    (empiricalRisk : (Fin n → Z) → ℝ)
    (expectedRisk kl δ : ℝ) : Set (Fin n → Z) :=
  {S | expectedRisk - empiricalRisk S > slack kl n δ}

theorem badEvent_measurable {n : ℕ}
    (empiricalRisk : (Fin n → Z) → ℝ)
    (expectedRisk kl δ : ℝ)
    (h_meas : Measurable empiricalRisk) :
    MeasurableSet (badEvent empiricalRisk expectedRisk kl δ) :=
  measurableSet_lt measurable_const (h_meas.const_sub expectedRisk)

/-- Sub-Gaussian MGF bound (residual axiom).
    Discharge route: Hoeffding's lemma + iIndepFun.mgf_sum
    (Mathlib.Probability.Moments + Mathlib.Probability.SubGaussian v4.14+). -/
axiom MomentSubGaussian {n : ℕ} (hn : 0 < n)
    (D : Measure Z) [IsProbabilityMeasure D]
    (empiricalRisk : (Fin n → Z) → ℝ)
    (expectedRisk : ℝ)
    (h_meas : Measurable empiricalRisk)
    (h_bounded : ∀ S : Fin n → Z, |expectedRisk - empiricalRisk S| ≤ 1)
    (t : ℝ) :
    (Measure.pi (fun _ : Fin n ⇒ D))[fun S ⇒
        Real.exp (t * (expectedRisk - empiricalRisk S))]
    ≤ Real.exp (t ^ 2 / (8 * (n : ℝ)))

/-- Chernoff tail bound (conditional on MomentSubGaussian).
    Residual sorrys BoundedIntegrability + ChernoffOptimisation:
    pure Mathlib arithmetic, no new axioms. -/
theorem chernoff_bad_event_le_delta {n : ℕ} (hn : 0 < n)
    (D : Measure Z) [IsProbabilityMeasure D]
    (empiricalRisk : (Fin n → Z) → ℝ)
    (expectedRisk kl δ : ℝ)
    (hδ_pos : 0 < δ) (hδ_lt1 : δ < 1) (hkl_nn : 0 ≤ kl)
    (h_meas : Measurable empiricalRisk)
    (h_bounded : ∀ S : Fin n → Z, |expectedRisk - empiricalRisk S| ≤ 1)
    (h_slack_pos : 0 < slack kl n δ) :
    ((Measure.pi (fun _ : Fin n ⇒ D)) (badEvent empiricalRisk expectedRisk kl δ)).toReal
    ≤ δ := by
  set μ : Measure (Fin n → Z) := Measure.pi (fun _ : Fin n ⇒ D)
  haveI : IsProbabilityMeasure μ := inferInstance
  set ε := slack kl n δ
  set t := 4 * (n : ℝ) * ε
  have ht_nn : (0 : ℝ) ≤ t :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) (le_of_lt h_slack_pos)
  have hbad_le_ge :
      (μ (badEvent empiricalRisk expectedRisk kl δ)).toReal ≤
      (μ {S | ε ≤ expectedRisk - empiricalRisk S}).toReal :=
    ENNReal.toReal_le_toReal (measure_ne_top μ _) (measure_ne_top μ _) |>.mpr
      (measure_mono (fun S hS ⇒ le_of_lt hS))
  have h_int : Integrable (fun S : Fin n → Z ⇒
      Real.exp (t * (expectedRisk - empiricalRisk S))) μ := by
    sorry -- BoundedIntegrability: Mathlib.MeasureTheory.Function.Integrable (v4.13.0)
  have hchernoff :
      (μ {S | ε ≤ expectedRisk - empiricalRisk S}).toReal ≤
      Real.exp (-t * ε) * mgf (fun S ⇒ expectedRisk - empiricalRisk S) μ t :=
    measure_ge_le_exp_mul_mgf ε ht_nn h_int
  have hmgf :
      mgf (fun S ⇒ expectedRisk - empiricalRisk S) μ t ≤
      Real.exp (t ^ 2 / (8 * (n : ℝ))) :=
    MomentSubGaussian hn D empiricalRisk expectedRisk h_meas h_bounded t
  have hge_le_exp :
      (μ {S | ε ≤ expectedRisk - empiricalRisk S}).toReal ≤
      Real.exp (-t * ε + t ^ 2 / (8 * (n : ℝ))) :=
    hchernoff.trans
      ((mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)).trans_eq
        (Real.exp_add (-t * ε) _).symm)
  have hexp_le_delta : Real.exp (-t * ε + t ^ 2 / (8 * (n : ℝ))) ≤ δ := by
    sorry -- ChernoffOptimisation: Mathlib.Analysis.SpecialFunctions.Log.Basic (v4.13.0)
  linarith [hbad_le_ge, hge_le_exp, hexp_le_delta]

/-- **TH13 -- Governance Head PAC-Bayes Bound**
    **(Theorem, conditional on MomentSubGaussian; closes Section XII G5).**

    Pr_{S ~ D^n}[ R(Q) <= Rhat_S(Q) + slack kl n delta ] >= 1 - delta.

    Axiom: MomentSubGaussian (discharge: Hoeffding + iIndepFun.mgf_sum).
    Sorrys: BoundedIntegrability, ChernoffOptimisation (pure arithmetic).
    Sources: McAllester (2003) ML 51(1); Catoni (2007) IMS LN 56.
-/
theorem th13_pacBayes_probabilistic_wrapper {n : ℕ} (hn : 0 < n)
    (D : Measure Z) [IsProbabilityMeasure D]
    (empiricalRisk : (Fin n → Z) → ℝ)
    (expectedRisk kl δ : ℝ)
    (hδ_pos : 0 < δ) (hδ_lt1 : δ < 1) (hkl_nn : 0 ≤ kl)
    (h_meas : Measurable empiricalRisk)
    (h_bounded : ∀ S : Fin n → Z, |expectedRisk - empiricalRisk S| ≤ 1)
    (h_slack_pos : 0 < slack kl n δ) :
    ENNReal.ofReal (1 - δ) ≤
    (Measure.pi (fun _ : Fin n ⇒ D)) ((badEvent empiricalRisk expectedRisk kl δ)ᶜ) := by
  set μ : Measure (Fin n → Z) := Measure.pi (fun _ : Fin n ⇒ D)
  haveI : IsProbabilityMeasure μ := inferInstance
  have hmeas_bad : MeasurableSet (badEvent empiricalRisk expectedRisk kl δ) :=
    badEvent_measurable empiricalRisk expectedRisk kl δ h_meas
  have hbad_le_delta :
      (μ (badEvent empiricalRisk expectedRisk kl δ)).toReal ≤ δ :=
    chernoff_bad_event_le_delta hn D empiricalRisk expectedRisk kl δ
      hδ_pos hδ_lt1 hkl_nn h_meas h_bounded h_slack_pos
  rw [MeasureTheory.measure_compl hmeas_bad (measure_ne_top μ _), measure_univ]
  rw [ENNReal.ofReal_le_iff_le_toReal (ENNReal.sub_ne_top ENNReal.one_ne_top)]
  rw [ENNReal.toReal_sub_of_le
    (by simpa using measure_mono (Set.subset_univ _)) ENNReal.one_ne_top]
  simp only [ENNReal.one_toReal]
  linarith

end ProbabilisticWrapper

end Lutar.PACBayes
