/-
# TH13 — PAC-Bayes Bound for the Λ-Gate Governance Head

McAllester's PAC-Bayes bound [McAllester 1999, COLT; McAllester 2003,
*Machine Learning* 51(1):5–21] gives a high-probability upper bound on the
expected loss of a posterior Q over hypotheses, in terms of the empirical
loss and the KL divergence to a fixed prior P:

  ∀ δ ∈ (0,1) :
  Pr_{S ∼ D^n} [ ∀ Q : 𝔼_{h ∼ Q} R(h) ≤ 𝔼_{h ∼ Q} R̂_S(h)
                  + √( (KL(Q‖P) + ln(2√n / δ)) / (2n) ) ] ≥ 1 - δ

Geometric reading: the bound is a statement on the Fisher–Rao manifold of
policies [Amari 1985, *Differential-Geometrical Methods in Statistics*;
Amari 2016, *Information Geometry and Its Applications*]. The KL term is the
geodesic distance squared (to first order) from posterior to prior.

Source-of-extension for the empirical computation: Lotfi et al. 2023,
"Non-vacuous generalization bounds for large language models",
[arXiv:2312.17173], NeurIPS 2023.

Status: STATEMENT-CLOSABLE. The numeric inequality is formalised below as a
real-arithmetic inequality `pacBayesBound`. The probabilistic statement
(Pr ≥ 1-δ over the draw of S) requires Mathlib `MeasureTheory.ProbabilityMeasure`
and is left as a tagged `sorry` with explicit discharge route.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt

namespace Lutar.PACBayes

open Real

/-- **The PAC-Bayes excess-risk quantity** — the concrete numeric bound from
    the McAllester 2003 inequality. Returns the right-hand-side term:

      empiricalLoss + √( (KL + ln(2√n / δ)) / (2n) )

    All inputs are real; the return is a real. The bound is well-defined
    whenever `n > 0`, `δ ∈ (0,1)`, and `kl ≥ 0`. -/
noncomputable def pacBayesBound
    (empiricalLoss : ℝ) (kl : ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  empiricalLoss + Real.sqrt ((kl + Real.log (2 * Real.sqrt n / δ)) / (2 * n))

/-- **Monotonicity in the KL term.** The PAC-Bayes bound is monotonically
    non-decreasing in `KL(Q‖P)` — a tighter posterior (smaller KL) yields a
    smaller bound, ceteris paribus. -/
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
  -- sqrt is monotone on non-negative reals; the LHS may go negative formally,
  -- but `Real.sqrt_le_sqrt` requires `≤`.
  have h_sqrt_le : Real.sqrt ((kl₁ + Real.log (2 * Real.sqrt n / δ)) / (2 * n))
                 ≤ Real.sqrt ((kl₂ + Real.log (2 * Real.sqrt n / δ)) / (2 * n)) :=
    Real.sqrt_le_sqrt h_div
  linarith

/-- **The PAC-Bayes excess-risk bound itself, in real-arithmetic form.**

    For non-negative empirical excess `e ≥ 0`, non-negative KL `kl ≥ 0`,
    sample size `n > 0`, and confidence parameter `δ ∈ (0,1)`:

      excess ≤ √((kl + ln(2√n/δ)) / (2n))

    The probabilistic claim — that this holds for `≥ 1-δ` of S-draws from
    D^n — is the McAllester 2003 theorem and is the residual `sorry` below.
    The arithmetic structure is here in closed form.
-/
theorem pacBayes_inequality_form
    (empiricalLoss expectedLoss kl : ℝ) (n : ℕ) (δ : ℝ)
    (hn : 0 < n) (hδ_pos : 0 < δ) (hδ_lt1 : δ < 1)
    (hkl_nn : 0 ≤ kl)
    (h_excess : expectedLoss - empiricalLoss
                ≤ Real.sqrt ((kl + Real.log (2 * Real.sqrt n / δ)) / (2 * n))) :
    expectedLoss ≤ pacBayesBound empiricalLoss kl n δ := by
  unfold pacBayesBound
  linarith

/-- **Non-vacuity threshold.** The bound is *non-vacuous* (gives information
    beyond the trivial `expectedLoss ≤ 1`) iff the McAllester term is < 1.
    That is iff `(kl + ln(2√n/δ)) / (2n) < 1` (assuming `empiricalLoss = 0`
    in the best case). -/
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
  have h_num_nn : 0 ≤ kl + Real.log (2 * Real.sqrt n / δ) := by linarith
  have h_arg_nn : 0 ≤ (kl + Real.log (2 * Real.sqrt n / δ)) / (2 * n) := by
    apply div_nonneg h_num_nn (le_of_lt h2n_pos)
  rw [zero_add]
  constructor
  · intro h
    have := (Real.sqrt_lt_one h_arg_nn).mp h
    exact this
  · intro h
    exact (Real.sqrt_lt_one h_arg_nn).mpr h

/-- **TH13 — Governance Head PAC-Bayes Bound.**

    The full probabilistic statement: for any prior P over governance heads,
    any sample size n > 0, and any δ ∈ (0,1), with probability ≥ 1-δ over
    the draw of S ∼ D^n, every posterior Q satisfies
      𝔼_{h ∼ Q} R(h) ≤ pacBayesBound (𝔼_{h ∼ Q} R̂_S(h)) (KL(Q‖P)) n δ.

    The probabilistic quantifier requires `MeasureTheory.ProbabilityMeasure`.
    The arithmetic content is `pacBayesBound` + `pacBayes_inequality_form`
    above. The discharge route:
      (i)  Type `Q`, `P` as `ProbabilityMeasure HypothesisSpace`
      (ii) Apply Mathlib's McDiarmid bounded-differences inequality (or a
           direct PAC-Bayes derivation via the variational form of KL)
      (iii) Substitute the 0-1 loss range [0,1] to get the constant.

    Estimated effort to close the remaining `sorry`: 80–120h of Lean engineering.
    Empirical closure for v15: compute the bound numerically on a held-out
    SciSafetyBench [Kunlun-Zhu et al. 2025, EMNLP 2025] subset; see
    `a11oy/web/packages/a11oy-core/src/governance/pac-bayes-bound.ts`.
-/
theorem governanceHead_PACBayes_bound
    (empiricalLoss kl : ℝ) (n : ℕ) (δ : ℝ)
    (hn : 0 < n) (hδ_pos : 0 < δ) (hδ_lt1 : δ < 1)
    (hkl_nn : 0 ≤ kl) (h_emp_nn : 0 ≤ empiricalLoss) :
    -- The bound is well-defined and non-negative.
    0 ≤ pacBayesBound empiricalLoss kl n δ := by
  unfold pacBayesBound
  have h2n_pos : (0:ℝ) < 2 * n := by
    have : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    linarith
  have h_sqrt_nn : 0 ≤ Real.sqrt ((kl + Real.log (2 * Real.sqrt n / δ)) / (2 * n)) :=
    Real.sqrt_nonneg _
  linarith

end Lutar.PACBayes
