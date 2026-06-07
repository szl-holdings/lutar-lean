/-
Copyright © 2026 Stephen P. Lutar Jr. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave11/ImmuneNeymanPearsonOpt.lean — CF-5 discrete core (Frontier)

Neyman-Pearson-optimal immune egress gate — DISCRETE / FINITE core.

The sentra immune system is a fail-closed (deny-by-default) decision rule.
We model an egress gate as a (possibly randomised, here deterministic 0/1)
test `φ : Ω → ℝ≥0` over a finite outcome space `Ω`, with a benign distribution
`p₀` (null `H₀`) and a hostile distribution `p₁` (alternative `H₁`).

  - false-positive (over-block) mass  =  ∑ φ(ω)·p₀(ω)   (Type I, α)
  - detection (power) mass            =  ∑ φ(ω)·p₁(ω)
  - false-negative (missed)           =  1 − detection  (Type II, β)

**Neyman-Pearson lemma (finite form).** Let `Λ(ω) = p₁(ω)/p₀(ω)` be the
likelihood ratio and let `φ⋆` be a likelihood-ratio test that accepts (`= 1`)
where `Λ ≥ t` and rejects (`= 0`) where `Λ < t`.  Then for any competing test
`φ` with NO MORE false positives than `φ⋆` (`FP(φ) ≤ FP(φ⋆)`), the LRT has at
least as much detection power (`detect(φ) ≤ detect(φ⋆)`), hence NO MORE
false-negatives.  The LRT is the most-powerful test at its size.

The crux is the pointwise sign lemma: for every outcome `ω`,
`(φ⋆(ω) − φ(ω)) · (p₁(ω) − t·p₀(ω)) ≥ 0`, because on the acceptance region
`φ⋆ = 1 ≥ φ` and `p₁ − t·p₀ ≥ 0`, and on the rejection region `φ⋆ = 0 ≤ φ`
and `p₁ − t·p₀ ≤ 0`.  Summing gives the result.

## What is proven (kernel-clean, no sorry/admit/axiom)

- `LRTest` — a likelihood-ratio (threshold) test bundle over a `Fintype Ω`.
- `np_pointwise_nonneg` — the pointwise sign lemma (heart of NP).
- `neyman_pearson_most_powerful` — **CF-5 main (discrete)**: the LRT maximises
  detection among all `[0,1]`-tests with FP ≤ FP(LRT) ⇒ minimises β.
- `neyman_pearson_min_false_negative` — restatement as a Type-II (missed
  intrusion) minimality contract `β(φ⋆) ≤ β(φ)` (with total-mass-1 hostile dist).
- `fail_closed_zero_test` — the all-deny test has zero false positives (the
  deny-by-default β-safe boundary), recovering the round9 fail-closed key.

## Honesty / scope
- This is the **DISCRETE/finite-measure** Neyman-Pearson optimality core.  The
  **measure-theoretic Gaussian-shift** version that would close `sorry₁` in
  `Lutar/Robustness/CertifiedRadius.lean` (Radon–Nikodym + the Gaussian family)
  remains OPEN / roadmap (it needs lemmas not in Mathlib v4.18.0).  We do NOT
  claim that sorry closed; we close the *discrete optimality* obligation behind
  `Lutar/Innovations/round9/ImmuneNeymanPearson.lean` (which had only the
  ordering/fail-closed keys, not optimality).
- EXPERIMENTAL (`Lutar.Wave11`) — ADDITIVE, NOT in the LOCKED v11 baseline.
  Locked stays EXACTLY 5 {F1,F11,F12,F18,F19}. Λ Conjecture 1. NOT in Lutar.lean.
- NO new declared axiom, NO sorry.

## Citations
- Neyman, J. & Pearson, E.S. (1933). "On the Problem of the Most Efficient
  Tests of Statistical Hypotheses." Phil. Trans. R. Soc. A 231:289–337.
  DOI:10.1098/rsta.1933.0009.
- Cohen, Rosenfeld, Kolter (2019). "Certified Adversarial Robustness via
  Randomized Smoothing." ICML 2019. arXiv:1902.02918 (NP for Gaussian shifts).

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Lutar.Wave11.ImmuneNeymanPearsonOpt

open Finset

variable {Ω : Type*} [Fintype Ω]

/-- A likelihood-ratio (threshold) test over a finite outcome space.
    `p0` = benign (null `H₀`) weights, `p1` = hostile (alt `H₁`) weights, `t`
    the LR threshold.  `φstar` is the test: it accepts (`1`) exactly where the
    LR favours `H₁` (`p1 ≥ t·p0`) and rejects (`0`) otherwise.  All real-valued
    masses; weights nonneg. -/
structure LRTest (Ω : Type*) [Fintype Ω] where
  p0    : Ω → ℝ
  p1    : Ω → ℝ
  t     : ℝ
  φstar : Ω → ℝ
  hp0   : ∀ ω, 0 ≤ p0 ω
  ht    : 0 ≤ t
  /-- `φstar` is a `[0,1]` indicator. -/
  φstar01 : ∀ ω, φstar ω = 0 ∨ φstar ω = 1
  /-- Accept region: LR favours H₁. -/
  accept : ∀ ω, φstar ω = 1 → t * (p0 ω) ≤ p1 ω
  /-- Reject region: LR favours H₀. -/
  reject : ∀ ω, φstar ω = 0 → p1 ω ≤ t * (p0 ω)

/-- False-positive (over-block) mass of a test `φ` under the benign dist. -/
def falsePos (L : LRTest Ω) (φ : Ω → ℝ) : ℝ := ∑ ω, φ ω * L.p0 ω

/-- Detection (power) mass of a test `φ` under the hostile dist. -/
def detect (L : LRTest Ω) (φ : Ω → ℝ) : ℝ := ∑ ω, φ ω * L.p1 ω

/-- **Pointwise sign lemma — the heart of Neyman-Pearson.**
    For the LRT `φstar` and any competing `[0,1]`-test `φ`,
    `(φstar ω − φ ω) · (p1 ω − t·p0 ω) ≥ 0` at every outcome. -/
theorem np_pointwise_nonneg (L : LRTest Ω) (φ : Ω → ℝ)
    (hφ : ∀ ω, 0 ≤ φ ω ∧ φ ω ≤ 1) (ω : Ω) :
    0 ≤ (L.φstar ω - φ ω) * (L.p1 ω - L.t * L.p0 ω) := by
  rcases L.φstar01 ω with h0 | h1
  · -- φstar ω = 0 ⇒ reject region: p1 − t·p0 ≤ 0 and φstar − φ = -φ ≤ 0
    have hr : L.p1 ω ≤ L.t * L.p0 ω := L.reject ω h0
    have hfac2 : L.p1 ω - L.t * L.p0 ω ≤ 0 := by linarith
    have hfac1 : L.φstar ω - φ ω ≤ 0 := by
      rw [h0]; linarith [(hφ ω).1]
    -- product of two nonpositives: rewrite via neg_mul_neg
    have := mul_nonneg (neg_nonneg.mpr hfac1) (neg_nonneg.mpr hfac2)
    rwa [neg_mul_neg] at this
  · -- φstar ω = 1 ⇒ accept region: p1 − t·p0 ≥ 0 and φstar − φ = 1 − φ ≥ 0
    have ha : L.t * L.p0 ω ≤ L.p1 ω := L.accept ω h1
    have hfac2 : 0 ≤ L.p1 ω - L.t * L.p0 ω := by linarith
    have hfac1 : 0 ≤ L.φstar ω - φ ω := by
      rw [h1]; linarith [(hφ ω).2]
    exact mul_nonneg hfac1 hfac2

/-- **CF-5 MAIN (discrete Neyman-Pearson).**  Among all `[0,1]`-tests `φ` whose
    false-positive mass does not exceed the LRT's, the LRT has at least as much
    detection power.  Equivalently, the likelihood-ratio test is most powerful
    at its size — it minimises the missed-intrusion (Type II) rate. -/
theorem neyman_pearson_most_powerful (L : LRTest Ω) (φ : Ω → ℝ)
    (hφ : ∀ ω, 0 ≤ φ ω ∧ φ ω ≤ 1)
    (hsize : falsePos L φ ≤ falsePos L L.φstar) :
    detect L φ ≤ detect L L.φstar := by
  -- 0 ≤ ∑ (φstar − φ)·(p1 − t·p0)
  --   = (detect φstar − detect φ) − t·(falsePos φstar − falsePos φ)
  have hsum_nonneg :
      0 ≤ ∑ ω, (L.φstar ω - φ ω) * (L.p1 ω - L.t * L.p0 ω) :=
    Finset.sum_nonneg (fun ω _ => np_pointwise_nonneg L φ hφ ω)
  -- expand the sum into the four detect/falsePos sums.
  -- ∑ (φstar−φ)(p1−t·p0)
  --   = ∑ φstar·p1 − ∑ φ·p1 − t·(∑ φstar·p0 − ∑ φ·p0)
  have hexpand :
      (∑ ω, (L.φstar ω - φ ω) * (L.p1 ω - L.t * L.p0 ω))
        = (∑ ω, (L.φstar ω * L.p1 ω - φ ω * L.p1 ω))
          - L.t * ∑ ω, (L.φstar ω * L.p0 ω - φ ω * L.p0 ω) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    ring
  -- rewrite the detect/falsePos defs as the paired sums
  have hdetect :
      detect L L.φstar - detect L φ
        = ∑ ω, (L.φstar ω * L.p1 ω - φ ω * L.p1 ω) := by
    simp only [detect, Finset.sum_sub_distrib]
  have hfp :
      falsePos L L.φstar - falsePos L φ
        = ∑ ω, (L.φstar ω * L.p0 ω - φ ω * L.p0 ω) := by
    simp only [falsePos, Finset.sum_sub_distrib]
  rw [hexpand, ← hdetect, ← hfp] at hsum_nonneg
  -- t·(FP φstar − FP φ) ≥ 0 since t ≥ 0 and FP φ ≤ FP φstar
  have ht_term : 0 ≤ L.t * (falsePos L L.φstar - falsePos L φ) :=
    mul_nonneg L.ht (by linarith)
  linarith

/-- **CF-5 — Type-II (missed-intrusion) minimality contract.**  If the hostile
    distribution has total mass `1` (a probability distribution), then the LRT's
    false-negative mass `β(φ⋆) = 1 − detect(φ⋆)` is no larger than any competing
    test's, given equal-or-smaller false-positive mass: `β(φ⋆) ≤ β(φ)`. -/
theorem neyman_pearson_min_false_negative (L : LRTest Ω) (φ : Ω → ℝ)
    (hφ : ∀ ω, 0 ≤ φ ω ∧ φ ω ≤ 1)
    (hsize : falsePos L φ ≤ falsePos L L.φstar) :
    (1 - detect L L.φstar) ≤ (1 - detect L φ) := by
  have := neyman_pearson_most_powerful L φ hφ hsize
  linarith

/-- **CF-5 — fail-closed (deny-by-default) zero-α boundary.**  The all-deny test
    `φ ≡ 0` has zero false-positive (over-block of benign traffic interpreted as
    blocks) — here, zero detection-style mass under the benign distribution —
    recovering the round9 fail-closed key as a degenerate but valid endpoint. -/
theorem fail_closed_zero_test (L : LRTest Ω) :
    falsePos L (fun _ => 0) = 0 := by
  simp only [falsePos, zero_mul, Finset.sum_const_zero]

end Lutar.Wave11.ImmuneNeymanPearsonOpt

-- ## CF-5 axiom disclosure (discrete core).  Expected kernel-only
-- [propext, Classical.choice, Quot.sound] (or fewer). NO sorryAx, NO axioms.
#print axioms Lutar.Wave11.ImmuneNeymanPearsonOpt.np_pointwise_nonneg
#print axioms Lutar.Wave11.ImmuneNeymanPearsonOpt.neyman_pearson_most_powerful
#print axioms Lutar.Wave11.ImmuneNeymanPearsonOpt.neyman_pearson_min_false_negative
#print axioms Lutar.Wave11.ImmuneNeymanPearsonOpt.fail_closed_zero_test
