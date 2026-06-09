import Mathlib

namespace Lutar.Putnam.Sampler

/-!
# Sampler Problem 7 (Analysis / harmonic vs logarithm)

**Problem (PDF):** Prove the partial harmonic sum dominates the logarithm:
`∑_{k=1}^{n} 1/k ≥ ln(n+1)`.

**Proof (telescoping):** For each `k ≥ 0`, `ln(k+2) - ln(k+1) = ln((k+2)/(k+1)) ≤ (k+2)/(k+1) - 1
= 1/(k+1)` using `Real.log x ≤ x - 1`. Summing `k = 0 … n-1` telescopes the left side to
`ln(n+1) - ln 1 = ln(n+1)`, giving `ln(n+1) ≤ ∑_{k=0}^{n-1} 1/(k+1) = ∑_{j=1}^{n} 1/j`.

**Difficulty:** 3.
**Status:** KERNEL-VERIFIED (sorry-free).
-/

theorem p07 (n : ℕ) :
    Real.log ((n : ℝ) + 1) ≤ ∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have hne : ((m : ℝ) + 1) ≠ 0 := by positivity
      have hstep : Real.log ((m : ℝ) + 2) - Real.log ((m : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
        have hd : Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) ≤ ((m : ℝ) + 2) / ((m : ℝ) + 1) - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        rw [Real.log_div (by positivity) hne] at hd
        have he : ((m : ℝ) + 2) / ((m : ℝ) + 1) - 1 = 1 / ((m : ℝ) + 1) := by
          have h2 : ((m : ℝ) + 2) = ((m : ℝ) + 1) + 1 := by ring
          rw [h2, add_div, div_self hne]; ring
        linarith [hd, he]
      have hL : Real.log (((m + 1 : ℕ) : ℝ) + 1) = Real.log ((m : ℝ) + 2) := by
        congr 1; push_cast; ring
      rw [hL]
      linarith [hstep, ih]

end Lutar.Putnam.Sampler
