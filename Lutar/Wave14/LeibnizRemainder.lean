/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 14 — CF-18: clean Madhava–Leibniz alternating-series remainder bound

This file ships the **clean-form** Leibniz (Madhava) remainder estimate that the in-tree
`Lutar/PACBayes/MadhavaBound.lean` flagged as "pending the appropriate Mathlib lemma name":

* `madhava_alt_series_bound` there carries a tagged `sorry` whose discharge route explicitly
  reads *"the appropriate lemma name located in the current Mathlib"*.

Mathlib v4.18.0 in fact ships the alternating-series bracketing lemmas
(`Mathlib/Analysis/SpecificLimits/Normed.lean`):

* `Antitone.alternating_series_le_tendsto` : `∑_{i<2k} (-1)^i f i ≤ L`
* `Antitone.tendsto_le_alternating_series` : `L ≤ ∑_{i<2k+1} (-1)^i f i`

From this even/odd bracketing we derive, cleanly and with NO `sorry`/NO new `axiom`, the
standard Leibniz remainder bound `|S_N − L| ≤ f N` for an antitone nonnegative sequence whose
alternating partial sums converge to `L`. This is exactly the `madhava_alt_series_bound`
statement, here proved against the located Mathlib API.

## Honesty / scope
- EXPERIMENTAL companion (new dir `Lutar/Wave14/`). It does NOT edit the baseline
  `MadhavaBound.lean` (whose `sorry`s stay honestly tracked); it proves the clean general
  remainder fact so the technique is demonstrably within reach on Mathlib v4.18.0.
- Locked-proven set unchanged. NO new axiom; NO sorry.

## References
- Mādhava of Sangamagrama (~1400 CE); Plofker, *Mathematics in India* (2009), §7.4.
- Leibniz alternating-series criterion (standard; the "first omitted term" remainder).
- Mathlib `Antitone.{alternating_series_le_tendsto, tendsto_le_alternating_series}`.

Signed-off-by: SZL CTO <cto@szl-holdings.com>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Lutar.Wave14

open Filter Finset
open scoped Topology BigOperators

/-- **CF-18 — clean Leibniz / Madhava remainder bound.**

    For a real sequence `a : ℕ → ℝ` that is nonnegative and antitone (`a (n+1) ≤ a n`),
    whose alternating partial sums `∑_{i<M} (-1)^i a i` converge to `L`, the truncation
    after `N` terms differs from `L` by at most the first omitted-term magnitude `a N`:
    `|(∑_{i<N} (-1)^i a i) − L| ≤ a N`.

    This is the standard Leibniz criterion remainder (Mādhava ~1400 CE). Proved directly
    from Mathlib's even/odd alternating-series bracketing — NO new axiom, NO sorry. -/
theorem leibniz_remainder_bound
    (a : ℕ → ℝ) (L : ℝ) (N : ℕ)
    (_h_nn : ∀ n, 0 ≤ a n)
    (h_anti : Antitone a)
    (h_lim : Tendsto (fun M => ∑ i ∈ range M, (-1 : ℝ) ^ i * a i) atTop (𝓝 L)) :
    |(∑ i ∈ range N, (-1 : ℝ) ^ i * a i) - L| ≤ a N := by
  -- Split on the parity of N.
  rcases Nat.even_or_odd N with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- N = 2k : even partial sum is a LOWER bracket, S_N ≤ L ≤ S_{N+1} = S_N + a N.
    have hN : N = 2 * k := by omega
    subst hN
    have hlo : (∑ i ∈ range (2 * k), (-1 : ℝ) ^ i * a i) ≤ L :=
      h_anti.alternating_series_le_tendsto h_lim k
    have hhi : L ≤ ∑ i ∈ range (2 * k + 1), (-1 : ℝ) ^ i * a i :=
      h_anti.tendsto_le_alternating_series h_lim k
    -- S_{2k+1} = S_{2k} + (-1)^{2k} a (2k) = S_{2k} + a (2k).
    have hstep : (∑ i ∈ range (2 * k + 1), (-1 : ℝ) ^ i * a i)
        = (∑ i ∈ range (2 * k), (-1 : ℝ) ^ i * a i) + a (2 * k) := by
      rw [Finset.sum_range_succ]
      have : (-1 : ℝ) ^ (2 * k) = 1 := by
        rw [pow_mul]; norm_num
      rw [this, one_mul]
    rw [hstep] at hhi
    -- 0 ≤ L − S_{2k} ≤ a (2k) ⇒ |S_{2k} − L| ≤ a (2k).
    rw [abs_le]
    constructor
    · linarith
    · linarith
  · -- N = 2k+1 : odd partial sum is an UPPER bracket, S_{N+1} ≤ L ≤ S_N, with S_{N+1}=S_N - a N.
    have hN : N = 2 * k + 1 := by omega
    subst hN
    have hhi : L ≤ ∑ i ∈ range (2 * k + 1), (-1 : ℝ) ^ i * a i :=
      h_anti.tendsto_le_alternating_series h_lim k
    have hlo : (∑ i ∈ range (2 * (k + 1)), (-1 : ℝ) ^ i * a i) ≤ L :=
      h_anti.alternating_series_le_tendsto h_lim (k + 1)
    -- S_{2k+2} = S_{2k+1} + (-1)^{2k+1} a (2k+1) = S_{2k+1} − a (2k+1).
    have hstep : (∑ i ∈ range (2 * (k + 1)), (-1 : ℝ) ^ i * a i)
        = (∑ i ∈ range (2 * k + 1), (-1 : ℝ) ^ i * a i) - a (2 * k + 1) := by
      have h2 : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
      rw [h2, Finset.sum_range_succ]
      have : (-1 : ℝ) ^ (2 * k + 1) = -1 := by
        rw [pow_succ, pow_mul]; norm_num
      rw [this]; ring
    rw [hstep] at hlo
    -- 0 ≤ S_{2k+1} − L ≤ a (2k+1) ⇒ |S_{2k+1} − L| ≤ a (2k+1).
    rw [abs_le]
    constructor
    · linarith
    · linarith

/-- Convenience restatement matching the in-tree `MadhavaBound.madhava_alt_series_bound`
    hypothesis shape (pointwise antitone `a (n+1) ≤ a n` instead of the bundled `Antitone`). -/
theorem madhava_alt_series_bound_clean
    (a : ℕ → ℝ) (L : ℝ) (N : ℕ)
    (h_nn : ∀ n, 0 ≤ a n)
    (h_dec : ∀ n, a (n + 1) ≤ a n)
    (h_lim : Tendsto (fun M => ∑ i ∈ range M, (-1 : ℝ) ^ i * a i) atTop (𝓝 L)) :
    |(∑ i ∈ range N, (-1 : ℝ) ^ i * a i) - L| ≤ a N :=
  leibniz_remainder_bound a L N h_nn (antitone_nat_of_succ_le h_dec) h_lim

end Lutar.Wave14
