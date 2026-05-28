/-
# R4-I1 — Madhava alternating-series bound

Mādhava of Sangamagrama (~1340–1425 CE) discovered the alternating series
for `arctan(x)` and the Leibniz-criterion remainder bound roughly three
centuries before Gregory and Leibniz [Plofker 2009, *Mathematics in
India*, Princeton UP §7.4; Joseph 2010, *The Crest of the Peacock*, 3rd
ed., Princeton UP, ch. 9].

For an alternating series with monotone-decreasing absolute terms, the
truncation error after `N` terms is bounded by the magnitude of the first
omitted term. We formalise the *generic* Madhava–Leibniz remainder bound
for any real alternating series with monotone decreasing positive terms
that converges (existence of a limit `L`). The Mādhava arctan-bound is
the special case `a_n = x^(2n+1) / (2n+1)` for `|x| ≤ 1`.

Runtime counterpart:
  `a11oy/web/packages/a11oy-core/src/governance/madhava-bound.ts`.

Sources:
  * Plofker, K. (2009), *Mathematics in India*, Princeton University
    Press, ISBN 978-0691120676, §7.4.
  * Joseph, G. G. (2010), *The Crest of the Peacock*, 3rd ed., Princeton
    University Press, ISBN 978-0691135267, ch. 9.
  * Original: Mādhava (~1400 CE), via Yuktibhāṣā of Jyeṣṭhadeva (~1530
    CE); see Sarma 2008 ed., *Ganita-Yukti-Bhāṣā*, Hindustan Book Agency.
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Lutar.PACBayes

open BigOperators Finset Filter Set

/-- The Mādhava arctan partial sum to `N` terms:
    `Σ_{n=0}^{N-1} (-1)^n · x^(2n+1) / (2n+1)`. -/
noncomputable def madhavaArctanPartial (x : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, (-1 : ℝ)^n * x^(2*n+1) / (2*n+1)

/-- The Mādhava remainder bound: `|x|^(2N+1) / (2N+1)`. -/
noncomputable def madhavaRemainderBound (x : ℝ) (N : ℕ) : ℝ :=
  |x|^(2*N+1) / (2*N+1)

/-- The remainder bound is non-negative for any real `x` and any `N`. -/
theorem madhavaRemainderBound_nonneg (x : ℝ) (N : ℕ) :
    0 ≤ madhavaRemainderBound x N := by
  unfold madhavaRemainderBound
  have hnum : 0 ≤ |x|^(2*N+1) := pow_nonneg (abs_nonneg x) _
  have hden : (0 : ℝ) < (2*N+1 : ℕ) := by exact_mod_cast Nat.succ_pos (2*N)
  exact div_nonneg hnum (le_of_lt hden)

/-- The remainder bound at `x = 0` is exactly zero. -/
theorem madhavaRemainderBound_at_zero (N : ℕ) :
    madhavaRemainderBound 0 N = 0 := by
  unfold madhavaRemainderBound
  simp [zero_pow (Nat.succ_ne_zero (2*N))]

/-- Monotonicity in `N`: for `|x| ≤ 1`, the remainder bound decreases as
    we take more series terms. -/
theorem madhavaRemainderBound_anti
    (x : ℝ) (hx : |x| ≤ 1) (N : ℕ) :
    madhavaRemainderBound x (N+1) ≤ madhavaRemainderBound x N := by
  unfold madhavaRemainderBound
  have habs_nn : 0 ≤ |x| := abs_nonneg x
  have hnum_le : |x|^(2*(N+1)+1) ≤ |x|^(2*N+1) :=
    pow_le_pow_of_le_one habs_nn hx (by omega)
  have hden_pos1 : (0 : ℝ) < (2*N+1 : ℕ) := by exact_mod_cast Nat.succ_pos (2*N)
  have hden_pos2 : (0 : ℝ) < (2*(N+1)+1 : ℕ) := by exact_mod_cast Nat.succ_pos (2*(N+1))
  have hden_le : ((2*N+1 : ℕ) : ℝ) ≤ ((2*(N+1)+1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2*N+1 ≤ 2*(N+1)+1)
  exact le_trans
    (div_le_div_of_nonneg_right hnum_le hden_pos2)
    (div_le_div_of_nonneg_left (pow_nonneg habs_nn _) hden_pos1 hden_le)

/-- The **Mādhava–Leibniz alternating-series bound** (generic).

    For a real alternating series `Σ (-1)^n · a_n` whose absolute terms
    `a_n` are non-negative and monotone decreasing, and which converges
    to a limit `L`, the truncation after `N` terms differs from `L` by
    at most `a_N` (the first omitted-term magnitude).

    Proof uses `Antitone.alternating_series_le_tendsto` and
    `Antitone.tendsto_le_alternating_series` from
    `Mathlib.Analysis.SpecificLimits.Normed`.

    Sources:
      * Mathlib: `Antitone.alternating_series_le_tendsto`,
        `Antitone.tendsto_le_alternating_series`. -/
theorem madhava_alt_series_bound
    (a : ℕ → ℝ) (L : ℝ) (N : ℕ)
    (h_nn : ∀ n, 0 ≤ a n)
    (h_dec : ∀ n, a (n+1) ≤ a n)
    (h_lim : Filter.Tendsto
              (fun M => ∑ n ∈ range M, (-1 : ℝ)^n * a n)
              Filter.atTop (nhds L)) :
    |(∑ n ∈ range N, (-1 : ℝ)^n * a n) - L| ≤ a N := by
  have hanti : Antitone a := antitone_nat_of_succ_le h_dec
  rcases Nat.even_or_odd N with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- N = 2 * k (even): S_{2k} ≤ L ≤ S_{2k} + a_{2k}
    have hle : ∑ i ∈ range (2 * k), (-1 : ℝ) ^ i * a i ≤ L :=
      hanti.alternating_series_le_tendsto h_lim k
    have hge : L ≤ ∑ i ∈ range (2 * k + 1), (-1 : ℝ) ^ i * a i :=
      hanti.tendsto_le_alternating_series h_lim k
    rw [sum_range_succ, Even.neg_one_pow ⟨k, rfl⟩, one_mul] at hge
    subst hk
    rw [abs_of_nonpos (by linarith)]
    linarith
  · -- N = 2 * k + 1 (odd): S_{2k+1} - a_{2k+1} ≤ L ≤ S_{2k+1}
    have hge : L ≤ ∑ i ∈ range (2 * k + 1), (-1 : ℝ) ^ i * a i :=
      hanti.tendsto_le_alternating_series h_lim k
    have hle2 : ∑ i ∈ range (2 * (k + 1)), (-1 : ℝ) ^ i * a i ≤ L :=
      hanti.alternating_series_le_tendsto h_lim (k + 1)
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, sum_range_succ,
        Odd.neg_one_pow ⟨k, rfl⟩, neg_one_mul] at hle2
    subst hk
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- Internal: for `0 ≤ x < 1`, the arctan remainder bound holds. -/
private lemma madhava_arctan_bound_nonneg
    (x : ℝ) (hx_nn : 0 ≤ x) (hx_lt : x < 1) (N : ℕ) :
    |madhavaArctanPartial x N - Real.arctan x| ≤ madhavaRemainderBound x N := by
  have hx_abs : |x| = x := abs_of_nonneg hx_nn
  have hx_norm : ‖x‖ < 1 := by rwa [Real.norm_eq_abs, hx_abs]
  -- Antitone sequence a n = x^(2n+1)/(2n+1)
  set a : ℕ → ℝ := fun n => x ^ (2 * n + 1) / (2 * n + 1)
  have ha_nn : ∀ n, 0 ≤ a n := fun n =>
    div_nonneg (pow_nonneg hx_nn _) (by exact_mod_cast (Nat.succ_pos (2*n)).le)
  have ha_dec : ∀ n, a (n + 1) ≤ a n := fun n => by
    have h' := madhavaRemainderBound_anti x (by rwa [hx_abs]) n
    unfold madhavaRemainderBound at h'; rw [hx_abs] at h'
    convert h' using 2 <;> ring
  -- Tendsto via Real.hasSum_arctan (Mathlib.Analysis.SpecialFunctions.Complex.Arctan)
  have htend : Filter.Tendsto
      (fun M => ∑ n ∈ range M, (-1 : ℝ) ^ n * a n)
      Filter.atTop (nhds (Real.arctan x)) := by
    refine (Real.hasSum_arctan hx_norm).tendsto_sum_nat.congr'
            (eventually_of_forall fun M => ?_)
    congr 1; ext n; simp [a, mul_div_assoc]
  have hbound := madhava_alt_series_bound a (Real.arctan x) N ha_nn ha_dec htend
  convert hbound using 2
  · unfold madhavaArctanPartial; congr 1; ext n; simp [a, mul_div_assoc]
  · unfold madhavaRemainderBound; rw [hx_abs]

/-- **R4-I1 specialisation.** For `|x| ≤ 1`, the Mādhava partial sum
    approximates `Real.arctan x` with error bounded by the next-term
    magnitude.

    Proof: interior case (`|x| < 1`) via `Real.hasSum_arctan`; boundary
    cases (`x = ±1`) via continuity and a left/right limit using the
    interior bound; negative case via odd parity of `arctan` and of the
    partial sums.

    Sources:
      * Real.hasSum_arctan — Mathlib.Analysis.SpecialFunctions.Complex.Arctan.
      * Alternating bounds — Mathlib.Analysis.SpecificLimits.Normed. -/
theorem madhava_arctan_remainder
    (x : ℝ) (hx : |x| ≤ 1) (N : ℕ) :
    |madhavaArctanPartial x N - Real.arctan x|
      ≤ madhavaRemainderBound x N := by
  -- Continuous helper functions (used for boundary limits)
  have hG_cont : Continuous (fun y => |madhavaArctanPartial y N - Real.arctan y|) := by
    apply Continuous.abs; apply Continuous.sub
    · unfold madhavaArctanPartial
      exact continuous_finset_sum _ fun n _ =>
        (continuous_const.mul (continuous_pow _)).div_const _
    · exact Real.continuous_arctan
  have hH_cont : Continuous (fun y => madhavaRemainderBound y N) := by
    unfold madhavaRemainderBound; exact (continuous_abs.pow _).div_const _
  -- Odd-parity identity: madhavaArctanPartial (-x) N = -madhavaArctanPartial x N
  have hparity : ∀ y : ℝ, madhavaArctanPartial (-y) N = -madhavaArctanPartial y N := fun y => by
    unfold madhavaArctanPartial
    rw [← sum_neg_distrib]
    congr 1; ext n
    have : (-y) ^ (2 * n + 1) = -(y ^ (2 * n + 1)) := by
      rw [Odd.neg_pow ⟨n, rfl⟩]
    rw [this]; ring
  -- Bound identity: madhavaRemainderBound (-y) N = madhavaRemainderBound y N
  have hbound_neg : ∀ y : ℝ, madhavaRemainderBound (-y) N = madhavaRemainderBound y N := fun y => by
    unfold madhavaRemainderBound; simp [abs_neg]
  -- Reduction: |f(-y) - arctan(-y)| = |f(y) - arctan(y)|
  have habs_neg : ∀ y : ℝ,
      |madhavaArctanPartial (-y) N - Real.arctan (-y)| =
      |madhavaArctanPartial y N - Real.arctan y| := fun y => by
    rw [hparity, Real.arctan_neg, show -madhavaArctanPartial y N - (-Real.arctan y) =
        -(madhavaArctanPartial y N - Real.arctan y) by ring, abs_neg]
  -- Main case analysis: x ≥ 0 vs x < 0
  rcases le_or_lt 0 x with hx_nn | hx_neg
  · -- x ≥ 0: |x| = x ≤ 1
    have hx_abs : |x| = x := abs_of_nonneg hx_nn
    rcases lt_or_eq_of_le (hx_abs ▸ hx) with hx_lt | hx_eq
    · -- x ∈ [0, 1): interior
      exact madhava_arctan_bound_nonneg x hx_nn hx_lt N
    · -- x = 1: boundary, left limit
      have hx1 : x = 1 := by linarith [hx_abs ▸ hx_eq.symm]
      subst hx1
      -- G(1) ≤ H(1) via left limit: G(y) ≤ H(y) for all y ∈ (1/2, 1) ⊆ 𝓝[<] 1
      -- nhdsWithin 1 (Iio 1) is NeBot since ℝ has NoMinOrder
      haveI : (nhdsWithin (1 : ℝ) (Iio 1)).NeBot := nhdsWithin_Iio_self_neBot'
      apply le_of_tendsto_of_tendsto
              (f := fun y => |madhavaArctanPartial y N - Real.arctan y|)
              (g := fun y => madhavaRemainderBound y N)
      · exact hG_cont.continuousAt.continuousWithinAt
      · exact hH_cont.continuousAt.continuousWithinAt
      · -- G(y) ≤ H(y) for y ∈ Ioo (1/2) 1, which is a member of 𝓝[<] 1
        filter_upwards [Ioo_mem_nhdsWithin_Iio.mpr ⟨1/2, by norm_num, Subset.refl _⟩]
          with y hy
        simp only [mem_Ioo] at hy
        exact madhava_arctan_bound_nonneg y (by linarith) hy.2 N
  · -- x < 0: reduce to x' = -x > 0 via parity
    have hmx_nn : 0 ≤ -x := by linarith
    have hmx_hx : |-x| ≤ 1 := by rwa [abs_neg]
    -- Rewrite using parity
    rw [← habs_neg x, ← hbound_neg x]
    -- Now need: |madhavaArctanPartial (-x) N - arctan (-x)| ≤ madhavaRemainderBound (-x) N
    -- with -x ≥ 0 and |-x| ≤ 1
    have hmx_abs : |-x| = -x := abs_of_nonneg hmx_nn
    rcases lt_or_eq_of_le (hmx_abs ▸ hmx_hx) with hmx_lt | hmx_eq
    · exact madhava_arctan_bound_nonneg (-x) hmx_nn hmx_lt N
    · -- -x = 1: boundary (x = -1)
      have hmx1 : -x = 1 := by linarith [hmx_abs ▸ hmx_eq.symm]
      -- Substitute -x = 1
      rw [hmx1]
      -- Now goal: |madhavaArctanPartial 1 N - arctan 1| ≤ madhavaRemainderBound 1 N
      -- Same left-limit argument as the x = 1 case above
      haveI : (nhdsWithin (1 : ℝ) (Iio 1)).NeBot := nhdsWithin_Iio_self_neBot'
      apply le_of_tendsto_of_tendsto
              (f := fun y => |madhavaArctanPartial y N - Real.arctan y|)
              (g := fun y => madhavaRemainderBound y N)
      · exact hG_cont.continuousAt.continuousWithinAt
      · exact hH_cont.continuousAt.continuousWithinAt
      · filter_upwards [Ioo_mem_nhdsWithin_Iio.mpr ⟨1/2, by norm_num, Subset.refl _⟩]
          with y hy
        simp only [mem_Ioo] at hy
        exact madhava_arctan_bound_nonneg y (by linarith) hy.2 N

end Lutar.PACBayes
