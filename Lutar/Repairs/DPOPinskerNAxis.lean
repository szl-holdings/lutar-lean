/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Tier-B Repair — DPO Pinsker promotion (n-axis), axiom-free

## Honesty verdict first (philosophers' enforcement)

The in-tree DPO honest-gap axiom Lutar.DPOFeasibility.pinsker
(tvDist <= sqrt (klDivergence / 2), stated with NO probability-simplex
hypothesis on PolicyParam n = Fin n -> R) is FALSE-as-stated and its
token is UNTOUCHED by this file. This module DISCHARGES the corrected
statement for EVERY dimension n under the simplex-interior hypotheses:

* dpo_pinsker_n_axis — the full Pinsker bound
  tvDist p q <= sqrt (klDivergence p q / 2) for simplex-interior policies
  of ANY dimension n, proven from Wave14 log_sum_inequality (CF-21) and
  Wave17 binary_pinsker (CF-23). NO axioms, no unproved placeholders.
* LambdaGateLID_DPO_stability_simplex — TH12 for every n, with ZERO
  dependence on either honest-gap axiom (the DPO file's own TH12 proof
  shape, with dpo_pinsker_n_axis in place of the axiom).

This generalizes the merged two-axis repair (PR #367,
Lutar/Repairs/DPOPinskerPromotion.lean) from numAxes = 2 to every
dimension. With this module, the only remaining obstacle to closing the
Pinsker honest-gap ledger entry is the missing simplex hypothesis in
PolicyParam itself (the v18 re-typing decision), not any proof obligation.

## Proof (Cover-Thomas Thm 11.6.1 route)
(a) Sign set V = { i | q i <= p i }. Then
    tvDist p q = (1/2) * sum_i |p i - q i| = sum_(i in V) (p i - q i) = P - Q
    where P = sum_(i in V) p i, Q = sum_(i in V) q i, by equal-mass
    cancellation (sum p = sum q = 1).
(b) Log-sum inequality (Wave14 CF-21) applied to the two cells V and its
    complement: P * log(P/Q) + (1-P) * log((1-P)/(1-Q)) <= KL(p, q).
(c) Binary Pinsker (Wave17 CF-23): 2 * (P - Q)^2 <= P * (log P - log Q)
    + (1-P) * (log (1-P) - log (1-Q)).
(d) Chain (b) and (c): 2 * tvDist^2 <= KL; close by sqrt monotonicity.

## References
- Cover, T.M. & Thomas, J.A. (2006). Elements of Information Theory, 2nd
  ed. Thm 11.6.1 (Pinsker), Lemma 11.6.1 (binary reduction via sign set).
- Pinsker, M.S. (1964). Information and Information Stability. sec 2.2.
- Wave14 CF-21 log_sum_inequality; Wave17 CF-23 binary_pinsker.

Signed-off-by: SZL CTO <cto@szlholdings.com>
-/
import Lutar.DPOFeasibility
import Lutar.Wave14.LogSumInequality
import Lutar.Wave17.BinaryPinsker
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Lutar.Repairs

open Real Finset BigOperators

/-- CF-24 (Tier-B, n-axis). The full Pinsker bound in the DPO file's own
symbols, for simplex-interior policies of ANY dimension n:
tvDist p q <= sqrt (klDivergence p q / 2).
Proven from Wave14 log_sum_inequality + Wave17 binary_pinsker —
NO axioms, no unproved placeholders. -/
theorem dpo_pinsker_n_axis {n : ℕ}
    (p q : Lutar.DPOFeasibility.PolicyParam n)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hpsum : ∑ i : Fin n, p i = 1) (hqsum : ∑ i : Fin n, q i = 1) :
    Lutar.DPOFeasibility.tvDist p q ≤
      Real.sqrt (Lutar.DPOFeasibility.klDivergence p q / 2) := by
  classical
  -- (a) the sign set
  set V : Finset (Fin n) := Finset.univ.filter (fun i => q i ≤ p i) with _hVdef
  have hmemV : ∀ i, i ∈ V ↔ q i ≤ p i := fun i =>
    Finset.mem_filter.trans (and_iff_right (Finset.mem_univ i))
  -- total signed difference is zero (equal mass)
  have hdsum : ∑ i : Fin n, (p i - q i) = 0 := by
    rw [Finset.sum_sub_distrib, hpsum, hqsum]; ring
  -- absolute values split over the two cells
  have hAbs : ∑ i : Fin n, |p i - q i| =
      (∑ i ∈ V, (p i - q i)) + ∑ i ∈ Vᶜ, (q i - p i) := by
    have hVabs : ∑ i ∈ V, |p i - q i| = ∑ i ∈ V, (p i - q i) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [abs_of_nonneg (sub_nonneg.mpr ((hmemV i).mp hi))]
    have hCabs : ∑ i ∈ Vᶜ, |p i - q i| = ∑ i ∈ Vᶜ, (q i - p i) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi' : i ∉ V := Finset.mem_compl.mp hi
      have hpq : ¬ (q i ≤ p i) := fun hle =>
        hi' (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hle⟩)
      have hlt : p i < q i := not_le.mp hpq
      rw [abs_sub_comm (p i) (q i), abs_of_nonneg (show 0 ≤ q i - p i by linarith)]
    rw [← Finset.sum_add_sum_compl V (fun i => |p i - q i|), hVabs, hCabs]
  -- complement cell carries the same mass difference as V
  have hC : ∑ i ∈ Vᶜ, (q i - p i) = ∑ i ∈ V, (p i - q i) := by
    have h1 : ∑ i ∈ Vᶜ, (q i - p i) = - ∑ i ∈ Vᶜ, (p i - q i) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have h2 : (∑ i ∈ V, (p i - q i)) + ∑ i ∈ Vᶜ, (p i - q i) = 0 := by
      rw [Finset.sum_add_sum_compl V (fun i => p i - q i), hdsum]
    linarith
  -- hence tvDist is exactly the V-cell signed mass
  have htv : Lutar.DPOFeasibility.tvDist p q = ∑ i ∈ V, (p i - q i) := by
    unfold Lutar.DPOFeasibility.tvDist Lutar.DPOFeasibility.axisScore
    rw [hAbs, hC]; ring
  -- cell masses
  set P := ∑ i ∈ V, p i with hP
  set Q := ∑ i ∈ V, q i with hQ
  have hTV : Lutar.DPOFeasibility.tvDist p q = P - Q := by
    rw [htv, Finset.sum_sub_distrib, ← hP, ← hQ]
  have hPc : ∑ i ∈ Vᶜ, p i = 1 - P := by
    have h := Finset.sum_add_sum_compl V p
    rw [hpsum] at h
    linarith
  have hQc : ∑ i ∈ Vᶜ, q i = 1 - Q := by
    have h := Finset.sum_add_sum_compl V q
    rw [hqsum] at h
    linarith
  -- (b) log-sum inequality on the two cells
  have hls1 := Lutar.Wave14.log_sum_inequality V p q
    (fun i _ => hp i) (fun i _ => hq i)
  have hls2 := Lutar.Wave14.log_sum_inequality Vᶜ p q
    (fun i _ => hp i) (fun i _ => hq i)
  rw [← hP, ← hQ] at hls1
  rw [hPc, hQc] at hls2
  have hKLsplit : Lutar.DPOFeasibility.klDivergence p q =
      (∑ i ∈ V, p i * Real.log (p i / q i)) + ∑ i ∈ Vᶜ, p i * Real.log (p i / q i) := by
    unfold Lutar.DPOFeasibility.klDivergence Lutar.DPOFeasibility.axisScore
    rw [← Finset.sum_add_sum_compl V (fun i => p i * Real.log (p i / q i))]
  -- tvDist is nonnegative
  have hTVnn : 0 ≤ Lutar.DPOFeasibility.tvDist p q := by
    have hle : ∀ i ∈ V, 0 ≤ p i - q i := fun i hi => sub_nonneg.mpr ((hmemV i).mp hi)
    have hsum : ∑ i ∈ V, (p i - q i) = P - Q := by rw [hP, hQ, Finset.sum_sub_distrib]
    rw [hTV, ← hsum]
    exact Finset.sum_nonneg hle
  rcases Finset.eq_empty_or_nonempty V with hV0 | hVne
  · -- V empty forces tvDist = 0
    have hP0 : P = 0 := by rw [hP, hV0]; simp
    have hQnn : 0 ≤ Q := by rw [hQ]; exact Finset.sum_nonneg (fun i _ => le_of_lt (hq i))
    have h1 : Lutar.DPOFeasibility.tvDist p q = -Q := by
      rw [hTV, hP0]; ring
    have hTV0 : Lutar.DPOFeasibility.tvDist p q = 0 := by linarith
    rw [hTV0]; exact Real.sqrt_nonneg _
  rcases Finset.eq_empty_or_nonempty (Vᶜ : Finset (Fin n)) with hVC0 | hVCne
  · -- complement empty forces tvDist = 0
    have h2' : (∑ i ∈ V, (p i - q i)) + ∑ i ∈ Vᶜ, (p i - q i) = 0 := by
      rw [Finset.sum_add_sum_compl V (fun i => p i - q i), hdsum]
    rw [hVC0] at h2'
    rw [Finset.sum_empty] at h2'
    have hTV0 : Lutar.DPOFeasibility.tvDist p q = 0 := by rw [htv]; linarith
    rw [hTV0]; exact Real.sqrt_nonneg _
  -- main case: both cells nonempty
  have hPpos : 0 < P := Finset.sum_pos (fun i _ => hp i) hVne
  have hQpos : 0 < Q := Finset.sum_pos (fun i _ => hq i) hVne
  have hPcpos : 0 < ∑ i ∈ Vᶜ, p i := Finset.sum_pos (fun i _ => hp i) hVCne
  have hQcpos : 0 < ∑ i ∈ Vᶜ, q i := Finset.sum_pos (fun i _ => hq i) hVCne
  have hP1 : P < 1 := by have := hPc; linarith
  have hQ1 : Q < 1 := by have := hQc; linarith
  -- (c) binary Pinsker on the cell masses
  have hbin := Lutar.Wave17.binary_pinsker Q P hQpos hQ1 hPpos hP1
  have eP : P * (Real.log P - Real.log Q) = P * Real.log (P / Q) := by
    rw [Real.log_div (ne_of_gt hPpos) (ne_of_gt hQpos)]
  have eQ : (1 - P) * (Real.log (1 - P) - Real.log (1 - Q)) =
      (1 - P) * Real.log ((1 - P) / (1 - Q)) := by
    rw [Real.log_div (ne_of_gt (show 0 < 1 - P by linarith))
      (ne_of_gt (show 0 < 1 - Q by linarith))]
  rw [eP, eQ] at hbin
  -- (d) chain: 2 * tvDist^2 <= KL
  have h2 : 2 * (P - Q) ^ 2 ≤ Lutar.DPOFeasibility.klDivergence p q := by
    calc 2 * (P - Q) ^ 2
        ≤ P * Real.log (P / Q) + (1 - P) * Real.log ((1 - P) / (1 - Q)) := hbin
      _ ≤ (∑ i ∈ V, p i * Real.log (p i / q i)) + ∑ i ∈ Vᶜ, p i * Real.log (p i / q i) :=
          add_le_add hls1 hls2
      _ = Lutar.DPOFeasibility.klDivergence p q := hKLsplit.symm
  have hsq : (Lutar.DPOFeasibility.tvDist p q) ^ 2 ≤
      Lutar.DPOFeasibility.klDivergence p q / 2 := by
    rw [hTV]
    linarith
  rw [← abs_of_nonneg hTVnn, ← Real.sqrt_sq_eq_abs (Lutar.DPOFeasibility.tvDist p q)]
  exact Real.sqrt_le_sqrt hsq

/-- TH12 restated for every n (Tier-B). LAMBDAGateLID DPO stability for
simplex-interior policies of ANY dimension, proven WITHOUT the honest-gap
axioms Lutar.DPOFeasibility.pinsker / klDivergence_nonneg — the Pinsker
step is dpo_pinsker_n_axis (Wave14/Wave17-backed). -/
theorem LambdaGateLID_DPO_stability_simplex {n : ℕ}
    (pi_ref pi_new : Lutar.DPOFeasibility.PolicyParam n)
    (hp_ref : ∀ i, 0 < pi_ref i) (hp_new : ∀ i, 0 < pi_new i)
    (hp_ref_sum : ∑ i : Fin n, pi_ref i = 1) (hp_new_sum : ∑ i : Fin n, pi_new i = 1)
    (tau eps : ℝ)
    (h_ref_in_LID : pi_ref ∈ Lutar.DPOFeasibility.ΛGateLID tau)
    (h_kl : Lutar.DPOFeasibility.klDivergence pi_new pi_ref ≤ eps)
    (_h_eps_nonneg : 0 ≤ eps) :
    pi_new ∈ Lutar.DPOFeasibility.ΛGateLID
      (tau - Lutar.DPOFeasibility.gateLipschitz * Real.sqrt (eps / 2)) := by
  intro k
  -- (1) n-axis Pinsker -> TV <= sqrt(eps/2)
  have h_tv_le : Lutar.DPOFeasibility.tvDist pi_new pi_ref ≤ Real.sqrt (eps / 2) := by
    have h_pinsker :=
      dpo_pinsker_n_axis pi_new pi_ref hp_new hp_ref hp_new_sum hp_ref_sum
    have h_kl_half :
        Lutar.DPOFeasibility.klDivergence pi_new pi_ref / 2 ≤ eps / 2 := by linarith
    have h_sqrt_mono :
        Real.sqrt (Lutar.DPOFeasibility.klDivergence pi_new pi_ref / 2) ≤
        Real.sqrt (eps / 2) :=
      Real.sqrt_le_sqrt h_kl_half
    linarith
  -- (2) Lipschitz (proved theorem, no axiom)
  have h_lip := Lutar.DPOFeasibility.axisScore_lipschitz pi_ref pi_new k
  have h_diff_le : Lutar.DPOFeasibility.axisScore pi_ref k - Lutar.DPOFeasibility.axisScore pi_new k ≤
                   Lutar.DPOFeasibility.gateLipschitz * Lutar.DPOFeasibility.tvDist pi_ref pi_new :=
    le_trans (le_abs_self _) h_lip
  -- (3) TV symmetry (proved theorem, no axiom)
  have h_sym : Lutar.DPOFeasibility.tvDist pi_ref pi_new =
      Lutar.DPOFeasibility.tvDist pi_new pi_ref :=
    Lutar.DPOFeasibility.tvDist_symm pi_ref pi_new
  -- (4) anchor + arithmetic close
  have h_ref_tau : tau ≤ Lutar.DPOFeasibility.axisScore pi_ref k := h_ref_in_LID k
  have h_tv_ref_le : Lutar.DPOFeasibility.tvDist pi_ref pi_new ≤ Real.sqrt (eps / 2) :=
    h_sym ▸ h_tv_le
  have h_L_tv_le : Lutar.DPOFeasibility.gateLipschitz * Lutar.DPOFeasibility.tvDist pi_ref pi_new ≤
                   Lutar.DPOFeasibility.gateLipschitz * Real.sqrt (eps / 2) :=
    mul_le_mul_of_nonneg_left h_tv_ref_le Lutar.DPOFeasibility.gateLipschitz_nonneg
  nlinarith

end Lutar.Repairs

#print axioms Lutar.Repairs.dpo_pinsker_n_axis
#print axioms Lutar.Repairs.LambdaGateLID_DPO_stability_simplex
