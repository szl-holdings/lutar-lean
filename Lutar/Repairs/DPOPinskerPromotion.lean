/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Tier-B Repair — DPO Pinsker promotion (two-axis), axiom-free

## Honesty verdict first (philosophers' enforcement)

The in-tree DPO honest-gap axioms Lutar.DPOFeasibility.pinsker and
Lutar.DPOFeasibility.klDivergence_nonneg are FALSE-as-stated (no
probability-simplex hypothesis on PolicyParam n = Fin n -> R) and their
tokens are UNTOUCHED by this file. This module PROMOTES the corrected,
hypothesis-carrying statements into the DPO file's own symbols:

* dpo_klDivergence_nonneg_simplex — promoted re-export of Wave15 CF-22
  (Lutar.Wave15.dpo_klDivergence_nonneg_on_simplex): KL >= 0 on the simplex
  interior, stated in DPO symbols.
* dpo_pinsker_two_axis — NEW: the full Pinsker bound
  tvDist p q <= sqrt (klDivergence p q / 2) for TWO-AXIS simplex-interior
  policies, proven from Wave17 binary_pinsker (CF-23). NO axioms.
* LambdaGateLID_DPO_stability_two_axis — the TH12 stability result (proven, axiom-free)
  restated for two axes on the simplex interior, with ZERO dependence on the
  two honest-gap axioms (only the Wave14/15/17 proof chain + Mathlib).

## What remains honestly open
The n-axis (n > 2) Pinsker bound in DPO symbols remains OPEN: the
squared-L1 lower-bound step recorded in Lutar.Wave15.PinskerRoadmap and the
two-cell multiclass_pinsker (Wave17 CF-23-FULL) cover a single partition;
the full n-axis assembly is NOT proven here. The unconditional axioms stay
FALSE-as-stated. Locked-proven set unchanged. NO new axiom; NO sorry.

## References
- Pinsker, M.S. (1964). Information and Information Stability. §2.2.
- Cover, T.M. & Thomas, J.A. (2006). Elements of Information Theory, 2nd ed.
  Thm 11.6.1 (Pinsker), Lemma 11.6.1 (binary reduction).
- Wave14 CF-21 log-sum / Gibbs core; Wave15 CF-22; Wave17 CF-23 binary_pinsker.

Signed-off-by: SZL CTO <cto@szlholdings.com>
-/
import Lutar.DPOFeasibility
import Lutar.Wave15.KLDivergenceSimplex
import Lutar.Wave17.BinaryPinsker
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Lutar.Repairs

open Real Finset BigOperators

/-- CF-22 promoted (Tier-B). KL non-negativity in the DPO file's own
symbols, on the simplex interior. Zero axioms; delegates to Wave15 CF-22. -/
theorem dpo_klDivergence_nonneg_simplex {n : ℕ}
    (p q : Lutar.DPOFeasibility.PolicyParam n)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hpsum : ∑ i : Fin n, p i = 1) (hqsum : ∑ i : Fin n, q i = 1) :
    0 ≤ Lutar.DPOFeasibility.klDivergence p q :=
  Lutar.Wave15.dpo_klDivergence_nonneg_on_simplex p q hp hq hpsum hqsum

/-- CF-23 two-axis promotion (Tier-B). The full Pinsker bound in the DPO
file's own symbols, for TWO-AXIS simplex-interior policies:
tvDist p q <= sqrt (klDivergence p q / 2).
Proven from Wave17 binary_pinsker — NO axioms, NO sorry. -/
theorem dpo_pinsker_two_axis
    (p q : Lutar.DPOFeasibility.PolicyParam 2)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hpsum : ∑ i : Fin 2, p i = 1) (hqsum : ∑ i : Fin 2, q i = 1) :
    Lutar.DPOFeasibility.tvDist p q ≤
      Real.sqrt (Lutar.DPOFeasibility.klDivergence p q / 2) := by
  -- (a) coordinates
  have hps : p 0 + p 1 = 1 := by
    have h := hpsum; rwa [Fin.sum_univ_two] at h
  have hqs : q 0 + q 1 = 1 := by
    have h := hqsum; rwa [Fin.sum_univ_two] at h
  have hp1 : p 1 = 1 - p 0 := by linarith
  have hq1 : q 1 = 1 - q 0 := by linarith
  have ha0 : 0 < p 0 := hp 0
  have hb0 : 0 < q 0 := hq 0
  have ha1 : p 0 < 1 := by linarith [hp 1]
  have hb1 : q 0 < 1 := by linarith [hq 1]
  have ha1pos : 0 < p 1 := hp 1
  have hb1pos : 0 < q 1 := hq 1
  -- (b) KL divergence equals the binary KL form
  have hkl : Lutar.DPOFeasibility.klDivergence p q =
      p 0 * (Real.log (p 0) - Real.log (q 0)) +
      (1 - p 0) * (Real.log (1 - p 0) - Real.log (1 - q 0)) := by
    unfold Lutar.DPOFeasibility.klDivergence Lutar.DPOFeasibility.axisScore
    rw [Fin.sum_univ_two]
    have e0 : p 0 * Real.log (p 0 / q 0)
        = p 0 * (Real.log (p 0) - Real.log (q 0)) := by
      rw [Real.log_div (ne_of_gt ha0) (ne_of_gt hb0)]
    have e1 : p 1 * Real.log (p 1 / q 1)
        = p 1 * (Real.log (p 1) - Real.log (q 1)) := by
      rw [Real.log_div (ne_of_gt ha1pos) (ne_of_gt hb1pos)]
    rw [e0, e1, hp1, hq1]
  -- (c) binary Pinsker (Wave17 CF-23), transported into DPO symbols
  have hbin := Lutar.Wave17.binary_pinsker (q 0) (p 0) hb0 hb1 ha0 ha1
  rw [← hkl] at hbin
  -- (d) tvDist p q = |p 0 - q 0|
  have htv : Lutar.DPOFeasibility.tvDist p q = |p 0 - q 0| := by
    unfold Lutar.DPOFeasibility.tvDist Lutar.DPOFeasibility.axisScore
    rw [Fin.sum_univ_two, hp1, hq1]
    have heq : (1 - p 0) - (1 - q 0) = q 0 - p 0 := by ring
    rw [heq, abs_sub_comm (q 0) (p 0)]
    ring
  -- (e) close: |d| = sqrt d² and d² ≤ KL/2
  rw [htv, ← Real.sqrt_sq_eq_abs (p 0 - q 0)]
  exact Real.sqrt_le_sqrt (by linarith)

/-- TH12 restated (Tier-B, two-axis). ΛGateLID DPO stability for two-axis
simplex-interior policies, proven WITHOUT the honest-gap axioms
Lutar.DPOFeasibility.pinsker / klDivergence_nonneg — the Pinsker step is
dpo_pinsker_two_axis (Wave17-backed). -/
theorem LambdaGateLID_DPO_stability_two_axis
    (pi_ref pi_new : Lutar.DPOFeasibility.PolicyParam 2)
    (hp_ref : ∀ i, 0 < pi_ref i) (hp_new : ∀ i, 0 < pi_new i)
    (hp_ref_sum : ∑ i : Fin 2, pi_ref i = 1) (hp_new_sum : ∑ i : Fin 2, pi_new i = 1)
    (tau eps : ℝ)
    (h_ref_in_LID : pi_ref ∈ Lutar.DPOFeasibility.ΛGateLID tau)
    (h_kl : Lutar.DPOFeasibility.klDivergence pi_new pi_ref ≤ eps)
    (_h_eps_nonneg : 0 ≤ eps) :
    pi_new ∈ Lutar.DPOFeasibility.ΛGateLID
      (tau - Lutar.DPOFeasibility.gateLipschitz * Real.sqrt (eps / 2)) := by
  intro k
  -- (1) two-axis Pinsker -> TV <= sqrt(eps/2)
  have h_tv_le : Lutar.DPOFeasibility.tvDist pi_new pi_ref ≤ Real.sqrt (eps / 2) := by
    have h_pinsker :=
      dpo_pinsker_two_axis pi_new pi_ref hp_new hp_ref hp_new_sum hp_ref_sum
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

#print axioms Lutar.Repairs.dpo_klDivergence_nonneg_simplex
#print axioms Lutar.Repairs.dpo_pinsker_two_axis
#print axioms Lutar.Repairs.LambdaGateLID_DPO_stability_two_axis
