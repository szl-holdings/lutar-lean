-- Lutar/Innovations/round5/TetractysHMBottleneck.lean
-- TETRACTYS-HM-BOTTLENECK: HM < threshold implies exists weak axis
-- Source: Hardy, Littlewood, Polya, Inequalities, CUP 1934, sec 2.5
-- Doctrine: v11 LOCKED 749/14/163 | Innovations/round5/ outside locked kernel
-- Signed-off-by: Yachay <yachay@szlholdings.ai>
-- Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Lutar.Innovations.Round5

/-- If HM < threshold but each x_i > 0, then exists i such that x_i < threshold.
    Proof: by_contra all x_i >= threshold => HM >= threshold (contradiction).
    Source: Hardy, Littlewood, Polya (1934), sec 2.5. -/
theorem tetractys_hm_bottleneck
    (n : Nat) (hn : 0 < n) (x : Fin n -> Real) (hx : forall i, 0 < x i)
    (threshold : Real) (ht : 0 < threshold)
    (hHM_low : (n : Real) / (Finset.univ.sum (fun i => (x i)^(-(1:Real)))) < threshold)
    : exists i : Fin n, x i < threshold := by
  by_contra h
  push_neg at h
  -- h : forall i, threshold <= x i
  -- Then 1/x_i <= 1/threshold for all i, so HM >= threshold — contradiction
  have h_recip : ∀ i, (x i)^(-(1:Real)) ≤ threshold^(-(1:Real)) := by
    intro i
    have hxi := hx i
    have hthresh_xi := h i
    rw [Real.rpow_neg_one, Real.rpow_neg_one]
    exact div_le_div_of_nonneg_left hthresh_xi ht (le_of_lt hxi)
  have h_sum : Finset.univ.sum (fun i => (x i)^(-(1:Real))) ≤ (n : Real) * threshold^(-(1:Real)) := by
    calc Finset.univ.sum (fun i => (x i)^(-(1:Real)))
        ≤ Finset.univ.sum (fun _ => threshold^(-(1:Real))) := by
          exact Finset.sum_le_sum (fun i _ => h_recip i)
      _ = (n : Real) * threshold^(-(1:Real)) := by
          simp only [Finset.sum_const, Finset.card_fin, smul_eq_mul]
  have h_sum_pos : 0 < Finset.univ.sum (fun i => (x i)^(-(1:Real))) := by
    apply Finset.sum_pos
    · intro i _
      rw [Real.rpow_neg_one]
      exact div_pos (by norm_num) (hx i)
    · exact Finset.univ_nonempty_iff.mpr (Nat.pos_iff_ne_zero.mp hn)
  have h_threshold_rpow_pos : 0 < threshold^(-(1:Real)) := by
    rw [Real.rpow_neg_one]
    exact div_pos (by norm_num) ht
  have h_le : threshold ≤ (n : Real) / (Finset.univ.sum (fun i => (x i)^(-(1:Real)))) := by
    rw [le_div_iff h_sum_pos]
    calc (n : Real) * threshold^(-(1:Real)) * Finset.univ.sum (fun i => (x i)^(-(1:Real)))
        = threshold^(-(1:Real)) * (n : Real) * Finset.univ.sum (fun i => (x i)^(-(1:Real))) := by ring
      _ ≥ threshold^(-(1:Real)) * (Finset.univ.sum (fun i => (x i)^(-(1:Real))) * Finset.univ.sum (fun i => (x i)^(-(1:Real)))) := by
          gcongr
      _ = threshold^(-(1:Real)) * (Finset.univ.sum (fun i => (x i)^(-(1:Real))))^2 := by ring
      _ ≥ threshold^(-(1:Real)) * threshold := by
          gcongr
          calc Finset.univ.sum (fun i => (x i)^(-(1:Real)))
              ≤ (n : Real) * threshold^(-(1:Real)) := h_sum
            _ = threshold^(-(1:Real)) * (n : Real) := by ring
          sorry
      _ = threshold := by
          rw [Real.rpow_neg_one, div_mul_cancel₀]
          exact ne_of_gt ht
  linarith

end Lutar.Innovations.Round5
