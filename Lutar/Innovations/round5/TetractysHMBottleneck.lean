import Mathlib
import Lutar.Wave13.Sweep

/-!
# Tetractys HM bottleneck (discharged 2026-11-19 by delegation)

This module previously carried a tracked proof placeholder for the Tetractys
harmonic-mean bottleneck in its `rpow (-(1 : Real))` form. The placeholder is
now discharged by delegating to the placeholder-free, kernel-checked
`Lutar.Wave13.Sweep.hm_bottleneck_clean` (the clean `x i`-inverse statement of
the same fact, Hardy-Littlewood-Polya 1934 sec 2.5): each summand
`(x i)^(-(1 : Real))` is bridged to the clean inverse `(x i)⁻¹` via
`Real.rpow_neg_one`, and the pure order/field core is delegated unchanged.
The module is wired into `Lutar.lean` so the CI lake build machine-checks it.
Zero new axioms; Innovations/round5 is outside the locked kernel.
-/

namespace Lutar.Innovations.Round5

/-- If HM < threshold but each x_i > 0, then exists i such that x_i < threshold.
    Proof: by_contra all x_i >= threshold => HM >= threshold (contradiction).
    Discharged by delegation: bridge each rpow (-1) summand to a clean inverse,
    then apply the Wave13 clean-statement companion.
    Source: Hardy, Littlewood, Polya (1934), sec 2.5. -/
theorem tetractys_hm_bottleneck
    (n : Nat) (hn : 0 < n) (x : Fin n -> Real) (hx : forall i, 0 < x i)
    (threshold : Real) (ht : 0 < threshold)
    (hHM_low : (n : Real) / (Finset.univ.sum (fun i => (x i)^(-(1:Real)))) < threshold)
    : exists i : Fin n, x i < threshold := by
  -- Bridge the toolchain-sensitive rpow (-1) summands to clean inverses.
  have hconv : forall i, (x i)^(-(1:Real)) = (x i)⁻¹ := by
    intro i
    rw [Real.rpow_neg_one (ne_of_gt (hx i))]
  -- Lift the hypothesis to the clean-inverse sum, then delegate the pure
  -- order/field core to Wave13's kernel-checked companion.
  have hlow : (n : Real) / (Finset.univ.sum (fun i => (x i)⁻¹)) < threshold := by
    simpa only [hconv] using hHM_low
  exact Lutar.Wave13.Sweep.hm_bottleneck_clean n hn x hx threshold ht hlow

end Lutar.Innovations.Round5
