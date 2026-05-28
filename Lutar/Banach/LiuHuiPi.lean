/-
# R4-C2 — Liu Hui polygon-doubling π converges

Liu Hui (3rd c. CE, *Jiu Zhang Suanshu* commentary) computed `π` by
inscribed regular polygon doubling: starting from the regular hexagon
(`s₆ = 1` on the unit circle) and applying `s_{2k}² = 2 - √(4 - s_k²)`,
the 96-gon (`k = 4`) gives the classical bound
`3.141024 < π < 3.142704`.

The sequence `π_n := n · s_n / 2` is monotonically increasing in `n`
(more sides ⇒ closer to the inscribed-arc length) and bounded above by
`π`, hence convergent. This is the twin contraction lineage to the
Babylonian sqrt (R3-G1).

Citations:
- Cullen, C. (1996). *Astronomy and Mathematics in Ancient China.* CUP.
- Martzloff, J.-C. (1997). *A History of Chinese Mathematics.* Springer.

Status: skeleton; monotone-bounded convergence is recorded with a tagged
`sorry` deferring to the monotone-convergence theorem in Mathlib.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt

namespace Lutar.Banach.LiuHui

open Real

/-- Squared inscribed-side length at the `k`-th polygon-doubling, starting
    from the regular hexagon (`s₆ = 1`, `s₆² = 1`). -/
noncomputable def sideSquared : ℕ → ℝ
  | 0     => 1
  | n + 1 => 2 - Real.sqrt (4 - sideSquared n)

/-- Number of sides at doubling step `k`:  `n_k = 6 · 2^k`. -/
def sideCount (k : ℕ) : ℕ := 6 * 2 ^ k

/-- Inscribed-polygon estimate of `π` at doubling step `k`. -/
noncomputable def liuHuiPi (k : ℕ) : ℝ :=
  (sideCount k : ℝ) * Real.sqrt (sideSquared k) / 2

/-- The 96-gon (Liu Hui's documented choice): `k = 4` since `6 · 2^4 = 96`. -/
noncomputable def liuHui96Gon : ℝ := liuHuiPi 4

/-- `sideSquared n ∈ [0, 4]` for all `n` (well-definedness of the recurrence). -/
theorem sideSquared_bounds : ∀ n, 0 ≤ sideSquared n ∧ sideSquared n ≤ 4 := by
  intro n
  induction n with
  | zero => refine ⟨by norm_num, by norm_num⟩
  | succ n ih =>
    obtain ⟨h0, h4⟩ := ih
    -- sideSquared (n+1) = 2 - √(4 - sideSquared n); 0 ≤ 4 - sideSquared n ≤ 4
    -- so 0 ≤ √(...) ≤ 2 and 0 ≤ 2 - √(...) ≤ 2 ≤ 4.
    sorry

/-- **Liu Hui's π sequence converges.**

    The sequence `liuHuiPi k` is monotone non-decreasing in `k` (each doubling
    refines the inscribed perimeter) and is bounded above by `π`, hence
    converges by the monotone-convergence theorem [Mathlib
    `tendsto_of_monotone_of_bounded`]. The limit is `π`. -/
theorem liu_hui_pi_converges :
    ∃ L : ℝ, ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, |liuHuiPi k - L| < ε := by
  -- The classical proof: refine using the half-angle identity and bound
  -- the gap by 1 - cos(π / n_k) → 0.
  sorry

end Lutar.Banach.LiuHui
