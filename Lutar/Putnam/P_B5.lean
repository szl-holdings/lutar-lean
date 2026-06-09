import Mathlib

namespace Lutar.Putnam.P_B5

/-!
# Putnam 2025 B5

**Problem.** Let `p` be a prime `> 3`. For each `k ∈ {1, …, p−1}`, let
`I(k) ∈ {1, …, p−1}` satisfy `k · I(k) ≡ 1 (mod p)`. Prove that the number of
integers `k ∈ {1, …, p−2}` such that `I(k+1) < I(k)` is greater than `p/4 − 1`.

**Honest status: DEMO** — faithful statement, proof DEFERRED (`sorry`).
The modular-inverse function `I` is modelled by its characterizing hypothesis
`hI` (range `1 ≤ I k ≤ p−1` and `k · I k ≡ 1 (mod p)`).
-/

/-- Faithful statement of Putnam 2025 B5 (DEMO: proof deferred). -/
theorem putnam_B5_correct (p : ℕ) (hp : p.Prime) (hp3 : 3 < p)
    (I : ℕ → ℕ)
    (hI : ∀ k, 1 ≤ k → k ≤ p - 1 → 1 ≤ I k ∧ I k ≤ p - 1 ∧ (k * I k) % p = 1) :
    (p : ℝ) / 4 - 1 <
      (((Finset.Icc 1 (p - 2)).filter (fun k => I (k + 1) < I k)).card : ℝ) := by
  sorry

end Lutar.Putnam.P_B5
