import Mathlib

namespace Lutar.Putnam.P_A1

/-!
# Putnam 2025 A1

**Problem.** Let `m₀` and `n₀` be distinct positive integers. For every positive
integer `k`, define `mₖ` and `nₖ` to be the relatively prime positive integers
such that `mₖ / nₖ = (2 mₖ₋₁ + 1) / (2 nₖ₋₁ + 1)`. Prove that `2 mₖ + 1` and
`2 nₖ + 1` are relatively prime for all but finitely many positive integers `k`.

**Honest status: DEMO** — faithful statement, proof DEFERRED (`sorry`).
The reduced-fraction sequence is modelled by its defining hypotheses: `hrec` is
the cross-multiplied form of `mₖ₊₁ / nₖ₊₁ = (2 mₖ + 1) / (2 nₖ + 1)`, and `hcop`
records that each `(mₖ₊₁, nₖ₊₁)` is the reduced (coprime) representative.
-/

/-- Faithful statement of Putnam 2025 A1 (DEMO: proof deferred). -/
theorem putnam_A1_correct
    (m n : ℕ → ℕ)
    (hm : ∀ k, 0 < m k) (hn : ∀ k, 0 < n k)
    (hdist : m 0 ≠ n 0)
    (hrec : ∀ k, m (k + 1) * (2 * n k + 1) = n (k + 1) * (2 * m k + 1))
    (hcop : ∀ k, Nat.Coprime (m (k + 1)) (n (k + 1))) :
    ∃ K : ℕ, ∀ k ≥ K, Nat.Coprime (2 * m k + 1) (2 * n k + 1) := by
  sorry

end Lutar.Putnam.P_A1
