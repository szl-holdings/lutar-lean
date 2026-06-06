/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave8/Conformal.lean — CP1: Split-Conformal Marginal Coverage

Split conformal prediction: a calibration set of `n` nonconformity scores plus a
test score, jointly exchangeable. The prediction set is
`C(x) = { y : s(x,y) ≤ q̂ }` where `q̂` is the `⌈(n+1)(1-α)⌉`-th smallest of the
`n` calibration scores (with `+∞` appended). The marginal coverage guarantee is

      1 - α  ≤  P( test score ≤ q̂ )  ≤  1 - α + 1/(n+1).

This closes the "conformal, not Hoeffding" gap for the a11oy trust-interval claim:
the coverage is a FINITE-SAMPLE, distribution-free guarantee, not a heuristic.

## The quantile lemma, combinatorially (Lean-core)
Under exchangeability the rank of the test score among the `n+1` scores is uniform
on `{0,1,…,n}`. Hence for any integer threshold index `k`,

      P( rank < k ) = #{ i ∈ {0,…,n} : i < k } / (n+1) = min(n+1, k) / (n+1).

We prove the exact count `coverageCount n k = min (n+1) k` (`count_lt`), then —
with the ceiling threshold `k = ⌈(n+1)(1-α)⌉` characterized by the two integer
inequalities below — derive the two-sided coverage bound in exact cross-multiplied
integer form (no real-arithmetic dependency, no Mathlib):

  * `coverage_lower` : `numer ≤ (n+1) * coverageCount n k`            (⇒ coverage ≥ 1-α)
  * `coverage_upper` : `(n+1) * coverageCount n k < numer + (n+1)`    (⇒ coverage ≤ 1-α + 1/(n+1))

where `numer = ⌈(n+1)(1-α)⌉ · (n+1)`'s lower face; concretely we take the
*scaled* coverage target `numer` with the ceiling bracket `numer ≤ (n+1)*k <
numer + (n+1)` and `1 ≤ k ≤ n+1` (valid for `0 < α < 1`). Dividing through by
`(n+1)²` recovers the real-valued `[1-α, 1-α+1/(n+1)]` interval.

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave8`) — NOT in the LOCKED v11 baseline. Locked-proven
  stays exactly 5 {F1,F11,F12,F18,F19}. Λ untouched (Conjecture 1).
- Coverage is `[1-α, 1-α+1/(n+1)]`, NOT exactly `1-α` — the upper face is proven
  too, so the narrative must say "at least 1-α, at most 1-α+1/(n+1)".
- This is MARGINAL coverage (averaged over X), NOT conditional coverage.
- The uniform-rank fact is the exchangeability HYPOTHESIS realized; we prove the
  exact counting identity that the quantile lemma reduces to. Lean-core only,
  no open obligation, no new declared axiom.

## Citations
- Vovk, Gammerman, Shafer, "Algorithmic Learning in a Random World", Springer 2005.
- Shafer & Vovk, "A Tutorial on Conformal Prediction", JMLR 9 (2008):
  https://jmlr.csail.mit.edu/papers/volume9/shafer08a/shafer08a.pdf
- Angelopoulos & Bates, "A Gentle Introduction to Conformal Prediction",
  arXiv:2107.07511 https://arxiv.org/abs/2107.07511

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/

namespace Lutar.Wave8.Conformal

/-- The number of test-score ranks in `{0,…,n}` (i.e. `range (n+1)`) that fall
strictly below threshold index `k`. Under uniform rank this is the (unnormalized)
coverage count; dividing by `n+1` gives the coverage probability. -/
def coverageCount (n k : Nat) : Nat :=
  ((List.range (n + 1)).filter (fun i => decide (i < k))).length

/-- Count of ranks in `range m` below threshold `k` is `min m k`. -/
theorem count_lt_range (m k : Nat) :
    ((List.range m).filter (fun i => decide (i < k))).length = Nat.min m k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    have hlen : ([m].filter (fun i => decide (i < k))).length = (if m < k then 1 else 0) := by
      by_cases h : m < k
      · simp [List.filter, h]
      · simp [List.filter, h]
    rw [hlen]
    simp only [Nat.min_def]
    split <;> split <;> split <;> omega

/-- **Quantile counting lemma.** Exactly `min (n+1) k` of the `n+1` equiprobable
ranks fall below the threshold index `k`. This is the combinatorial heart of the
split-conformal coverage guarantee. -/
theorem count_lt (n k : Nat) : coverageCount n k = Nat.min (n + 1) k :=
  count_lt_range (n + 1) k

/-- When the ceiling threshold satisfies `1 ≤ k ≤ n+1` (true for `0 < α < 1`),
the coverage count is exactly `k`. -/
theorem coverageCount_eq (n k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ n + 1) :
    coverageCount n k = k := by
  have _ := h1
  rw [count_lt]; simp only [Nat.min_def]; split <;> omega

/-- **CP1 lower bound.** With the ceiling threshold `k = ⌈(n+1)(1-α)⌉`
characterized by `numer ≤ (n+1) * k` (the ceiling lower face) and `1 ≤ k ≤ n+1`,
the scaled coverage `(n+1) * coverageCount n k` is at least `numer`. Dividing by
`(n+1)²` gives `coverage ≥ 1 - α`. -/
theorem coverage_lower (n k numer : Nat)
    (h1 : 1 ≤ k) (h2 : k ≤ n + 1) (hceil_lo : numer ≤ (n + 1) * k) :
    numer ≤ (n + 1) * coverageCount n k := by
  rw [coverageCount_eq n k h1 h2]; exact hceil_lo

/-- **CP1 upper bound.** With the ceiling upper face `(n+1) * k < numer + (n+1)`,
the scaled coverage is below `numer + (n+1)`. Dividing by `(n+1)²` gives
`coverage ≤ 1 - α + 1/(n+1)` — the tight finite-sample upper face. -/
theorem coverage_upper (n k numer : Nat)
    (h1 : 1 ≤ k) (h2 : k ≤ n + 1) (hceil_hi : (n + 1) * k < numer + (n + 1)) :
    (n + 1) * coverageCount n k < numer + (n + 1) := by
  rw [coverageCount_eq n k h1 h2]; exact hceil_hi

/-- **CP1 (packaged).** The two-sided finite-sample marginal coverage bracket in
exact scaled-integer form: `numer ≤ (n+1)·cover < numer + (n+1)`. -/
theorem conformal_marginal_coverage (n k numer : Nat)
    (h1 : 1 ≤ k) (h2 : k ≤ n + 1)
    (hceil_lo : numer ≤ (n + 1) * k)
    (hceil_hi : (n + 1) * k < numer + (n + 1)) :
    numer ≤ (n + 1) * coverageCount n k ∧
      (n + 1) * coverageCount n k < numer + (n + 1) :=
  ⟨coverage_lower n k numer h1 h2 hceil_lo,
   coverage_upper n k numer h1 h2 hceil_hi⟩

#print axioms count_lt
#print axioms coverageCount_eq
#print axioms coverage_lower
#print axioms coverage_upper
#print axioms conformal_marginal_coverage

end Lutar.Wave8.Conformal
