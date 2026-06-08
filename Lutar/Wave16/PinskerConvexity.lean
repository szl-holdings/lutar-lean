/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 16 — CF-23 advance: the binary-KL convexity crux for Pinsker (axiom-free)

## Honesty verdict first (philosophers' enforcement)

The in-tree DPO axiom `Lutar.DPOFeasibility.pinsker` (`2·TV² ≤ KL`, equivalently
`½‖p−q‖₁² ≤ KL`) is **FALSE-as-stated** (no simplex hypothesis) and its token is **UNTOUCHED**.
Full conditional (binary-bin) Pinsker `2(p−q)² ≤ KL_bin(p,q)` is NOT proven here. Wave15 confirmed
that `nlinarith` with the loose `log x ≤ x−1` facts FAILS for the quadratic bound; the textbook
proof needs the gap `g(p) = KL_bin(p,q) − 2(p−q)²` to satisfy `g(q)=0`, `g′(q)=0`, and `g″ ≥ 0`
via a mean-value / monotone-derivative argument that is a multi-week Mathlib formalization.

## What THIS wave adds beyond Wave15 (the missing crux, now machine-proven; no sorry / NO new axiom)

The single fact that makes `g″ ≥ 0` — and hence the whole derivative argument — go through is the
**binary-entropy convexity bound**:

* `binary_inv_sum_ge_four` — for `p ∈ (0,1)`,  `4 ≤ 1/p + 1/(1−p)`.
  Since `g″(p) = 1/p + 1/(1−p) − 4`, this is exactly `g″ ≥ 0`. It is the precise analytic gap
  Wave15 flagged as missing; we now supply it (clean, via `(2p−1)² ≥ 0`).

* `binary_inv_sum_eq_four_iff` — equality `1/p + 1/(1−p) = 4` holds iff `p = 1/2` (the unique
  inflection); confirms the bound is TIGHT and pins the minimiser.

These are genuine, correctly-stated theorems — NOT a disguised Pinsker. They reduce the remaining
gap to "assemble the MVT chain from `g″ ≥ 0`", which we honestly document as CF-23-FULL roadmap.

## Roadmap to full conditional Pinsker (CF-23-FULL, future wave)
1. Define `gapFn q p = p·log(p/q)+(1−p)·log((1−p)/(1−q)) − 2(p−q)²`; show `deriv (gapFn q) p
   = log(p/q) − log((1−p)/(1−q)) − 4(p−q)` (Mathlib `Real.deriv_log`, `deriv_const_mul`),
   `gapFn q q = 0`, `deriv (gapFn q) q = 0`, and `deriv^[2] (gapFn q) p = 1/p+1/(1−p)−4 ≥ 0`
   (THIS lemma `binary_inv_sum_ge_four`). Then `StrictMonoOn`/`MonotoneOn` of `deriv (gapFn q)`
   ⇒ `gapFn q ≥ 0`. ~150–250 LoC.
2. Data-processing reduction to the multi-bin case via the `{i : pᵢ ≥ qᵢ}` partition (CF-21 supplies
   the log-sum core). ~200 LoC.

## Honesty / scope
- EXPERIMENTAL companion (`Lutar/Wave16/`). NO new axiom; NO sorry. Locked-proven set unchanged.
- DPO `pinsker` stays FALSE-as-stated, token UNTOUCHED. Λ unchanged (Conjecture 1).

## References
- Pinsker, M.S. (1964). *Information and Information Stability*, AN SSSR. §2.2.
- Cover, T.M. & Thomas, J.A. (2006). *Elements of Information Theory*, 2nd ed., Wiley.
  Thm 11.6.1 (Pinsker), Lemma 11.6.1 (binary reduction). ISBN 978-0-471-24195-9.

Signed-off-by: SZL CTO <cto@szl-holdings.com>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Lutar.Wave16

open Real

/-- **CF-23 advance — binary-entropy convexity crux.** For `p ∈ (0,1)`,
      `4 ≤ 1/p + 1/(1−p)`.
    This is exactly the second-derivative nonnegativity `g″(p) = 1/p + 1/(1−p) − 4 ≥ 0` of the
    binary Pinsker gap `g(p) = KL_bin(p,q) − 2(p−q)²` — the analytic fact Wave15 flagged as the
    missing piece. Proof: clear denominators, then `(2p−1)² ≥ 0`. -/
theorem binary_inv_sum_ge_four (p : ℝ) (h0 : 0 < p) (h1 : p < 1) :
    4 ≤ 1 / p + 1 / (1 - p) := by
  have hp1 : 0 < 1 - p := by linarith
  rw [div_add_div _ _ (ne_of_gt h0) (ne_of_gt hp1), le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (2 * p - 1)]

/-- **CF-23 advance — tightness / minimiser.** The convexity bound is tight exactly at the
    inflection `p = 1/2`:  `1/p + 1/(1−p) = 4 ↔ p = 1/2` (for `p ∈ (0,1)`). -/
theorem binary_inv_sum_eq_four_iff (p : ℝ) (h0 : 0 < p) (h1 : p < 1) :
    1 / p + 1 / (1 - p) = 4 ↔ p = 1 / 2 := by
  have hp1 : 0 < 1 - p := by linarith
  rw [div_add_div _ _ (ne_of_gt h0) (ne_of_gt hp1), div_eq_iff (by positivity)]
  constructor
  · intro h
    have hsq : (2 * p - 1) ^ 2 = 0 := by nlinarith [h]
    have : 2 * p - 1 = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
      linarith [this]
    linarith
  · intro h; rw [h]; ring

end Lutar.Wave16
