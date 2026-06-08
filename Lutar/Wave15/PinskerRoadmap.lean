/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 15 — CF-23: Pinsker building blocks + HONEST roadmap (NOT full Pinsker)

## Honesty verdict first (philosophers' enforcement)

The in-tree DPO axiom `Lutar.DPOFeasibility.pinsker`
  `TV(p,q) ≤ √(KL(p‖q) / 2)`  ⟺  `2·TV² ≤ KL`  ⟺  `½‖p−q‖₁² ≤ KL`
is **FALSE-as-stated** (no simplex hypothesis). Its CORRECT, simplex-conditional form is the
classical Pinsker inequality (Cover–Thomas Thm 11.6.1). We DID NOT prove that here, and we do
NOT claim to. The honest reason, machine-confirmed this wave:

* The crux is the **binary per-bin lemma** `2(p−q)² ≤ p·log(p/q) + (1−p)·log((1−p)/(1−q))`.
  This is genuinely TIGHT: the loose convexity bound `log x ≤ x−1` (which suffices for Gibbs /
  CF-22) is **provably insufficient** here — `nlinarith` with the `log ≤ x−1` facts FAILS (we
  ran it). The textbook proof requires a one-variable **derivative sign analysis** of the gap
  `g(p) = KL_bin(p,q) − 2(p−q)²` (g(q)=0, g′(q)=0, and a monotonicity argument on g′), and the
  general k-bin case needs a **data-processing reduction** to the binary channel. Neither is in
  Mathlib v4.18.0; both are multi-week formalizations. **Pinsker therefore stays a roadmap item.**

So `DPOFeasibility.pinsker` stays FALSE-as-stated and its axiom token is UNTOUCHED. CF-22 already
gave the honest *conditional* repair of `klDivergence_nonneg`; Pinsker's conditional repair is
explicitly DEFERRED, not faked.

## What IS proven here (the largest clean honest sub-lemma; no sorry / NO new axiom)

* `gibbs_term_lower` — per-coordinate Gibbs bound `a − b ≤ a·log(a/b)` for `a,b > 0`.
  (From `Real.log_le_sub_one_of_pos` applied to `b/a`.) This is the load-bearing per-term
  inequality behind both CF-22 (sum it on the simplex) and the *first* step of any Pinsker proof.
* `klSum_lower_by_mass_gap` — its summed corollary: `∑(pᵢ − qᵢ) ≤ ∑ pᵢ·log(pᵢ/qᵢ)`. On the
  simplex the LHS is `0`, recovering KL ≥ 0; off the simplex it is the honest *mass-gap* lower
  bound (a correctly-stated, non-vacuous quantity — NOT a tautological stub).

These are genuine, correctly-stated theorems. They are NOT a disguised Pinsker. The quadratic
(squared-L1) lower bound is the part we leave open.

## Roadmap to full conditional Pinsker (CF-23-FULL, future wave)
1. Formalize `binaryKL p q = p·log(p/q) + (1−p)·log((1−p)/(1−q))` and prove
   `2(p−q)² ≤ binaryKL p q` via `deriv`/`StrictMonoOn` of the gap (Mathlib `Real.deriv_log`,
   `MonotoneOn` from nonneg derivative). ~150–250 LoC.
2. Data-processing reduction: for k-bin `p,q`, the binary partition `{i : pᵢ ≥ qᵢ}` gives
   `binaryKL(P(A),Q(A)) ≤ KL(p‖q)` and `‖p−q‖₁ = 2|P(A)−Q(A)|`, yielding the multi-bin form.
   ~200 LoC + the log-sum / DPI monotonicity (CF-21 supplies the core).

## References
- Pinsker, M.S. (1964). *Information and Information Stability*, AN SSSR. §2.2, Thm 2.2.
- Csiszár, I. (1967). *Studia Sci. Math. Hungar.* 2:299–318, eq. (2).
- Cover, T.M. & Thomas, J.A. (2006). *Elements of Information Theory*, 2nd ed., Wiley.
  Thm 11.6.1 (Pinsker), Lemma 11.6.1 (binary reduction). ISBN 978-0-471-24195-9.

Signed-off-by: SZL CTO <cto@szl-holdings.com>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

namespace Lutar.Wave15

open Real Finset BigOperators

variable {ι : Type*}

/-- **CF-23 building block.** Per-coordinate Gibbs lower bound: for `a, b > 0`,
      `a − b ≤ a · log(a / b)`.
    Proof: `log(b/a) ≤ b/a − 1` (`log_le_sub_one_of_pos`), then `log(b/a) = −log(a/b)`, multiply
    by `a > 0`, rearrange. The load-bearing per-term inequality behind Gibbs/KL≥0. -/
theorem gibbs_term_lower (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a - b ≤ a * Real.log (a / b) := by
  have hlog : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have e : Real.log (b / a) = - Real.log (a / b) := by rw [← Real.log_inv, inv_div]
  rw [e] at hlog
  have hmul : a * (- Real.log (a / b)) ≤ a * (b / a - 1) :=
    mul_le_mul_of_nonneg_left hlog (le_of_lt ha)
  have hrhs : a * (b / a - 1) = b - a := by field_simp
  nlinarith [hmul, hrhs]

/-- **CF-23 summed corollary.** Summed mass-gap lower bound for the KL form: for strictly-positive
    `p, q` on a finset `s`,
      `∑ (pᵢ − qᵢ) ≤ ∑ pᵢ · log(pᵢ / qᵢ)`.
    On the simplex (`∑ p = ∑ q`) the LHS is `0`, recovering KL ≥ 0 (cf. CF-22). This is a
    correctly-stated, non-vacuous bound — NOT full Pinsker (no squared-L1 term). -/
theorem klSum_lower_by_mass_gap (s : Finset ι) (p q : ι → ℝ)
    (hp : ∀ i ∈ s, 0 < p i) (hq : ∀ i ∈ s, 0 < q i) :
    ∑ i ∈ s, (p i - q i) ≤ ∑ i ∈ s, p i * Real.log (p i / q i) :=
  Finset.sum_le_sum (fun i hi => gibbs_term_lower (p i) (q i) (hp i hi) (hq i hi))

end Lutar.Wave15
