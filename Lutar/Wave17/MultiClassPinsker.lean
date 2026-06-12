/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 17 — CF-23-FULL: multi-class (k-bin) Pinsker via the binary data-processing reduction

## Honesty verdict first (philosophers' enforcement)

This file discharges **roadmap step 2** recorded in `Lutar.Wave15.PinskerRoadmap`: the
data-processing reduction from the proven binary bound `Lutar.Wave17.binary_pinsker` to the
multi-class case, using the proven log-sum inequality `Lutar.Wave14.log_sum_inequality`.

What is proven here (NO sorry, NO new axiom):

* `klSum_ge_twoCell` — two-cell data-processing lower bound: for strictly-positive `p, q` on a
  finset `s` and ANY decidable partition predicate `pr`, the KL sum dominates the sum of the two
  coarsened cell binary-KL terms `(Σ_cell p)·log((Σ_cell p)/(Σ_cell q))`. This is the log-sum /
  DPI core, applied on each cell plus the `filter`/`filter ¬` split.
* `multiclass_pinsker` — the headline. For a probability-vector pair (`∑ p = ∑ q = 1`, strictly
  positive) and a **non-degenerate** partition (cell mass `P = Σ_{pr} p ∈ (0,1)` under `p` and
  `Q = Σ_{pr} q ∈ (0,1)` under `q`), `2·(P − Q)² ≤ Σ pᵢ·log(pᵢ/qᵢ) = KL(p‖q)`. Taking
  `pr = (qᵢ ≤ pᵢ)` gives `P − Q = TV(p,q) = ½‖p−q‖₁`, recovering classical `2·TV² ≤ KL`.

## Honesty / scope
- EXPERIMENTAL (`Lutar/Wave17/`). NO new axiom; NO sorry. Locked-proven set unchanged.
- CONDITIONAL on the stated non-degeneracy (`0 < P < 1`, `0 < Q < 1`): a degenerate partition
  (one cell carrying all the mass under `p` or under `q`) is excluded, exactly as the binary base
  case requires `p, q ∈ (0,1)`. The in-tree DPO axiom `Lutar.DPOFeasibility.pinsker` stays
  FALSE-as-stated, token UNTOUCHED. Λ unchanged (Conjecture 1, machine-FALSE unconditional).

## References
- Cover, T.M. & Thomas, J.A. (2006). *Elements of Information Theory*, 2nd ed., Wiley.
  Thm 11.6.1 (Pinsker), Lemma 11.6.1 (binary reduction), Thm 2.7.1 (log-sum). ISBN 978-0-471-24195-9.

Signed-off-by: SZL CTO <cto@szl-holdings.com>
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lutar.Wave14.LogSumInequality
import Lutar.Wave17.BinaryPinsker

namespace Lutar.Wave17

open Real Finset BigOperators

variable {ι : Type*}

/-- **Two-cell data-processing lower bound.**  For strictly-positive `p, q` on a finset `s` and a
    decidable partition predicate `pr`, the KL sum dominates the sum of the two cell binary-KL
    terms `(Σ_cell p)·log((Σ_cell p)/(Σ_cell q))`.  Immediate from the log-sum inequality applied
    on each cell, plus the `filter`/`filter ¬` split of the sum. -/
theorem klSum_ge_twoCell (s : Finset ι) (pr : ι → Prop) [DecidablePred pr]
    (p q : ι → ℝ) (hp : ∀ i ∈ s, 0 < p i) (hq : ∀ i ∈ s, 0 < q i) :
    (∑ i ∈ s.filter pr, p i) * Real.log ((∑ i ∈ s.filter pr, p i) / (∑ i ∈ s.filter pr, q i))
      + (∑ i ∈ s.filter (fun i => ¬ pr i), p i)
          * Real.log ((∑ i ∈ s.filter (fun i => ¬ pr i), p i)
              / (∑ i ∈ s.filter (fun i => ¬ pr i), q i))
      ≤ ∑ i ∈ s, p i * Real.log (p i / q i) := by
  have hpA : ∀ i ∈ s.filter pr, 0 < p i := fun i hi => hp i (Finset.mem_filter.mp hi).1
  have hqA : ∀ i ∈ s.filter pr, 0 < q i := fun i hi => hq i (Finset.mem_filter.mp hi).1
  have hpB : ∀ i ∈ s.filter (fun i => ¬ pr i), 0 < p i :=
    fun i hi => hp i (Finset.mem_filter.mp hi).1
  have hqB : ∀ i ∈ s.filter (fun i => ¬ pr i), 0 < q i :=
    fun i hi => hq i (Finset.mem_filter.mp hi).1
  have hA := Lutar.Wave14.log_sum_inequality (s.filter pr) p q hpA hqA
  have hB := Lutar.Wave14.log_sum_inequality (s.filter (fun i => ¬ pr i)) p q hpB hqB
  have hsplit :
      (∑ i ∈ s.filter pr, p i * Real.log (p i / q i))
        + (∑ i ∈ s.filter (fun i => ¬ pr i), p i * Real.log (p i / q i))
        = ∑ i ∈ s, p i * Real.log (p i / q i) :=
    Finset.sum_filter_add_sum_filter_not s pr (fun i => p i * Real.log (p i / q i))
  linarith [hA, hB, hsplit]

/-- **Multi-class (k-bin) Pinsker inequality (conditional on a non-degenerate partition).**
    For a probability-vector pair `p, q` on a finset `s` (`∑ p = ∑ q = 1`, strictly positive) and a
    decidable partition predicate `pr` whose `pr`-cell carries mass `P = Σ_{pr} p ∈ (0,1)` under `p`
    and `Q = Σ_{pr} q ∈ (0,1)` under `q`,
      `2·(P − Q)² ≤ Σ pᵢ·log(pᵢ/qᵢ)`.
    With `pr = (qᵢ ≤ pᵢ)` one has `P − Q = TV(p,q) = ½‖p−q‖₁`, recovering classical Pinsker
    `2·TV² ≤ KL`.  Proof: the two-cell DPI lower bound (`klSum_ge_twoCell`) plus the simplex
    relations (`P' = 1−P`, `Q' = 1−Q`) reduce the claim to the proven binary case
    `binary_pinsker`. -/
theorem multiclass_pinsker (s : Finset ι) (pr : ι → Prop) [DecidablePred pr]
    (p q : ι → ℝ) (hp : ∀ i ∈ s, 0 < p i) (hq : ∀ i ∈ s, 0 < q i)
    (hps : ∑ i ∈ s, p i = 1) (hqs : ∑ i ∈ s, q i = 1)
    (hP0 : 0 < ∑ i ∈ s.filter pr, p i) (hP1 : (∑ i ∈ s.filter pr, p i) < 1)
    (hQ0 : 0 < ∑ i ∈ s.filter pr, q i) (hQ1 : (∑ i ∈ s.filter pr, q i) < 1) :
    2 * ((∑ i ∈ s.filter pr, p i) - (∑ i ∈ s.filter pr, q i)) ^ 2
      ≤ ∑ i ∈ s, p i * Real.log (p i / q i) := by
  have hpc : (∑ i ∈ s.filter (fun i => ¬ pr i), p i) = 1 - (∑ i ∈ s.filter pr, p i) := by
    have h := Finset.sum_filter_add_sum_filter_not s pr p
    linarith [h, hps]
  have hqc : (∑ i ∈ s.filter (fun i => ¬ pr i), q i) = 1 - (∑ i ∈ s.filter pr, q i) := by
    have h := Finset.sum_filter_add_sum_filter_not s pr q
    linarith [h, hqs]
  have htc := klSum_ge_twoCell s pr p q hp hq
  rw [hpc, hqc] at htc
  rw [Real.log_div (ne_of_gt hP0) (ne_of_gt hQ0),
      Real.log_div (ne_of_gt (by linarith : (0:ℝ) < 1 - (∑ i ∈ s.filter pr, p i)))
        (ne_of_gt (by linarith : (0:ℝ) < 1 - (∑ i ∈ s.filter pr, q i)))] at htc
  have hbp := binary_pinsker (∑ i ∈ s.filter pr, q i) (∑ i ∈ s.filter pr, p i) hQ0 hQ1 hP0 hP1
  linarith [htc, hbp]

end Lutar.Wave17
