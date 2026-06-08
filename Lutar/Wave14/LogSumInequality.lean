/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 14 — CF-21: Log-sum inequality & Gibbs' inequality (clean, axiom-free)

The data-processing inequality (DPI) and non-negativity of KL divergence used throughout the
Khipu / DPO information-theory tabs rest on two classical facts (Cover & Thomas 2006, Thm 2.7.1
"Log sum inequality" and its corollary, Gibbs' inequality / Thm 2.6.3). The in-tree DPO
`klDivergence` / `pinsker` statements are honestly flagged FALSE-as-stated (they assume a
simplex normalisation that is not in the hypotheses). This file proves the genuine, fully
hypothesised inequalities — the building blocks a correctly-stated DPI would compose.

## What is PROVEN here (no sorry / NO new axiom)
* `log_sum_inequality` — for finitely many strictly-positive `aᵢ, bᵢ`,
      `(Σ aᵢ) · log( (Σ aᵢ)/(Σ bᵢ) ) ≤ Σ aᵢ · log( aᵢ/bᵢ )`.
  This is exactly Cover–Thomas Theorem 2.7.1.
* `gibbs_inequality` — for strictly-positive `pᵢ, qᵢ` with equal total mass `Σ p = Σ q`,
      `0 ≤ Σ pᵢ · log( pᵢ/qᵢ )`  (relative entropy non-negativity; Cover–Thomas Thm 2.6.3).
  It is the `Σa = Σb` specialisation of the log-sum inequality (then `log 1 = 0`).

Both are proved from the single convexity fact `Real.log x ≤ x − 1` (`log_le_sub_one_of_pos`),
applied pointwise to the tilted ratios `bᵢ·A / (aᵢ·B)` and summed — the standard textbook proof,
needing no measure theory and no simplex assumption.

## Honesty / scope
- EXPERIMENTAL companion (`Lutar/Wave14/`). Does NOT edit the DPO `klDivergence`/`pinsker`
  statements, which remain honestly FALSE-as-stated (missing simplex hypothesis). This file is
  the *correctly stated* core those would need; folding it into a fixed DPI is future work.
- Locked-proven set unchanged. NO new axiom; NO sorry.

## References
- Cover, T.M. & Thomas, J.A. (2006). *Elements of Information Theory*, 2nd ed., Wiley.
  §2.6–2.7 (Gibbs' inequality Thm 2.6.3; Log sum inequality Thm 2.7.1); DPI Thm 2.8.1.
  ISBN 978-0-471-24195-9.
- Log sum inequality — https://en.wikipedia.org/wiki/Log_sum_inequality
- Csiszár & Körner (2011). *Information Theory: Coding Theorems for Discrete Memoryless
  Systems*, 2nd ed., CUP. (DPI / f-divergence monotonicity.)

Signed-off-by: SZL CTO <cto@szl-holdings.com>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Lutar.Wave14

open Real Finset BigOperators

variable {ι : Type*}

/-- **Log-sum inequality (Cover–Thomas Thm 2.7.1).** For finitely many strictly-positive
    reals `aᵢ, bᵢ` indexed by a finset `s`,
      `(Σ aᵢ) · log((Σ aᵢ)/(Σ bᵢ)) ≤ Σ aᵢ · log(aᵢ/bᵢ)`.

    Proof: apply `log t ≤ t − 1` to `t = (bᵢ·A)/(aᵢ·B)` (with `A = Σa`, `B = Σb`), multiply by
    `aᵢ ≥ 0`, and sum; the right side telescopes to `0`, leaving the claim after splitting the
    logarithm `log((bᵢ·A)/(aᵢ·B)) = log(bᵢ/aᵢ) + log(A/B)`. -/
theorem log_sum_inequality (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) (hb : ∀ i ∈ s, 0 < b i) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i))
      ≤ ∑ i ∈ s, a i * Real.log (a i / b i) := by
  set A := ∑ i ∈ s, a i with hA
  set B := ∑ i ∈ s, b i with hB
  rcases s.eq_empty_or_nonempty with hs | hs
  · subst hs; simp [hA, hB]
  · have hApos : 0 < A := Finset.sum_pos ha hs
    have hBpos : 0 < B := Finset.sum_pos hb hs
    have hbound : ∀ i ∈ s,
        a i * Real.log ((b i * A) / (a i * B)) ≤ (b i * A) / B - a i := by
      intro i hi
      have hai := ha i hi
      have hbi := hb i hi
      have hlog : Real.log ((b i * A) / (a i * B)) ≤ (b i * A) / (a i * B) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      calc a i * Real.log ((b i * A) / (a i * B))
          ≤ a i * ((b i * A) / (a i * B) - 1) :=
            mul_le_mul_of_nonneg_left hlog (le_of_lt hai)
        _ = (b i * A) / B - a i := by field_simp; ring
    have hsum_bound :
        ∑ i ∈ s, a i * Real.log ((b i * A) / (a i * B))
          ≤ ∑ i ∈ s, ((b i * A) / B - a i) := Finset.sum_le_sum hbound
    have hrhs : ∑ i ∈ s, ((b i * A) / B - a i) = 0 := by
      rw [Finset.sum_sub_distrib]
      have h1 : ∑ i ∈ s, (b i * A) / B = A := by
        rw [← Finset.sum_div, ← Finset.sum_mul, ← hB]
        field_simp
      rw [h1, ← hA]; ring
    rw [hrhs] at hsum_bound
    have hdecomp : ∀ i ∈ s,
        a i * Real.log ((b i * A) / (a i * B))
          = a i * Real.log (b i / a i) + a i * Real.log (A / B) := by
      intro i hi
      have hai := ha i hi
      have hbi := hb i hi
      have e : (b i * A) / (a i * B) = (b i / a i) * (A / B) := by
        field_simp
      rw [e, Real.log_mul (by positivity) (by positivity)]; ring
    rw [Finset.sum_congr rfl hdecomp, Finset.sum_add_distrib] at hsum_bound
    have hconst : ∑ i ∈ s, a i * Real.log (A / B) = A * Real.log (A / B) := by
      rw [← Finset.sum_mul, ← hA]
    rw [hconst] at hsum_bound
    have hneg : ∀ i ∈ s, a i * Real.log (b i / a i) = - (a i * Real.log (a i / b i)) := by
      intro i hi
      have hai := ha i hi
      have hbi := hb i hi
      have : Real.log (b i / a i) = - Real.log (a i / b i) := by
        rw [← Real.log_inv, inv_div]
      rw [this]; ring
    rw [Finset.sum_congr rfl hneg] at hsum_bound
    rw [Finset.sum_neg_distrib] at hsum_bound
    linarith

/-- **Gibbs' inequality (Cover–Thomas Thm 2.6.3).** For strictly-positive `pᵢ, qᵢ` of equal
    total mass `Σ p = Σ q`, the relative entropy is non-negative:
      `0 ≤ Σ pᵢ · log(pᵢ/qᵢ)`.

    Immediate from the log-sum inequality at `a = p`, `b = q`: the left side becomes
    `(Σp)·log((Σp)/(Σq)) = (Σp)·log 1 = 0`. -/
theorem gibbs_inequality (s : Finset ι) (p q : ι → ℝ)
    (hp : ∀ i ∈ s, 0 < p i) (hq : ∀ i ∈ s, 0 < q i)
    (hsum : ∑ i ∈ s, p i = ∑ i ∈ s, q i) :
    0 ≤ ∑ i ∈ s, p i * Real.log (p i / q i) := by
  have hls := log_sum_inequality s p q hp hq
  rw [hsum] at hls
  rcases s.eq_empty_or_nonempty with hs | hs
  · subst hs; simp
  · have hQpos : 0 < ∑ i ∈ s, q i := Finset.sum_pos hq hs
    rw [div_self (ne_of_gt hQpos), Real.log_one, mul_zero] at hls
    exact hls

end Lutar.Wave14
