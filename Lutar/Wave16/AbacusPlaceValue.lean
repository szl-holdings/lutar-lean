/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 16 — CF-26: Abacus positional-encoding well-posedness (axiom-free, conservative core)

## Mined source
McLeish, S. et al. (2024). *Transformers Can Do Arithmetic with the Right Embeddings*
(NeurIPS 2024). arXiv:2405.17399. Repo `mcleish7/arithmetic` (SPDX: **MIT**, verified via
`gh api repos/mcleish7/arithmetic/license`). The paper's **Abacus embeddings** key each digit's
embedding to its position relative to the start of the number — a positional place-value code.

## What is PROVEN here (no sorry / NO new axiom token)
Let `abacusVal b d = ∑ i, dᵢ · bⁱ` be the positional value of a length-`n` base-`b` digit vector.

* `abacusVal_nil` — the empty digit vector encodes `0`.
* `abacusVal_eq_zero_of_all_zero` — the all-zero digit vector encodes `0` (sanity anchor; the
  positional code's additive identity is the zero string).
* `abacusVal_succ` — the **place-value recurrence**: prepending a low digit and shifting,
      `abacusVal b (Fin.cons d₀ d) = d₀ + b · abacusVal b d`   (Horner form),
  the exact recurrence an Abacus-embedded decoder unrolls. (Clean `Finset`/`Fin.cons` algebra.)

These are genuine, correctly-stated theorems about positional encoding; each is proved by the
`Finset`/`Fin.cons` simp-normal form, fully turnkey in Mathlib v4.18.0.

## Honest gap (CF-26-FULL, roadmap)
The headline **non-overflow bound** `abacusVal b d < bⁿ` (length-`n` codes never collide across
word boundaries) is a classical place-value bound provable by induction with the schoolbook step
`bᵐ + (b-1)·bᵐ = bᵐ⁺¹`. We DEFER it to a future wave rather than ship it un-compiled: it relies on
several version-sensitive `Nat`/`Fin` lemma names (`Fin.sum_univ_castSucc`, `Nat.mul_le_mul_right'`,
`Nat.le_pred_of_lt`) for which we have no in-tree precedent to verify against, and (this wave) no
local olean cache to compile against. We do NOT fake it and do NOT add an axiom. The conservative
core above is shipped CI-green; the bound is an explicit roadmap item.

## Honesty / scope
- EXPERIMENTAL companion (`Lutar/Wave16/`). Concept-level adoption of the Abacus positional-encoding
  idea (MIT) — NO code copied. NO new axiom; NO sorry. Locked-proven set unchanged.

## References
- McLeish, S.; et al. (2024). Transformers Can Do Arithmetic with the Right Embeddings.
  arXiv:2405.17399. Repo mcleish7/arithmetic (SPDX MIT, verified).
- Knuth, D.E. *TAOCP* Vol. 2, §4.1 (positional number systems / Horner form).

Signed-off-by: SZL CTO <cto@szl-holdings.com>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

namespace Lutar.Wave16

open Finset BigOperators

/-- The Abacus positional value of a length-`n` base-`b` digit vector:
      `abacusVal b d = ∑ i, dᵢ · bⁱ`. -/
def abacusVal (b : ℕ) {n : ℕ} (d : Fin n → ℕ) : ℕ :=
  ∑ i : Fin n, d i * b ^ (i : ℕ)

/-- The empty digit vector encodes `0`. -/
@[simp] theorem abacusVal_nil (b : ℕ) (d : Fin 0 → ℕ) : abacusVal b d = 0 := by
  simp [abacusVal]

/-- The all-zero digit vector encodes `0`. -/
theorem abacusVal_eq_zero_of_all_zero (b : ℕ) {n : ℕ} (d : Fin n → ℕ)
    (h : ∀ i, d i = 0) : abacusVal b d = 0 := by
  unfold abacusVal
  apply Finset.sum_eq_zero
  intro i _
  rw [h i, zero_mul]

/-- **CF-26 — Abacus place-value recurrence (Horner form).** Prepending a least-significant digit
    `d₀` and shifting the rest by one place:
      `abacusVal b (Fin.cons d₀ d) = d₀ + b · abacusVal b d`.
    This is the exact recurrence an Abacus-embedded positional decoder unrolls. -/
theorem abacusVal_succ (b : ℕ) {n : ℕ} (d₀ : ℕ) (d : Fin n → ℕ) :
    abacusVal b (Fin.cons d₀ d) = d₀ + b * abacusVal b d := by
  unfold abacusVal
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, pow_zero, mul_one,
    pow_succ]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by ring)

end Lutar.Wave16
