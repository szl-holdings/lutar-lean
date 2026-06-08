/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 16 — CF-25: Λ product-multiplicativity ⇒ MPP normalization-invariance (axiom-free)

## What is PROVEN here (no sorry / NO new axiom token)

The Multiple-Physics-Pretraining (MPP, arXiv:2310.02994, MIT) discipline is a *shared normalized
embedding space*: each heterogeneous "organ" is rescaled into one latent before fusion, and the
fused score must not depend on each organ's arbitrary per-organ scale. For the Λ aggregator
(geometric mean with unit-fraction weights) this invariance has a clean closed form:

* `lambda_mul_vec` — Λ is **product-multiplicative across vectors**: for any `c x : Axes k`,
      `Λ k (fun i => c i * x i) = Λ k c * Λ k x`.
  (The geometric mean of a Hadamard product factors as the product of the geometric means.)
* `lambda_scale_axes` — the MPP **per-organ rescaling law**: scaling each axis `i` by a positive
  factor `c i` multiplies the fused score by exactly `Λ k c` (the geometric mean of the scales):
      `Λ k (fun i => c i * x i) = Λ k c * Λ k x`  (same statement, named for the tab).
* `lambda_normalization_invariant` — **scale-robustness**: if two scale vectors share the same
  geometric mean (`Λ k c = Λ k c'`), then rescaling `x` by `c` vs `c'` gives the SAME fused score.
  In particular, any rescaling whose scales have geometric mean `1` leaves Λ invariant:
      `Λ k c = 1 → Λ k (fun i => c i * x i) = Λ k x`.
  This is the honest formal statement of "MPP shared-normalized-embedding fusion is invariant to
  per-organ normalization choices that preserve the geometric-mean budget."

All three are direct consequences of `Finset.prod_mul_distrib` + `NNReal.mul_rpow`; no analysis
beyond `rpow` algebra, fully turnkey in Mathlib v4.18.0.

## Honesty / scope
- EXPERIMENTAL companion (`Lutar/Wave16/`). Concept-level adoption of MPP (MIT) — NO code copied.
  These are genuine new theorems about the in-tree `Λ`, NOT a restatement of the 1-homogeneity
  axiom A2 (which only covers the *uniform* scale `c i = c`; here each axis scales independently).
- Locked-proven set unchanged. NO new axiom; NO sorry.

## References
- McCabe, M. et al. (2023). Multiple Physics Pretraining for Physical Surrogate Models.
  arXiv:2310.02994. Repo PolymathicAI/multiple_physics_pretraining (SPDX: MIT, verified).
- Hardy, Littlewood, Pólya (1934). *Inequalities*, §2.5 (geometric mean of products).

Signed-off-by: SZL CTO <cto@szl-holdings.com>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/
import Lutar.Invariant
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Lutar.Wave16

open NNReal BigOperators

/-- **CF-25 — Λ product-multiplicativity.** The geometric mean of a Hadamard (pointwise) product
    factors as the product of the geometric means:
      `Λ k (fun i => c i * x i) = Λ k c * Λ k x`.
    Proof: `∏ (cᵢ·xᵢ) = (∏ cᵢ)(∏ xᵢ)` then `(uv)^(1/k) = u^(1/k) · v^(1/k)`. -/
theorem lambda_mul_vec {k : ℕ} (hk : 0 < k) (c x : Axes k) :
    Λ k (fun i => c i * x i) = Λ k c * Λ k x := by
  rw [Λ_def hk, Λ_def hk, Λ_def hk]
  rw [Finset.prod_mul_distrib, NNReal.mul_rpow]

/-- **CF-25 — MPP per-organ rescaling law.** Rescaling each axis `i` by a positive factor `c i`
    multiplies the fused Λ score by exactly `Λ k c`, the geometric mean of the scale vector.
    (Named for the Trust Space / MPP tab; same content as `lambda_mul_vec`.) -/
theorem lambda_scale_axes {k : ℕ} (hk : 0 < k) (c x : Axes k) :
    Λ k (fun i => c i * x i) = Λ k c * Λ k x :=
  lambda_mul_vec hk c x

/-- **CF-25 — MPP normalization-invariance (scale-robustness).** If a per-organ rescaling has
    geometric-mean budget `1` (`Λ k c = 1`), the fused Λ score is unchanged:
      `Λ k (fun i => c i * x i) = Λ k x`.
    Formalizes "MPP shared-embedding fusion is invariant to normalization choices that preserve
    the geometric-mean budget." -/
theorem lambda_normalization_invariant {k : ℕ} (hk : 0 < k) (c x : Axes k)
    (hc : Λ k c = 1) :
    Λ k (fun i => c i * x i) = Λ k x := by
  rw [lambda_mul_vec hk, hc, one_mul]

/-- **CF-25 — budget-equivalent rescalings agree.** Two scale vectors with equal geometric-mean
    budget produce identical fused scores under per-axis rescaling. -/
theorem lambda_rescale_eq_of_budget_eq {k : ℕ} (hk : 0 < k) (c c' x : Axes k)
    (h : Λ k c = Λ k c') :
    Λ k (fun i => c i * x i) = Λ k (fun i => c' i * x i) := by
  rw [lambda_mul_vec hk, lambda_mul_vec hk, h]

end Lutar.Wave16
