/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Uniqueness/Identifiability.lean — Identifiability Assumptions (IA) + Conjecture 1 intake

This module packages the **identifiability assumptions** under which Λ-uniqueness becomes a
THEOREM (Theorem U, proved in `TheoremU.lean` by reduction to the already-proven Round13
conditional theorems), and states the still-OPEN unconditional **Conjecture 1** in the exact
shape the `szl-holdings/lambda-bounty` intake expects, so an external A6/bisymmetry proof
drops in and auto-upgrades it.

## What is PROVEN here (placeholder-free; NO new `axiom` token)

* `FactorAssumptions` / `SeparableAssumptions` / `IdentifiabilityAssumptions` — record
  bundles of the well-posedness + separability + normalization data an aggregator must carry
  for the uniqueness reduction. (`Type`-valued: they carry the slice/exponent data.)
* `separableAssumptions_to_IA`, `factorAssumptions_to_IA` — bridges showing the factored and
  separable hypothesis bundles each refine into `IdentifiabilityAssumptions`. The factor
  bridge derives the multiplicative/monotone/unit slices `t ↦ t^(αᵢ)` via `NNReal.mul_rpow`,
  `NNReal.one_rpow`, `NNReal.rpow_le_rpow`.
* `Anchored` / `Normalized` — the budget-1 gauge fixing: `Λ k` is the canonical representative
  of its own `≈Λ` fiber (Wave16 `lambda_normalization_invariant`: rescalings of geometric-mean
  budget `1` leave `Λ` fixed). Strict `=` is recoverable from `≈Λ` only under this anchoring
  (see `TheoremU.lambda_equiv_to_eq_of_anchored`).

## OPEN obligation (NOT proven; bounty intake)
* `Conjecture1_LambdaUnique` — the UNCONDITIONAL statement "any two A1–A5 aggregators agree".
  It is stated only as a `Prop` (no proof), and it is **machine-checked false** as stated:
  `Round13.maxAgg_ne_Lambda` plus `LambdaEquiv.lambdaEquiv_nondegenerate` exhibit two A1–A5
  aggregators that disagree. Λ therefore stays **Conjecture 1**; closing it soundly needs a
  NEW axiom A6 (bisymmetry, Kolmogorov–Nagumo–Aczél), a founder decision, not fabricated here.

## Honesty / scope
- Locked-proven set unchanged (EXACTLY 5). NO new `axiom`; no proof placeholders.

## References
- Aczél, J. (1966). *Lectures on Functional Equations.* §5.1, §6.4 (bisymmetry).
- Kolmogorov (1930); Nagumo (1930); de Finetti (1931) — quasi-arithmetic means.
- Hardy, Littlewood, Pólya (1934). *Inequalities.* §2.18.

Signed-off-by: SZL CTO <cto@szl-holdings.com>
-/
import Lutar.Axioms
import Lutar.Invariant
import Lutar.Round13.Lambda_Uniqueness
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Lutar.Uniqueness

open Lutar Lutar.Round13 NNReal BigOperators

/-! ## Hypothesis bundles -/

/-- **Factor assumptions.** `Φ` is a well-posed A1–A5 aggregator that factors into per-axis
    power laws with exponents `exps`. (`Type`-valued: carries the exponent data.) -/
structure FactorAssumptions {k : ℕ} (Φ : Aggregator k) where
  /-- Well-posedness: positive dimension. -/
  pos : 0 < k
  /-- `Φ` satisfies the Lutar axioms A1–A5. -/
  axioms : LutarAxioms Φ
  /-- Per-axis exponents. -/
  exps : Fin k → NNReal
  /-- `Φ` factors as the exponential product `∏ xᵢ ^ (expsᵢ)`. -/
  factors : Factors Φ exps

/-- **Separable assumptions.** `Φ` is a well-posed A1–A5 aggregator that *separates* into
    multiplicative, unit-normalized, monotone per-axis slices — strictly weaker than assuming
    the exponential shape outright. (`Type`-valued: carries the slice data.) -/
structure SeparableAssumptions {k : ℕ} (Φ : Aggregator k) where
  /-- Well-posedness: positive dimension. -/
  pos : 0 < k
  /-- `Φ` satisfies the Lutar axioms A1–A5. -/
  axioms : LutarAxioms Φ
  /-- Per-axis slice maps. -/
  slices : Fin k → (NNReal → NNReal)
  /-- Separability: `Φ` is the product of its per-axis slices. -/
  separates : ∀ x, Φ x = ∏ i, slices i (x i)
  /-- Each slice is multiplicative. -/
  slice_mul : ∀ i s t, slices i (s * t) = slices i s * slices i t
  /-- Each slice is unit-normalized. -/
  slice_one : ∀ i, slices i 1 = 1
  /-- Each slice is monotone. -/
  slice_mono : ∀ i, Monotone (slices i)

/-- **Identifiability Assumptions (IA).** The canonical bundle under which the Λ aggregator is
    *identifiable*: existence/well-posedness (`pos`, `axioms`), separability/injectivity of the
    per-axis response (`slices`, `separates`, `slice_mul`), and normalization (`slice_one`,
    `slice_mono`). Theorem U concludes Λ-uniqueness (modulo `≈Λ`, indeed `=`) from IA. -/
structure IdentifiabilityAssumptions {k : ℕ} (Φ : Aggregator k) where
  /-- Existence / well-posedness: positive dimension. -/
  pos : 0 < k
  /-- `Φ` satisfies the Lutar axioms A1–A5. -/
  axioms : LutarAxioms Φ
  /-- Per-axis slice maps (the identifiable per-organ response). -/
  slices : Fin k → (NNReal → NNReal)
  /-- Separability / injectivity of the response: `Φ = ∏ slices`. -/
  separates : ∀ x, Φ x = ∏ i, slices i (x i)
  /-- Multiplicativity of each slice. -/
  slice_mul : ∀ i s t, slices i (s * t) = slices i s * slices i t
  /-- Normalization: each slice fixes `1`. -/
  slice_one : ∀ i, slices i 1 = 1
  /-- Non-degeneracy / monotonicity of each slice. -/
  slice_mono : ∀ i, Monotone (slices i)

/-! ## Bridges into IA -/

/-- Separable assumptions refine directly into Identifiability Assumptions. -/
def separableAssumptions_to_IA {k : ℕ} {Φ : Aggregator k}
    (sa : SeparableAssumptions Φ) : IdentifiabilityAssumptions Φ where
  pos := sa.pos
  axioms := sa.axioms
  slices := sa.slices
  separates := sa.separates
  slice_mul := sa.slice_mul
  slice_one := sa.slice_one
  slice_mono := sa.slice_mono

/-- Factor assumptions refine into Identifiability Assumptions: the power-law slices
    `t ↦ t^(αᵢ)` are multiplicative (`NNReal.mul_rpow`), unit-normalized (`NNReal.one_rpow`),
    and monotone (`NNReal.rpow_le_rpow`, exponent `≥ 0`). `noncomputable` because the
    power-law slices `t ↦ t^(αᵢ)` use `NNReal.rpow` (real exponent), which has no executable code. -/
noncomputable def factorAssumptions_to_IA {k : ℕ} {Φ : Aggregator k}
    (fa : FactorAssumptions Φ) : IdentifiabilityAssumptions Φ where
  pos := fa.pos
  axioms := fa.axioms
  slices := fun i t => t ^ (fa.exps i : ℝ)
  separates := fa.factors
  slice_mul := fun i s t => by simp only [NNReal.mul_rpow]
  slice_one := fun i => by simp only [NNReal.one_rpow]
  slice_mono := fun i => by
    intro a b h
    exact NNReal.rpow_le_rpow h (fa.exps i).coe_nonneg

/-! ## Gauge anchoring -/

/-- **`Normalized` — budget-1 gauge fixing.** `Φ` is normalized when it coincides with the
    canonical Lutar invariant `Λ k`. By Wave16 `lambda_normalization_invariant`, `Λ` is the
    gauge-anchored fixed point of its own `≈Λ` fiber (rescalings of geometric-mean budget `1`
    leave it invariant), so this is the canonical representative of the fiber. -/
def Normalized {k : ℕ} (Φ : Aggregator k) : Prop := Φ = Λ k

/-- **`Anchored`** — synonym of `Normalized`: `Φ` is anchored to the canonical Λ gauge.
    Strict equality is recoverable from `≈Λ` only under this predicate
    (`TheoremU.lambda_equiv_to_eq_of_anchored`). -/
def Anchored {k : ℕ} (Φ : Aggregator k) : Prop := Normalized Φ

/-! ## Conjecture 1 (OPEN — bounty intake shape) -/

/-- **Conjecture 1 — unconditional Λ-uniqueness (OPEN).** "Any two A1–A5 aggregators agree."

    Stated only as a `Prop`; NO proof is shipped, because as stated it is **machine-checked
    false** (`Round13.maxAgg_ne_Lambda` + `LambdaEquiv.lambdaEquiv_nondegenerate`: `maxAgg` and
    `Λ 2` both satisfy the axioms studied yet disagree). This is the `szl-holdings/lambda-bounty`
    intake shape: a complete machine-checked proof of `Conjecture1_LambdaUnique` (which requires
    a NEW axiom A6 = bisymmetry) drops in and discharges the bounty. Λ stays Conjecture 1. -/
def Conjecture1_LambdaUnique : Prop :=
  ∀ {k : ℕ} (_hk : 0 < k) (Φ Ψ : Aggregator k),
    LutarAxioms Φ → LutarAxioms Ψ → Φ = Ψ

end Lutar.Uniqueness
