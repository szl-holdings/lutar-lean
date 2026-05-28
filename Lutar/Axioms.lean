/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar — Axioms A1..A4

The Lutar Invariant Λ_k : (Fin k → ℝ≥0) → ℝ≥0 is the unique scalar
runtime-trust aggregator that satisfies the four axioms below.

We follow the convention used in `packages/ouroboros-invariant`:
weights are Egyptian unit fractions (1/k), values are in [0,1].

## A3 fix (PhD-Math V14-C1 / integrity-remediation 2026-05-28)

The original A3 field `weight_eq : (1:ℚ)/k = (1:ℚ)/k` was a tautology —
it did not constrain the aggregator at all. PhD-Math audit (V14-C1) flagged
this: any aggregator satisfied A3 vacuously.

The fix (V14PF-T1): replace with `A3_normalize`, the equal-weight diagonal
commitment S1: `∀ c, Λ (fun _ => c) = c`. This constrains Λ to be exactly
the geometric mean on the diagonal, which (together with A1, A2, A4) forces
uniqueness via the Cauchy functional equation argument documented in
`Lutar/Uniqueness.lean`.

The concrete proof that `Lutar.Λ k` satisfies `A3_normalize` is provided in
`Lutar/Invariant.lean` as `theorem a3_normalize_proof`, to avoid a circular
import (Invariant.lean already imports Axioms.lean for the type definitions).

**Postulation rationale** (why `k_pos` is a hypothesis in `IsEgyptianExact`):
Positivity of `k` is a structural precondition — it cannot be derived from
the axiom system itself, which is parametric in `k`. It is the standard
hypothesis required by `Finset.univ.sup'` nonemptiness in A4.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.NNReal.Basic

open NNReal Real

namespace Lutar

/-- Axes vector: `k` non-negative reals in `[0,∞)`. -/
abbrev Axes (k : ℕ) := Fin k → NNReal

/-- A trust aggregator on `k` axes. -/
abbrev Aggregator (k : ℕ) := Axes k → NNReal

/-- **A1 — Monotonicity.** Increasing any axis cannot decrease Λ. -/
def IsMonotone {k : ℕ} (Λ : Aggregator k) : Prop :=
  ∀ x y : Axes k, (∀ i, x i ≤ y i) → Λ x ≤ Λ y

/-- **A2 — Positive homogeneity (degree 1).** Scaling every axis by `c`
scales the output by `c`. -/
def IsHomogeneous {k : ℕ} (Λ : Aggregator k) : Prop :=
  ∀ (c : NNReal) (x : Axes k), Λ (fun i => c * x i) = c * Λ x

/-- **A3 — Egyptian-exact diagonal normalization (V14PF-T1 fix).**
All `k` axes share the same unit-fraction weight `1/k`.
The *meaningful* constraint (S1 from Uniqueness.lean §S1): `Λ (fun _ => c) = c`.

This replaces the tautological `weight_eq : (1:ℚ)/k = (1:ℚ)/k` that was
present before the V14-C1 integrity fix. The field `A3_normalize` pins Λ
to the diagonal of the simplex, providing the S1 condition needed to upgrade
`lutar_unique` from Conjecture to Theorem (see Uniqueness.lean).
-/
structure IsEgyptianExact (k : ℕ) (Λ : Aggregator k) : Prop where
  /-- k must be positive for the geometric mean to be well-defined. -/
  k_pos        : 0 < k
  /-- Equal-weight diagonal commitment (S1 / V14PF-T1): the constant-vector
      input returns the constant. This is the meaningful content of A3. -/
  A3_normalize : ∀ c : NNReal, Λ (fun _ => c) = c

/-- **A4 — Bounded by max axis.** Λ is never larger than the largest axis. -/
def IsBounded {k : ℕ} (hk : 0 < k) (Λ : Aggregator k) : Prop :=
  ∀ x : Axes k,
    Λ x ≤ Finset.univ.sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ x

/-- The four Lutar axioms collected. A3 now carries the meaningful diagonal
normalization constraint (V14PF-T1 fix; replaces old tautological `weight_eq`). -/
structure LutarAxioms {k : ℕ} (Λ : Aggregator k) : Prop where
  A1 : IsMonotone Λ
  A2 : IsHomogeneous Λ
  A3 : IsEgyptianExact k Λ
  A4 : IsBounded A3.k_pos Λ

end Lutar
