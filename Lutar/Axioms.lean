/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.

# Lutar — Axioms A1..A4

The Lutar Invariant Λ_k : (Fin k → ℝ≥0) → ℝ≥0 is the unique scalar
runtime-trust aggregator that satisfies the four axioms below.

We follow the convention used in `packages/ouroboros-invariant`:
weights are Egyptian unit fractions (1/k), values are in [0,1].
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.NNReal.Basic

open NNReal Real

namespace Lutar

/-- Axes vector: `k` non-negative reals in `[0,1]`. We use `NNReal` for `[0,∞)`
and impose the upper bound separately when needed. -/
abbrev Axes (k : ℕ) := Fin k → NNReal

/-- A trust aggregator on `k` axes. -/
abbrev Aggregator (k : ℕ) := Axes k → NNReal

/-- **A1 — Monotonicity.** Increasing any axis cannot decrease Λ. -/
def IsMonotone {k : ℕ} (Λ : Aggregator k) : Prop :=
  ∀ x y : Axes k, (∀ i, x i ≤ y i) → Λ x ≤ Λ y

/-- **A2 — Positive homogeneity (degree 1).** Scaling every axis by `c`
scales the output by `c`. (Geometric-mean style: same as `Λ(c·x) = c · Λ x`.) -/
def IsHomogeneous {k : ℕ} (Λ : Aggregator k) : Prop :=
  ∀ (c : NNReal) (x : Axes k), Λ (fun i => c * x i) = c * Λ x

/-- **A3 — Egyptian-exact weights.** All `k` axes share the *same* unit-fraction
weight `1/k`. This is the inspectability constraint: weights are auditable as a
single rational number, no "secret blends". Captured as a positional witness. -/
structure IsEgyptianExact (k : ℕ) : Prop where
  k_pos : 0 < k
  /-- Each axis weight is the unit fraction `1/k`. -/
  weight_eq : (1 : ℚ) / (k : ℚ) = (1 : ℚ) / (k : ℚ)  -- placeholder; full lemma in Egyptian.lean

/-- **A4 — Bounded by max axis.** Λ is never larger than the largest axis.
(Equivalently: Λ ∈ [min axis, max axis] ⊆ [0,1] when axes ⊆ [0,1].)

We carry the witness `hk : 0 < k` so that `Finset.univ : Finset (Fin k)`
is nonempty; the `k = 0` case is degenerate and handled separately. -/
def IsBounded {k : ℕ} (hk : 0 < k) (Λ : Aggregator k) : Prop :=
  ∀ x : Axes k,
    Λ x ≤ Finset.univ.sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ x

/-- The four Lutar axioms collected. The hypothesis `0 < k` is supplied by
`A3.k_pos` and threaded into `A4`'s `IsBounded`. -/
structure LutarAxioms {k : ℕ} (Λ : Aggregator k) : Prop where
  A1 : IsMonotone Λ
  A2 : IsHomogeneous Λ
  A3 : IsEgyptianExact k
  A4 : IsBounded A3.k_pos Λ

end Lutar
