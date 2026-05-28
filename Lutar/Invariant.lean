/-
# The Lutar Invariant Λ_k

Definition:

    Λ_k(x₁,...,x_k) := (x₁ · x₂ · ... · x_k)^(1/k)

i.e. the *weighted geometric mean* with all weights equal to the Egyptian unit
fraction `1/k`. This is the concrete witness function whose uniqueness we
prove in `Uniqueness.lean`.

## Canonical status (fix/lambda-unification)

This file is the formal anchor of the Lutar Invariant Λ as a *scalar*
in [0,1]. The runtime now matches:

  - `ouroboros/runtime/lambda-gate/src/gate.ts` (computeLambda → geomean)
  - `platform/packages/ouroboros-guardrails/src/lambda.ts` (lambdaScore → geomean)
  - `platform/packages/ouroboros-invariant/src/lutar-invariant-9.ts` (lutarInvariant9 → geomean)

The Boolean gate verdict (per-axis conjunctive AND with thresholds θᵢ) is a
*separate* artefact — it is not Λ. The single source of truth for the
runtime contract is `ouroboros/docs/lambda-spec.md`. The thesis presents
the two as Definition 2a (Λ scalar) and Definition 2b (gate verdict) in
v14 §3.3 (post fix/lambda-unification).

`Uniqueness.lean` proves (postulates pending stronger A3, see file header)
that the geomean defined here is the unique aggregator satisfying
A1–A4 — in particular the MIN-fold fails A3 (Egyptian-exactness).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Group.Finset
import Lutar.Axioms

namespace Lutar

open NNReal

/-- The Lutar Invariant: geometric mean with unit-fraction weights. -/
noncomputable def Λ (k : ℕ) (x : Axes k) : NNReal :=
  if hk : k = 0 then 0
  else
    let prod : NNReal := (Finset.univ : Finset (Fin k)).prod x
    prod ^ ((1 : ℝ) / (k : ℝ))

/-- For `k ≥ 1`, Λ is well-defined as the k-th root of the axis product. -/
theorem Λ_def {k : ℕ} (hk : 0 < k) (x : Axes k) :
    Λ k x = ((Finset.univ : Finset (Fin k)).prod x) ^ ((1 : ℝ) / (k : ℝ)) := by
  simp [Λ, hk.ne']

end Lutar
