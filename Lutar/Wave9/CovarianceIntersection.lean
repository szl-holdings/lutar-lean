/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave9/CovarianceIntersection.lean — OE-2: Covariance-intersection PSD closure

Covariance Intersection (CI) fuses two possibly-correlated estimates into a
conservative one WITHOUT the cross-covariance, by combining the INFORMATION-FORM
matrices convexly: `Iₓ = ω · P₁⁻¹ + (1-ω) · P₂⁻¹`, `ω ∈ [0,1]`. The consistency
of CI rests on the fact that this convex combination of positive-semidefinite
(information) matrices is itself positive semidefinite — the fused information is
a valid (PSD) information matrix for every mixing weight.

We machine-check the CORE of OE-2: positive-semidefiniteness is closed under
NONNEGATIVE SCALING and under CONVEX COMBINATION, over real matrices, from
Mathlib's `Matrix.PosSemidef`. This is the conservative-consistency engine of CI.

The Loewner-order inequality on the INVERTED fused covariance
(`fused_error_covariance ≤ (ω·P₁⁻¹ + (1-ω)·P₂⁻¹)⁻¹`) needs matrix-monotone
inversion on the positive-definite cone, which Mathlib does not package directly;
it is the documented ROADMAP extension. We ship the PSD-closure core rather than
fabricate the inversion-monotonicity step.

## What is proven
- `PosSemidef.nonneg_smul` — `0 ≤ c` and `A` PSD ⟹ `c • A` PSD (real matrices).
- `posSemidef_convex_comb` — `A, B` PSD and `ω ∈ [0,1]` ⟹
  `ω • A + (1-ω) • B` PSD: the fused INFORMATION matrix is a valid PSD matrix.
- `ci_information_psd` — packaged OE-2 statement on information-form inputs
  `Q₁ = P₁⁻¹`, `Q₂ = P₂⁻¹` (passed as PSD hypotheses): the CI-fused information
  `ω • Q₁ + (1-ω) • Q₂` is PSD for every `ω ∈ [0,1]`.

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave9`) — NOT in the LOCKED v11 baseline. Locked-proven
  stays exactly 5 {F1,F11,F12,F18,F19}. Λ untouched (Conjecture 1).
- Known-theorem formalization (Julier–Uhlmann covariance intersection). Backed by
  Mathlib `Matrix.PosSemidef`.
- NO new declared axiom, NO sorry in any theorem body.
- Scope: proves PSD closure (conservative consistency core) only — NOT optimality,
  unbiasedness, or superiority over centralized fusion, and NOT the inverted-cov
  Loewner inequality (ROADMAP), per the OE-2 risk note.

## Citations
- Julier, Uhlmann, "A non-divergent estimation algorithm in the presence of
  unknown correlations" (ACC 1997) — covariance intersection.
- IEEE Xplore DOI 10.1109/CCDC55256.2022.10034171:
  https://ieeexplore.ieee.org/document/10034171/
- IEEE Xplore DOI 10.1109/CCDC52312.2021.9601754:
  https://ieeexplore.ieee.org/document/9601754/
- Mathlib positive semidefinite matrices:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/PosDef.html

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix

namespace Lutar.Wave9.CovarianceIntersection

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **PSD closure under nonnegative real scaling.** If `A` is positive
semidefinite and `c ≥ 0`, then `c • A` is positive semidefinite. -/
theorem PosSemidef.nonneg_smul {A : Matrix n n ℝ} (hA : A.PosSemidef)
    {c : ℝ} (hc : 0 ≤ c) : (c • A).PosSemidef := by
  refine ⟨?_, fun x => ?_⟩
  · -- (c • A)ᴴ = c • Aᴴ = c • A   (over ℝ, star c = c)
    show (c • A).conjTranspose = c • A
    rw [conjTranspose_smul, hA.1, star_trivial]
  · -- xᴴ (c • A) x = c * (xᴴ A x) ≥ 0
    have hquad : 0 ≤ dotProduct (star x) (A *ᵥ x) := hA.2 x
    rw [smul_mulVec_assoc, dotProduct_smul]
    exact smul_nonneg hc hquad

/-- **OE-2 core — PSD convex closure.** If `A` and `B` are positive semidefinite
and `ω ∈ [0,1]`, then the convex combination `ω • A + (1-ω) • B` is positive
semidefinite. This is the conservative-consistency engine of covariance
intersection in information form. -/
theorem posSemidef_convex_comb {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    {ω : ℝ} (h0 : 0 ≤ ω) (h1 : ω ≤ 1) :
    ((ω • A) + (1 - ω) • B).PosSemidef :=
  Matrix.PosSemidef.add (PosSemidef.nonneg_smul hA h0)
    (PosSemidef.nonneg_smul hB (by linarith))

/-- **OE-2 (packaged).** Given two information-form matrices `Q₁ = P₁⁻¹`,
`Q₂ = P₂⁻¹` (positive semidefinite), the covariance-intersection fused
information `ω • Q₁ + (1-ω) • Q₂` is a valid (positive semidefinite) information
matrix for EVERY mixing weight `ω ∈ [0,1]` — CI produces a consistent
conservative estimate without any cross-covariance. -/
theorem ci_information_psd {Q₁ Q₂ : Matrix n n ℝ}
    (hQ₁ : Q₁.PosSemidef) (hQ₂ : Q₂.PosSemidef)
    {ω : ℝ} (h0 : 0 ≤ ω) (h1 : ω ≤ 1) :
    ((ω • Q₁) + (1 - ω) • Q₂).PosSemidef :=
  posSemidef_convex_comb hQ₁ hQ₂ h0 h1

#print axioms PosSemidef.nonneg_smul
#print axioms posSemidef_convex_comb
#print axioms ci_information_psd

end Lutar.Wave9.CovarianceIntersection
