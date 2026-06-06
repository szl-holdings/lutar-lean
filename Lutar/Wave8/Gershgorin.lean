/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave8/Gershgorin.lean — Q2: Gershgorin Governance Spectral Lower Bound

A direct application of Mathlib's Gershgorin circle theorem (`eigenvalue_mem_ball`)
to the a11oy governance weight matrix. If every diagonal entry has real part at
least `δ` and every off-diagonal row-sum of norms is at most `ε`, then EVERY
eigenvalue `μ` has real part at least `δ - ε`. When `ε < δ` this forces all
eigenvalues into the right half-plane: the governance matrix is non-degenerate
(no zero eigenvalue ⇒ invertible ⇒ stable aggregation). The "λ_min ≥ …" spectral
floor becomes a DERIVED theorem from the matrix structure, not a magic constant.

## What is proven
- `governance_spectral_lower_bound` — for `W : Matrix (Fin n) (Fin n) ℂ` (the
  complexified governance matrix), `δ ≤ (W i i).re` for all `i`, off-diagonal
  row-norm-sums `≤ ε`, then every eigenvalue `μ` of `toLin' W` has `δ - ε ≤ μ.re`.
- `governance_eigenvalues_pos_re` — corollary: if `ε < δ`, every eigenvalue has
  strictly positive real part (governance stability).

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave8`) — NOT in the LOCKED v11 baseline. Locked-proven
  stays exactly 5 {F1,F11,F12,F18,F19}. Λ untouched (Conjecture 1).
- Modeled over `ℂ` so the (possibly complex) eigenvalues live in the same field
  as the entries, letting us invoke Mathlib's `eigenvalue_mem_ball` directly; the
  governance matrix's real entries are the special case `μ.im = 0`.
- NO open obligation, no new declared axiom; Mathlib-backed.

## Citations
- Mathlib Gershgorin (`eigenvalue_mem_ball`):
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Gershgorin.html
- Wikipedia, Gershgorin circle theorem:
  https://en.wikipedia.org/wiki/Gershgorin_circle_theorem

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Data.Complex.Norm

open Matrix Complex

-- Gershgorin's `eigenvalue_mem_ball` instantiates `Matrix.toLin'` over a generic
-- `Fintype`/`DecidableEq` index, whose `whnf` reduction is costly; give the
-- elaborator extra budget. (Honest: a pure resource bump, no proof shortcut.)
set_option maxHeartbeats 1000000

namespace Lutar.Wave8.Gershgorin

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Q2 — Gershgorin governance spectral lower bound.** Every eigenvalue of the
governance matrix has real part at least `δ - ε`, derived from the diagonal floor
`δ` and the off-diagonal row-norm-sum ceiling `ε` via Gershgorin's theorem. -/
theorem governance_spectral_lower_bound (W : Matrix n n ℂ) (δ ε : ℝ)
    (hdiag : ∀ i, δ ≤ (W i i).re)
    (hoff : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖W i j‖ ≤ ε)
    (μ : ℂ) (hμ : Module.End.HasEigenvalue (Matrix.toLin' W) μ) :
    δ - ε ≤ μ.re := by
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hμ
  -- hk : μ ∈ closedBall (W k k) (∑ j ∈ univ.erase k, ‖W k j‖)
  rw [mem_closedBall_iff_norm] at hk
  -- hk : ‖μ - W k k‖ ≤ rowsum_k
  -- The real part of (W k k - μ) is bounded by the norm.
  have hnorm : ‖μ - W k k‖ ≤ ε := le_trans hk (hoff k)
  have hre : (W k k).re - μ.re ≤ ‖μ - W k k‖ := by
    have h1 : (W k k - μ).re ≤ ‖W k k - μ‖ := Complex.re_le_norm _
    have h3 : (W k k - μ).re = (W k k).re - μ.re := by rw [Complex.sub_re]
    rw [h3, norm_sub_rev] at h1
    exact h1
  -- Combine: μ.re ≥ (W k k).re - ε ≥ δ - ε.
  have : (W k k).re - μ.re ≤ ε := le_trans hre hnorm
  have hdk : δ ≤ (W k k).re := hdiag k
  linarith

/-- **Q2 corollary — governance stability.** If the diagonal floor strictly
dominates the off-diagonal row-norm ceiling (`ε < δ`), every eigenvalue has
strictly positive real part, so the governance matrix has no zero eigenvalue. -/
theorem governance_eigenvalues_pos_re (W : Matrix n n ℂ) (δ ε : ℝ)
    (hdiag : ∀ i, δ ≤ (W i i).re)
    (hoff : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖W i j‖ ≤ ε)
    (hδε : ε < δ)
    (μ : ℂ) (hμ : Module.End.HasEigenvalue (Matrix.toLin' W) μ) :
    0 < μ.re := by
  have := governance_spectral_lower_bound W δ ε hdiag hoff μ hμ
  linarith

#print axioms governance_spectral_lower_bound
#print axioms governance_eigenvalues_pos_re

end Lutar.Wave8.Gershgorin
