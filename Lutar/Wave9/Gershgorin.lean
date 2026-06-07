/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave9/Gershgorin.lean — MA1: Gershgorin Zero-Eigenvalue Exclusion (spectral form)

The classical Gershgorin / Lévy–Desplanques corollary, stated in the
EIGENVALUE language (the "no zero eigenvalue" / spectral form), over a general
normed field `K` (in particular `ℂ`). If every row of `A` is STRICTLY DIAGONALLY
DOMINANT — `∑_{j ≠ k} ‖A k j‖ < ‖A k k‖` — then `0` is NOT an eigenvalue of `A`
(equivalently, `A`'s associated endomorphism `Matrix.toLin' A` has no zero
eigenvalue), and the determinant is a unit, so `A` is invertible.

This is deliberately DISTINCT from `Lutar/Wave8/Gershgorin.lean` (which states
the real-valued `det ≠ 0` corollary, `governance_*`). Here we expose the
SPECTRAL formulation `¬ HasEigenvalue (toLin' A) 0` derived directly from
Mathlib's `eigenvalue_mem_ball`, over a general field including `ℂ`, which is the
precise "0 ∉ spectrum" certificate named in the MA1 shortlist sketch.

## What is proven
- `no_zero_eigenvalue` — `(K = ℂ` or any `NormedField)`: strict row diagonal
  dominance ⟹ `¬ Module.End.HasEigenvalue (Matrix.toLin' A) 0` (zero is not an
  eigenvalue: the governance/command matrix has trivial kernel).
- `nonsingular_of_strict_diag_dominant` — strict row dominance ⟹ `A.det ≠ 0`
  over any normed field (the field-general companion to Wave8's ℝ version).
- `isUnit_det_of_strict_diag_dominant` — corollary: `IsUnit A.det`.

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave9`) — NOT in the LOCKED v11 baseline. Locked-proven
  stays exactly 5 {F1,F11,F12,F18,F19}. Λ untouched (Conjecture 1).
- Known-theorem formalization (Gershgorin circle theorem / Lévy–Desplanques).
  Backed by Mathlib (`eigenvalue_mem_ball`, `det_ne_zero_of_sum_row_lt_diag`).
- NO open obligation, NO new declared axiom, NO sorry.
- Scope note: certifies the classical spectral non-degeneracy criterion only.
  Any mapping from governance/trust weights to a concrete matrix must be
  separately justified (per the MA1 risk note).

## Citations
- Mathlib Gershgorin (`eigenvalue_mem_ball`, `det_ne_zero_of_sum_row_lt_diag`):
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Gershgorin.html
- Wikipedia, Gershgorin circle theorem:
  https://en.wikipedia.org/wiki/Gershgorin_circle_theorem
- Mathlib spectral theory of hermitian matrices:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Spectrum.html

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/
import Mathlib.LinearAlgebra.Matrix.Gershgorin

open Matrix

namespace Lutar.Wave9.Gershgorin

variable {K n : Type*} [NormedField K] [Fintype n] [DecidableEq n] {A : Matrix n n K}

/-- **MA1 (spectral form).** If every row of `A` is strictly diagonally dominant
(`∑_{j ≠ k} ‖A k j‖ < ‖A k k‖`), then `0` is NOT an eigenvalue of the associated
endomorphism `Matrix.toLin' A`. Over `K = ℂ` this is exactly `0 ∉ spectrum`:
the command/governance matrix has trivial kernel.

Proof: a zero eigenvalue would, by `eigenvalue_mem_ball`, force
`0 ∈ closedBall (A k k) (∑_{j≠k} ‖A k j‖)` for some `k`, i.e.
`‖A k k‖ ≤ ∑_{j≠k} ‖A k j‖`, contradicting strict dominance at that row. -/
theorem no_zero_eigenvalue
    (h : ∀ k, ∑ j ∈ Finset.univ.erase k, ‖A k j‖ < ‖A k k‖) :
    ¬ Module.End.HasEigenvalue (Matrix.toLin' A) 0 := by
  intro hμ
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hμ
  -- `hk : 0 ∈ closedBall (A k k) r` unfolds to `‖A k k‖ ≤ r`.
  rw [mem_closedBall_iff_norm', sub_zero] at hk
  exact absurd hk (not_le.mpr (h k))

/-- **MA1 (determinant form, field-general).** Strict row diagonal dominance over
any normed field `K` (in particular `ℂ`) ⟹ `A.det ≠ 0`. This is the
field-general companion to the real-valued Wave8 `governance_nonsingular_real`. -/
theorem nonsingular_of_strict_diag_dominant
    (h : ∀ k, ∑ j ∈ Finset.univ.erase k, ‖A k j‖ < ‖A k k‖) :
    A.det ≠ 0 :=
  det_ne_zero_of_sum_row_lt_diag h

/-- **MA1 corollary.** A strictly diagonally-dominant matrix has a unit
determinant, hence is invertible. -/
theorem isUnit_det_of_strict_diag_dominant
    (h : ∀ k, ∑ j ∈ Finset.univ.erase k, ‖A k j‖ < ‖A k k‖) :
    IsUnit A.det :=
  isUnit_iff_ne_zero.mpr (nonsingular_of_strict_diag_dominant h)

#print axioms no_zero_eigenvalue
#print axioms nonsingular_of_strict_diag_dominant
#print axioms isUnit_det_of_strict_diag_dominant

end Lutar.Wave9.Gershgorin
