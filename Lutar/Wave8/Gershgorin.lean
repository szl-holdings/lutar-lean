/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave8/Gershgorin.lean — Q2: Gershgorin Governance Non-Degeneracy

A direct application of Mathlib's Gershgorin-derived diagonal-dominance theorem
(`det_ne_zero_of_sum_row_lt_diag`) to the a11oy governance weight matrix.
If every diagonal entry strictly dominates the sum of the norms of the
off-diagonal entries in its row, then the governance matrix is NON-SINGULAR
(`det ≠ 0`), hence invertible: the weighted-aggregation operator has a unique
solution and no zero eigenvalue. The "non-degenerate governance" guarantee
becomes a DERIVED theorem from the matrix structure, not a magic constant.

This is the honest, robust face of the Gershgorin circle theorem: rather than
destructuring an arbitrary complex eigenvalue (which forces an expensive
`Matrix.toLin'` `whnf` reduction in the elaborator), we use the strict
row-dominance ⇒ `det ≠ 0` corollary that Mathlib derives FROM `eigenvalue_mem_ball`.

## What is proven
- `governance_nonsingular_real` — for `W : Matrix n n ℝ` (the honest
  real-governance model), if for every row `i`
  `∑_{j ≠ i} ‖W i j‖ < ‖W i i‖` (strict diagonal dominance), then `W.det ≠ 0`.
- `governance_unit_solvable` — corollary: a strictly diagonally-dominant
  real governance matrix is invertible (`IsUnit W.det`), so weighted aggregation
  `W x = b` has a unique solution.

## Scope note (Q2 honesty)
Framing non-degenerate governance as a REAL-weight model fully satisfies Q2's
intent: non-degenerate governance ⇒ unique weighted aggregation. A complex (ℂ)
variant was attempted but is left as ROADMAP: Mathlib's normed-field instance
synthesis for `‖·‖` over `ℂ` in `det_ne_zero_of_sum_row_lt_diag` did not
elaborate cleanly here, so to keep the kernel obligation fully discharged we
ship only the real-valued theorems (no open obligation, no fabricated axioms).

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave8`) — NOT in the LOCKED v11 baseline. Locked-proven
  stays exactly 5 {F1,F11,F12,F18,F19}. Λ untouched (Conjecture 1).
- NO open obligation, no new declared axiom; Mathlib-backed (Gershgorin).

## Citations
- Mathlib Gershgorin (`det_ne_zero_of_sum_row_lt_diag`, `eigenvalue_mem_ball`,
  top-level decls in `Mathlib.LinearAlgebra.Matrix.Gershgorin`):
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Gershgorin.html
- Wikipedia, Gershgorin circle theorem:
  https://en.wikipedia.org/wiki/Gershgorin_circle_theorem

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/
import Mathlib.LinearAlgebra.Matrix.Gershgorin

open Matrix

namespace Lutar.Wave8.Gershgorin

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Q2 — Gershgorin governance non-degeneracy (ℝ).** The honest real-governance
model: a strictly diagonally-dominant real governance matrix is non-singular. -/
theorem governance_nonsingular_real (W : Matrix n n ℝ)
    (hdom : ∀ k, ∑ j ∈ Finset.univ.erase k, ‖W k j‖ < ‖W k k‖) :
    W.det ≠ 0 :=
  det_ne_zero_of_sum_row_lt_diag hdom

/-- **Q2 corollary — governance solvability.** A strictly diagonally-dominant
real governance matrix has a unit determinant (`IsUnit W.det`), hence is
invertible: weighted aggregation has a unique solution. -/
theorem governance_unit_solvable (W : Matrix n n ℝ)
    (hdom : ∀ k, ∑ j ∈ Finset.univ.erase k, ‖W k j‖ < ‖W k k‖) :
    IsUnit W.det :=
  isUnit_iff_ne_zero.mpr (governance_nonsingular_real W hdom)

#print axioms governance_nonsingular_real
#print axioms governance_unit_solvable

end Lutar.Wave8.Gershgorin
