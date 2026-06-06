/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave8/DensityMixture.lean — Q1: Density-Matrix Mixture PSD (honest QM gate)

A convex mixture of density matrices is again a density matrix: positive
semidefinite (PSD) and unit trace. We state the governance version over REAL
symmetric matrices (`Matrix n n ℝ`) — the a11oy "quantum gate" is metaphor for
the spectral analysis of a REAL governance matrix, so the honest model is real
linear algebra, NOT quantum hardware. Mixing evidence preserves a valid
probability-distribution representation: the gate cannot emit nonsense.

## What is proven
- `posSemidef_smul`         — `0 ≤ c → A.PosSemidef → (c • A).PosSemidef`.
- `posSemidef_sum`          — a finite sum of PSD matrices is PSD.
- `density_mixture_psd`     — `∑ i, ws i • ρs i` is PSD when each `ρs i` is PSD,
                              `ws i ≥ 0`.
- `density_mixture_trace`   — `trace (∑ i, ws i • ρs i) = 1` when each
                              `trace (ρs i) = 1` and `∑ ws = 1`.
- `density_matrix_mixture`  — packaged: the mixture is PSD AND unit-trace.

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave8`) — NOT in the LOCKED v11 baseline. Locked-proven
  stays exactly 5 {F1,F11,F12,F18,F19}. Λ untouched (Conjecture 1).
- "Quantum gate" is a NARRATIVE label for real matrix algebra; no quantum claim.
- Real symmetric model (the complex/`RCLike` version follows by the same
  `PosSemidef.add` + linearity argument; left as a follow-up). NO open obligation, no
  new declared axiom; Mathlib-backed.

## Citations
- Mathlib `Matrix.PosSemidef` (`.add`, `.zero`):
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/PosDef.html
- Watrous, density-matrix lecture notes:
  https://cs.uwaterloo.ca/~watrous/QC-notes/QC-notes.14.pdf

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

open Matrix BigOperators

namespace Lutar.Wave8.DensityMixture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A nonnegative real scalar multiple of a PSD real matrix is PSD. -/
theorem posSemidef_smul {A : Matrix n n ℝ} (hA : A.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    (c • A).PosSemidef := by
  refine ⟨?_, ?_⟩
  · -- Hermitian (= symmetric over ℝ) is preserved by scalar multiplication.
    have hH : Aᴴ = A := hA.1
    show (c • A)ᴴ = c • A
    rw [conjTranspose_smul, hH, star_trivial]
  · intro x
    -- (c • A) *ᵥ x = c • (A *ᵥ x); dotProduct pulls the scalar out.
    rw [smul_mulVec_assoc, dotProduct_smul]
    exact smul_nonneg hc (hA.2 x)

/-- A finite sum of PSD real matrices is PSD. -/
theorem posSemidef_sum {ι : Type*} (s : Finset ι) (M : ι → Matrix n n ℝ)
    (h : ∀ i ∈ s, (M i).PosSemidef) :
    (∑ i ∈ s, M i).PosSemidef := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (Matrix.PosSemidef.zero : (0 : Matrix n n ℝ).PosSemidef)
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- **Q1 (PSD part).** A convex/conic mixture of PSD matrices is PSD. -/
theorem density_mixture_psd {ι : Type*} (s : Finset ι)
    (ρ : ι → Matrix n n ℝ) (w : ι → ℝ)
    (hρ : ∀ i ∈ s, (ρ i).PosSemidef) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i • ρ i).PosSemidef :=
  posSemidef_sum s (fun i => w i • ρ i)
    (fun i hi => posSemidef_smul (hρ i hi) (hw i hi))

/-- **Q1 (trace part).** A mixture with weights summing to 1 of unit-trace
matrices has unit trace, by linearity of trace. -/
theorem density_mixture_trace {ι : Type*} (s : Finset ι)
    (ρ : ι → Matrix n n ℝ) (w : ι → ℝ)
    (htr : ∀ i ∈ s, Matrix.trace (ρ i) = 1) (hsum : ∑ i ∈ s, w i = 1) :
    Matrix.trace (∑ i ∈ s, w i • ρ i) = 1 := by
  rw [trace_sum]
  have : ∀ i ∈ s, Matrix.trace (w i • ρ i) = w i := by
    intro i hi
    rw [trace_smul, htr i hi, smul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl this, hsum]

/-- **Q1 (packaged).** The mixture of density matrices is a density matrix:
positive semidefinite AND unit trace. -/
theorem density_matrix_mixture {ι : Type*} (s : Finset ι)
    (ρ : ι → Matrix n n ℝ) (w : ι → ℝ)
    (hρ : ∀ i ∈ s, (ρ i).PosSemidef) (htr : ∀ i ∈ s, Matrix.trace (ρ i) = 1)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1) :
    (∑ i ∈ s, w i • ρ i).PosSemidef ∧ Matrix.trace (∑ i ∈ s, w i • ρ i) = 1 :=
  ⟨density_mixture_psd s ρ w hρ hw, density_mixture_trace s ρ w htr hsum⟩

#print axioms posSemidef_smul
#print axioms posSemidef_sum
#print axioms density_mixture_psd
#print axioms density_mixture_trace
#print axioms density_matrix_mixture

end Lutar.Wave8.DensityMixture
