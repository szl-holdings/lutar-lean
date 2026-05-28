/-
# The Lutar Invariant Λ_k

Definition:

    Λ_k(x₁,...,x_k) := (x₁ · x₂ · ... · x_k)^(1/k)

i.e. the *weighted geometric mean* with all weights equal to the Egyptian unit
fraction `1/k`. This is the concrete witness function whose uniqueness we
prove in `Uniqueness.lean`.
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
