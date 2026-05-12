/-
# Uniqueness Theorem (the headline)

**Theorem 1 (Lutar uniqueness).** Let `Λ, Λ' : (Fin k → ℝ≥0) → ℝ≥0` both
satisfy the four Lutar axioms (A1 monotone, A2 homogeneous, A3 Egyptian-exact,
A4 bounded). Then `Λ = Λ'`.

In other words: under A1..A4, the only valid invariant is the weighted
geometric mean with unit-fraction weights — i.e. `Λ_k` as defined in
`Invariant.lean`.

Status:
  · Statement: formal.
  · Proof: scaffolded with `sorry`. Discharged across:
      - A2 (homogeneity) ⇒ Λ is determined by its value on the unit cube.
      - A3 (Egyptian-exact) ⇒ weights are forced to 1/k by `Egyptian.unitWeight_unique`.
      - A1+A4 ⇒ Λ takes the geometric-mean form on the diagonal.
      - These three combine to identify Λ pointwise with `Λ_k`.

CI runs `lake exe check` and reports the number of `sorry`s remaining. The
public commitment is: this number reaches 0.
-/
import Lutar.Axioms
import Lutar.Egyptian
import Lutar.Invariant
import Lutar.Bound

namespace Lutar

/-- **Theorem 1.** Uniqueness of the Lutar Invariant under the four axioms. -/
theorem lutar_unique {k : ℕ} (hk : 0 < k)
    (Λ Λ' : Aggregator k)
    (hΛ  : LutarAxioms Λ)
    (hΛ' : LutarAxioms Λ') :
    Λ = Λ' := by
  sorry

/-- Corollary: the unique invariant *is* the weighted geometric mean `Λ_k`. -/
theorem lutar_is_geomean {k : ℕ} (hk : 0 < k)
    (Λ : Aggregator k) (hΛ : LutarAxioms Λ) :
    Λ = Lutar.Λ k := by
  sorry

end Lutar
