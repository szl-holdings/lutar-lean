/-
# Uniqueness Theorem (the headline)

**Theorem 1 (Lutar uniqueness).** Let `Λ, Λ' : (Fin k → ℝ≥0) → ℝ≥0` both
satisfy the four Lutar axioms (A1 monotone, A2 homogeneous, A3 Egyptian-exact,
A4 bounded). Then `Λ = Λ'`.

In other words: under A1..A4, the only valid invariant is the weighted
geometric mean with unit-fraction weights — i.e. `Λ_k` as defined in
`Invariant.lean`.

Status (2026-05-12 audit):
  · Statement: formal.
  · Proof: scaffolded with `sorry`. Discharge plan:
      - Step (a). A2 (homogeneity) ⇒ Λ is fully determined by its value on the
        unit cube `[0,1]^k`. Mathlib lemma: standard homogeneity-of-degree-1
        implies pointwise determination by the radial slice; no direct mathlib
        symbol, ~10 lines manual.
      - Step (b). A3 (Egyptian-exact) ⇒ weights are forced to `1/k`. Already
        captured by `Lutar.Egyptian.unitWeight_unique` (this lemma is
        unconditional and complete in `Lutar/Egyptian.lean`).
      - Step (c). A1 + A4 on the diagonal ⇒ Λ takes the geometric-mean form.
        Mathlib lemma: the characterisation of the geometric mean as the
        unique monotone-homogeneous map satisfying the upper-bound axiom
        follows from `Real.geom_mean_le_arith_mean_weighted` (one direction)
        plus an explicit equality construction on the unit cube.
      - Step (d). Combine (a)-(c) to identify Λ pointwise with `Λ_k`.

Discharging this theorem (and `lutar_is_geomean` below, which is an immediate
corollary) is the headline mathematical work-item for v13. The two `sorry`
sites are tracked at issue
`https://github.com/szl-holdings/lutar-lean/issues/1`.

CI runs `lake exe check` and reports the number of `sorry`s remaining. The
public commitment is: this number reaches 0 at v13. Until then, the runtime
suite under `packages/ouroboros-invariant/test/` (52 tests) verifies the
uniqueness property numerically across the reference vector set.
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
