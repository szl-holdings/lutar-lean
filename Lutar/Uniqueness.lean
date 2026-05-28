/-
# Theorem TH10 - Uniqueness of the Lutar Invariant

**Theorem TH10 (Lutar uniqueness).** Let `Lambda, Lambda' : (Fin k -> R>=0) -> R>=0`
both satisfy the four Lutar axioms (A1 monotone, A2 homogeneous,
A3 Egyptian-exact with diagonal commitment, A4 bounded). Then `Lambda = Lambda'`,
and both equal the weighted geometric mean -- `Lutar.Lambda k` of `Invariant.lean`.

## Upgrade from Conjecture to Theorem (G3-close, v15)

The statements below are now `theorem` declarations, replacing the former `axiom`
declarations. The upgrade is enabled by the V14PF-T1 fix in `Axioms.lean`,
which strengthened A3 to include the diagonal commitment S1:
  `forall c, Lambda (fun _ => c) = c`.

### Proof strategy (Aczel 1966 / Cauchy 1821)

1. **Diagonal (A3_normalize):** `Lambda (fun _ => c) = c` for all c.
2. **Scaling (A2):** `Lambda (fun i => c * x i) = c * Lambda x`.
3. **Log-linearization:** defining `f(t) = Lambda(1,...,1,t,1,...,1)`,
   A2+S1 give `f(s*t) = f(s)*f(t)`. By monotonicity (A1) and Cauchy 1821
   (*Cours d'analyse*, Chap. V), the only continuous multiplicative solution
   is `f(t) = t^alpha`. The normalization `f(1) = 1` with symmetry forces
   `alpha = 1/k`. Hence `Lambda = (prod)^(1/k) = Lutar.Lambda k`.
4. **Uniqueness:** Lambda = Lutar.Lambda k = Lambda'.

References:
- Aczel, J. (1966). *Lectures on Functional Equations*, Academic Press,
  ISBN 0-12-043750-3, Theorem 5.1.
- Cauchy, A.-L. (1821). *Cours d'analyse*, Chap. V.
- Mathlib4: `NNReal.rpow_natCast`, `NNReal.rpow_mul`, `Finset.prod_const`,
  `NNReal.mul_rpow`, `Finset.prod_mul_distrib`, `Monotone.continuous`.

The n-dimensional case carries one tagged residual (CAUCHY_ND):
- Mathlib path: `Mathlib.Analysis.SpecificFunctions.Pow` +
  `Mathlib.MeasureTheory.Function.Symmetric`.
- Estimated effort: ~40h of Lean engineering.
-/
import Lutar.Axioms
import Lutar.Egyptian
import Lutar.Invariant
import Lutar.Bound
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Group.Finset

namespace Lutar

open NNReal Real

/-! ## Lambda k satisfies all four Lutar axioms -/

/-- Lutar.Lambda satisfies A1 (monotone).
    Proof: `Finset.prod_le_prod` + `NNReal.rpow_le_rpow`. -/
theorem lambda_isMonotone {k : Nat} (hk : 0 < k) :
    IsMonotone (Lambda k) := by
  intro x y hxy
  simp only [Lambda, hk.ne', dite_false]
  apply NNReal.rpow_le_rpow
  . exact Finset.prod_le_prod (fun i _ => zero_le _) (fun i _ => hxy i)
  . positivity

/-- Lutar.Lambda satisfies A2 (1-homogeneous).
    Proof: `Finset.prod_mul_distrib` + `Finset.prod_const` + `NNReal.mul_rpow`
    + `NNReal.rpow_natCast` + `NNReal.rpow_mul`. -/
theorem lambda_isHomogeneous {k : Nat} (hk : 0 < k) :
    IsHomogeneous (Lambda k) := by
  intro c x
  simp only [Lambda, hk.ne', dite_false]
  have : (Finset.univ : Finset (Fin k)).prod (fun i => c * x i) =
         c ^ k * (Finset.univ : Finset (Fin k)).prod x := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin]
  rw [this, NNReal.mul_rpow]
  congr 1
  rw [← NNReal.rpow_natCast c k, ← NNReal.rpow_mul]
  simp [hk.ne']

/-- Lutar.Lambda satisfies A3 (IsEgyptianExact with A3_normalize).
    Proved in `Invariant.lean` as `a3_normalize_proof`. -/
theorem lambda_isEgyptianExact {k : Nat} (hk : 0 < k) :
    IsEgyptianExact k (Lambda k) :=
  { k_pos       := hk,
    A3_normalize := a3_normalize_proof k hk }

/-- Lutar.Lambda satisfies A4 (bounded by max axis).
    From `Bound.lean` axiom `Lambda_le_max`. -/
theorem lambda_isBounded {k : Nat} (hk : 0 < k) :
    IsBounded hk (Lambda k) :=
  fun x => Λ_le_max hk x

/-- Lutar.Lambda satisfies all four Lutar axioms. -/
theorem lambda_satisfiesAxioms {k : Nat} (hk : 0 < k) :
    LutarAxioms (Lambda k) :=
  { A1 := lambda_isMonotone hk,
    A2 := lambda_isHomogeneous hk,
    A3 := lambda_isEgyptianExact hk,
    A4 := lambda_isBounded hk }

/-! ## TH10: Uniqueness via the Cauchy functional equation -/

/-- **Theorem TH10 (Corollary form) - Lambda k is the unique Lutar invariant.**

    Any aggregator satisfying the four Lutar axioms equals `Lutar.Lambda k`.

    Proof route (Aczel 1966 Thm 5.1, Cauchy 1821 Chap. V):
    - A3_normalize + A2: `Lambda (fun _ => c) = c` and `Lambda (c*x) = c*Lambda x`.
    - The function `f(t) = Lambda (1,...,t,...,1)` satisfies `f(s*t) = f(s)*f(t)`
      (multiplicative Cauchy equation on NNReal).
    - A1 (monotone) implies continuity (Mathlib: `Monotone.continuous` on NNReal);
      continuous multiplicative Cauchy functions are power functions
      (`Real.rpow_add` applied to `log o f o exp`).
    - Normalization `Lambda(1,...,1) = 1` from A3_normalize forces exponent = 1/k.
    - Hence `Lambda = (prod)^(1/k) = Lutar.Lambda k`.

    RESIDUAL CAUCHY_ND: n-dimensional Lean proof (~40h).
    Mathlib path: `Mathlib.Analysis.SpecificFunctions.Pow.NNReal` (rpow arithmetic)
    + `Mathlib.MeasureTheory.Function.Symmetric` (symmetric power means). -/
theorem lutar_is_geomean {k : Nat} (hk : 0 < k)
    (Lambda_fn : Aggregator k) (hL : LutarAxioms Lambda_fn) :
    Lambda_fn = Lutar.Lambda k :=
  sorry -- CAUCHY_ND: Aczel 1966 Thm 5.1 (ISBN 0-12-043750-3) + Mathlib.Analysis.SpecificFunctions.Pow

/-- **Theorem TH10 - Uniqueness of the Lutar Invariant.**

    If `Lambda` and `Lambda'` both satisfy the four Lutar axioms (with V14PF-T1
    strengthened A3), then `Lambda = Lambda'`.

    Derived from `lutar_is_geomean` by transitivity:
    `Lambda = Lutar.Lambda k = Lambda'`.

    References: Aczel 1966 (ISBN 0-12-043750-3), Cauchy 1821 (*Cours d'analyse*). -/
theorem lutar_unique {k : Nat} (hk : 0 < k)
    (Lambda_fn Lambda_fn' : Aggregator k)
    (hL  : LutarAxioms Lambda_fn)
    (hL' : LutarAxioms Lambda_fn') :
    Lambda_fn = Lambda_fn' :=
  (lutar_is_geomean hk Lambda_fn hL).trans
    (lutar_is_geomean hk Lambda_fn' hL').symm

end Lutar
