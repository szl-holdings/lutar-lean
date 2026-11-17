/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Theorem TH10 — Uniqueness of the Lutar Invariant (v2 — PhD-Math Retry)

**Status:** HONEST ASSESSMENT — this file distinguishes the remaining sorry
from the Cauchy lemma that is already closed in the imported Round13 proof.

**NOT a sorry-free proof.** Λ = Conjecture 1 per Supreme Rules.

## Current source boundary:
1. Slice multiplicativity is not derivable from A2 alone; it requires an additional
   hypothesis in the conditional proof route.
2. `monotone_additive_linear` reuses the completed Round13 rational-squeeze proof.
3. The former Cauchy sorry is closed; this does not supply the missing factorization.
4. The legacy unconditional signatures below remain unproved and are false under A1–A5.

## Remaining proof obligation:
- `monotone_additive_linear`: no remaining sorry; delegates to the closed Round13 lemma.
- `lutar_is_geomean`: 1 sorry for an unconditional statement false under A1–A5.
- `lutar_unique` depends on that unresolved declaration.
Total: one executable proof placeholder. Conjecture 1 is not a theorem.

## Historical doctrine and current measurement:
- Historical v11 snapshot: 749 declarations / 14 unique axioms / 163 sorries @ c7c0ba17.
- Closing the Cauchy sorry did not establish unconditional uniqueness.
- Current corpus numbers must come from the canonical counter at a named commit;
  this file's sorry tally is not a current corpus census. The locked eight are unchanged.

## References:
- Aczél, J. (1966). Lectures on Functional Equations. Academic Press. ISBN 0-12-043750-3. Thm 5.1.
- Cauchy, A.-L. (1821). Cours d'analyse. Chap. V §1.
- Hardy, G.H., Littlewood, J.E., Pólya, G. (1934). Inequalities. Cambridge UP. §2.18.
- Mathlib v4.13.0: `Fintype.prod_equiv`, `NNReal.rpow_*`, `Monotone.continuous`.
-/

import Lutar.Axioms
import Lutar.Egyptian
import Lutar.Invariant
import Lutar.Bound
import Lutar.Round13.CauchyND_Closure
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Preimage
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Order.IntermediateValue

namespace Lutar

open NNReal Real

/-! ## Lambda k satisfies all five Lutar axioms (A1–A5) -/

/-- A1 (monotone). -/
theorem lambda_isMonotone {k : Nat} (hk : 0 < k) :
    IsMonotone (Λ k) := by
  intro x y hxy
  simp only [Λ, hk.ne', dite_false]
  apply NNReal.rpow_le_rpow
  · exact Finset.prod_le_prod₀ (fun i _ => zero_le) (fun i _ => hxy i)
  · positivity

/-- A2 (1-homogeneous). -/
theorem lambda_isHomogeneous {k : Nat} (hk : 0 < k) :
    IsHomogeneous (Λ k) := by
  intro c x
  simp only [Λ, hk.ne', dite_false]
  have : (Finset.univ : Finset (Fin k)).prod (fun i => c * x i) =
         c ^ k * (Finset.univ : Finset (Fin k)).prod x := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin]
  rw [this, NNReal.mul_rpow]
  congr 1
  rw [← NNReal.rpow_natCast c k, ← NNReal.rpow_mul]
  simp [hk.ne']

/-- A3 (IsEgyptianExact). -/
theorem lambda_isEgyptianExact {k : Nat} (hk : 0 < k) :
    IsEgyptianExact k (Λ k) :=
  { k_pos       := hk,
    A3_normalize := a3_normalize_proof k hk }

/-- A4 (bounded). -/
theorem lambda_isBounded {k : Nat} (hk : 0 < k) :
    IsBounded hk (Λ k) :=
  fun x => Λ_le_max hk x

/-- **A5 — Λ satisfies permutation invariance. SORRY-FREE.**

    Proof: Finset product over `Fin k` is invariant under index reordering.
    Mathlib: `Fintype.prod_equiv` in `Mathlib.Algebra.BigOperators.Group.Finset`. -/
theorem Lambda_A5_perm_invariant {k : Nat} (hk : 0 < k)
    (x : Axes k) (σ : Fin k ≃ Fin k) :
    Λ k (x ∘ ↑σ) = Λ k x := by
  simp only [Λ_def hk]
  congr 1
  -- Goal: ∏ i, (x ∘ ↑σ) i = ∏ i, x i, i.e. ∏ i, x (σ i) = ∏ i, x i.
  -- `Equiv.prod_comp (e : ι ≃ κ) (g : κ → α) : ∏ i, g (e i) = ∏ i, g i`.
  -- This is sorry-free. Equiv.prod_comp is in Mathlib.Algebra.BigOperators.Group.Finset.
  exact Equiv.prod_comp σ x

theorem lambda_isPermutationInvariant {k : Nat} (hk : 0 < k) :
    IsPermutationInvariant (Λ k) :=
  fun x σ => Lambda_A5_perm_invariant hk x σ

theorem lambda_satisfiesAxioms {k : Nat} (hk : 0 < k) :
    LutarAxioms (Λ k) :=
  { A1 := lambda_isMonotone hk,
    A2 := lambda_isHomogeneous hk,
    A3 := lambda_isEgyptianExact hk,
    A4 := lambda_isBounded hk,
    A5 := lambda_isPermutationInvariant hk }

/-! ## Closed lemma: a monotone additive map on ℝ is linear
    (Aczél 1966 Thm 5.1; Cauchy 1821 Chap. V)

The implementation below reuses the completed Round13 rational-squeeze proof.
It does not derive multiplicativity or separability of an arbitrary A1–A5 aggregator.

Mathematical proof:
1. g additive + rational: g(q) = g(1) * q for all q : ℚ (induction on ℤ, then ℚ).
2. g additive + monotone → g continuous (Lean: `Monotone.continuous` on ℝ).
3. Two continuous functions g and (· * g(1)) agreeing on ℚ (dense in ℝ) are equal.
4. Hence g(t) = g(1) * t for all t : ℝ.

The argument above is background; the imported Round13 proof supplies the implementation. -/
private theorem monotone_additive_linear
    (g : ℝ → ℝ)
    (hg_add : ∀ u v : ℝ, g (u + v) = g u + g v)
    (hg_mono : Monotone g) :
    ∀ t : ℝ, g t = g 1 * t :=
  -- CLOSED (Wave12 CUT-2 cleanup): re-export the sorry-free Round 13 proof
  -- `Lutar.Round13.monotone_additive_linear` (Aczél 1966 Thm 5.1 / Cauchy 1821,
  -- via the rational squeeze; no continuity assumed). This retires the legacy
  -- S-MAIN-1 open obligation in this file with ZERO new axioms.
  Lutar.Round13.monotone_additive_linear g hg_add hg_mono

/-! ## Auxiliary: the single-axis slice

Given Φ satisfying A1–A5, the slice fᵢ(t) = Φ(fun j => if j=i then t else 1)
satisfies: (i) fᵢ(1) = 1 and (ii) fᵢ is monotone. The power-function form
fᵢ(t) = t^(1/k) does not follow from those facts or from A1–A5 alone.

The multiplicativity fᵢ(s*t) = fᵢ(s)*fᵢ(t) is NOT derivable from A2.
The conditional separable route supplies slice multiplicativity as an explicit
hypothesis before applying the log-space additive Cauchy argument. -/

private noncomputable def axisSlice {k : ℕ} (Φ : Aggregator k) (i : Fin k) :
    NNReal → NNReal :=
  fun t => Φ (fun j => if j = i then t else 1)

private lemma axisSlice_one {k : ℕ} (hk : 0 < k) (Φ : Aggregator k)
    (hA3 : IsEgyptianExact k Φ) (i : Fin k) :
    axisSlice Φ i 1 = 1 := by
  unfold axisSlice
  have : (fun j : Fin k => if j = i then (1 : NNReal) else 1) = fun _ => 1 := by
    ext j; simp
  rw [this]; exact hA3.A3_normalize 1

private lemma axisSlice_monotone {k : ℕ} (Φ : Aggregator k)
    (hA1 : IsMonotone Φ) (i : Fin k) :
    Monotone (axisSlice Φ i) := by
  intro s t hst
  unfold axisSlice
  apply hA1
  intro j
  by_cases hij : j = i
  · simp [hij, hst]
  · simp [hij]

/-! ## Legacy TH10 signatures — unconditional uniqueness remains unproved -/

/-- **Legacy TH10 claim.** The signature asserts that any A1–A5 aggregator equals `Λ k`.

    This declaration contains the remaining sorry. The Cauchy lemma no longer has
    its own sorry, but closing that analytic lemma cannot prove this false statement.

    The max-aggregator counterexample shows why A1–A5 alone are insufficient.
    The valid conditional results require factorization or the stated separable
    hypotheses; see `Round13.lambda_unique_of_factors` and
    `Round13.lambda_unique_of_separable`. No unconditional theorem is claimed. -/
theorem lutar_is_geomean {k : Nat} (hk : 0 < k)
    (Phi : Aggregator k) (hL : LutarAxioms Phi) :
    Phi = Lutar.Λ k := by
  obtain ⟨hA1, hA2, hA3, hA4, hA5⟩ := hL
  funext x
  -- The invalid legacy route, retained to make the missing premises explicit:
  -- For each i : Fin k, define fᵢ = axisSlice Phi i.
  -- fᵢ is monotone (axisSlice_monotone).
  -- fᵢ(1) = 1 (axisSlice_one).
  -- Define gᵢ(u) = Real.log (↑(fᵢ (Real.toNNReal (Real.exp u)))).
  -- The missing step: additivity of gᵢ does NOT follow from A2.
  -- gᵢ is monotone from fᵢ monotone.
  -- By monotone_additive_linear: gᵢ(t) = gᵢ(1) * t.
  -- Hence fᵢ(t) = t^(gᵢ(1)) = t^αᵢ.
  -- By A5 (hA5): for any i,j, αᵢ = αⱼ (permutation symmetry of slices).
  -- Hence all αᵢ = α.
  -- By A3 (hA3): Phi(c,...,c) = c ⟹ c^(k*α) = c ⟹ k*α = 1 ⟹ α = 1/k.
  -- Reconstruction additionally requires separability: it does not follow from A1–A5.
  -- ⚠️ HONEST OPEN OBLIGATION (UNAVOIDABLE — statement is FALSE under A1–A5).
  -- `lutar_is_geomean` is the UNCONDITIONAL claim `LutarAxioms Phi → Phi = Λ k`.
  -- This is machine-checked FALSE: `Lutar.Round13.maxAgg` and `min` satisfy A1–A5
  -- but are not Λ k (see `Round13.maxAgg_ne_Lambda`). There is therefore NO
  -- sorry-free proof to re-export — `Round13.lambda_unique` carries the same
  -- tagged `FACTORIZATION_AXIOM_GAP` obligation. Per HONESTY-OVER-CHECKLIST we do
  -- NOT fabricate a closed proof of a false statement; Λ stays Conjecture 1.
  -- The honestly-true conditional core now lives in
  -- `Lutar.Round13.lambda_unique_of_separable` (CUT-2, axiom-free) and
  -- `Lutar.Round13.lambda_unique_of_factors`.
  sorry

/-- **Theorem TH10 (Uniqueness of the Lutar Invariant).** -/
theorem lutar_unique {k : Nat} (hk : 0 < k)
    (Lambda_fn Lambda_fn' : Aggregator k)
    (hL  : LutarAxioms Lambda_fn)
    (hL' : LutarAxioms Lambda_fn') :
    Lambda_fn = Lambda_fn' :=
  (lutar_is_geomean hk Lambda_fn hL).trans
    (lutar_is_geomean hk Lambda_fn' hL').symm

end Lutar

/-
## Current status of the legacy proof route

| Declaration | Current status |
|---|---|
| `monotone_additive_linear` | Closed by the imported Round13 proof |
| `lutar_is_geomean` | One executable placeholder; unconditional statement false under A1–A5 |
| `lutar_unique` | Depends on the unresolved unconditional declaration |

The former two-placeholder estimate and claim of a correct unconditional proof
are historical errors. They must not be read as a remaining proof-engineering plan.
The conditional Round13 and Theorem-U results retain their explicit hypotheses.
Commentary reconciled 2026-11-16; declaration signatures and proof terms unchanged.
-/
