/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 17 — CF-27: monDEQ well-posedness (uniqueness) from strong monotonicity, axiom-free

## Provenance / license doctrine (binding)

This is **PATTERN-ONLY** w.r.t. `locuslab/monotone_op_net` (the monDEQ reference implementation,
arXiv:2006.08591), whose repository license is **NOASSERTION**.  NO code is copied. We cite the
paper and write fresh Lean from first principles.  Winston & Kolter, *Monotone Operator Equilibrium
Networks*, NeurIPS 2020 (arXiv:2006.08591).

## What monDEQ well-posedness is, mathematically

A monotone-operator equilibrium network computes a fixed point `z⋆` of an equilibrium map; the
well-posedness guarantee of the paper is that when the associated residual operator is **strongly
monotone** (positive-definite symmetric part, parameter `m > 0`), the equilibrium point is
**unique**.  We model the finite-dimensional state space as `Fin n → ℝ` with the Euclidean dot
product `dotp` and squared norm `sq2`, and prove the well-posedness core:

* `dotp` / `sq2`                  — Euclidean pairing and squared norm on `Fin n → ℝ`.
* `sq2_nonneg`, `sq2_eq_zero`     — `sq2 u ≥ 0`, and `sq2 u = 0 ↔ u = 0`.
* `StronglyMonotone`              — `m·‖x−y‖² ≤ ⟨F x − F y, x − y⟩` for all `x,y`.
* `StronglyMonotone.injective`    — a strongly-monotone operator (with `m > 0`) is **injective**
                                    (Cauchy–Schwarz-free: uses `sq2 ≥ 0` directly).
* `StronglyMonotone.subsingleton_solutions` — the equation `F z = c` has **at most one** solution.
* `monDEQ_unique_equilibrium`     — the monDEQ residual `F z = z − G z` being strongly monotone
                                    ⇒ the equilibrium equation `z = G z` has at most one solution
                                    (the well-posedness theorem).

## Honesty / scope
- EXPERIMENTAL companion (`Lutar/Wave17/`). NO new axiom; NO sorry. Locked-proven set unchanged.
- This proves the UNIQUENESS half of well-posedness (the part guaranteed purely by strong
  monotonicity, no contraction constant needed).  EXISTENCE (a fixed point exists) requires a
  Banach/operator-splitting fixed-point argument over a complete inner-product space; that uses
  Mathlib `InnerProductSpace` machinery not assembled here and is documented as CF-27-FULL roadmap.
- Pattern-only: NO monotone_op_net code copied; fresh derivation, paper cited.

## References
- Winston, E. & Kolter, J.Z. (2020). *Monotone Operator Equilibrium Networks*. NeurIPS 2020.
  arXiv:2006.08591.  Repo `locuslab/monotone_op_net` (NOASSERTION) — pattern-only, no code used.

Signed-off-by: SZL CTO <cto@szl-holdings.com>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Lutar.Wave17

open Finset

/-- Euclidean dot product on the finite-dimensional state space `Fin n → ℝ`. -/
def dotp {n : ℕ} (u v : Fin n → ℝ) : ℝ := ∑ i, u i * v i

/-- Euclidean squared norm `‖u‖²`. -/
def sq2 {n : ℕ} (u : Fin n → ℝ) : ℝ := ∑ i, (u i) ^ 2

@[simp] theorem dotp_self {n : ℕ} (u : Fin n → ℝ) : dotp u u = sq2 u := by
  unfold dotp sq2; apply Finset.sum_congr rfl; intro i _; ring

theorem dotp_comm {n : ℕ} (u v : Fin n → ℝ) : dotp u v = dotp v u := by
  unfold dotp; apply Finset.sum_congr rfl; intro i _; ring

/-- The squared norm is nonnegative. -/
theorem sq2_nonneg {n : ℕ} (u : Fin n → ℝ) : 0 ≤ sq2 u := by
  unfold sq2; positivity

/-- The squared norm vanishes iff the vector is zero (positive-definiteness). -/
theorem sq2_eq_zero {n : ℕ} (u : Fin n → ℝ) : sq2 u = 0 ↔ u = 0 := by
  unfold sq2
  constructor
  · intro h
    funext i
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ (u j) ^ 2 := fun j _ => sq_nonneg _
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h i (Finset.mem_univ i)
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  · intro h; subst h; simp

/-- `F : (Fin n → ℝ) → (Fin n → ℝ)` is **strongly monotone** with modulus `m` if
    `m·‖x−y‖² ≤ ⟨F x − F y, x − y⟩` for all `x, y`. -/
def StronglyMonotone {n : ℕ} (m : ℝ) (F : (Fin n → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ x y : Fin n → ℝ, m * sq2 (fun i => x i - y i) ≤ dotp (fun i => F x i - F y i) (fun i => x i - y i)

/-- A strongly-monotone operator with positive modulus is **injective**. -/
theorem StronglyMonotone.injective {n : ℕ} {m : ℝ} (hm : 0 < m)
    {F : (Fin n → ℝ) → (Fin n → ℝ)} (hF : StronglyMonotone m F) :
    Function.Injective F := by
  intro x y hxy
  -- F x = F y ⇒ the inner product on the right is 0, so m·‖x−y‖² ≤ 0, forcing ‖x−y‖² = 0.
  have hzero : dotp (fun i => F x i - F y i) (fun i => x i - y i) = 0 := by
    have : (fun i => F x i - F y i) = (fun _ : Fin n => (0 : ℝ)) := by
      funext i; rw [hxy]; ring
    rw [this]; unfold dotp; simp
  have hle := hF x y
  rw [hzero] at hle
  have hsq : sq2 (fun i => x i - y i) ≤ 0 := by nlinarith [sq2_nonneg (fun i => x i - y i)]
  have heq : sq2 (fun i => x i - y i) = 0 :=
    le_antisymm hsq (sq2_nonneg _)
  have hdiff : (fun i => x i - y i) = 0 := (sq2_eq_zero _).mp heq
  funext i
  have := congrFun hdiff i
  simp only [Pi.zero_apply] at this
  linarith [this]

/-- The equation `F z = c` has **at most one** solution when `F` is strongly monotone
    (`m > 0`).  This is the uniqueness core of monDEQ well-posedness. -/
theorem StronglyMonotone.subsingleton_solutions {n : ℕ} {m : ℝ} (hm : 0 < m)
    {F : (Fin n → ℝ) → (Fin n → ℝ)} (hF : StronglyMonotone m F) (c : Fin n → ℝ) :
    ∀ z₁ z₂, F z₁ = c → F z₂ = c → z₁ = z₂ := by
  intro z₁ z₂ h₁ h₂
  exact hF.injective hm (h₁.trans h₂.symm)

/-- **monDEQ unique equilibrium (well-posedness, uniqueness half).**
    If the monDEQ residual operator `F z = z − G z` is strongly monotone with modulus `m > 0`,
    then the equilibrium equation `z = G z` (equivalently `F z = 0`) has **at most one** solution. -/
theorem monDEQ_unique_equilibrium {n : ℕ} {m : ℝ} (hm : 0 < m)
    (G : (Fin n → ℝ) → (Fin n → ℝ))
    (hF : StronglyMonotone m (fun z => fun i => z i - G z i)) :
    ∀ z₁ z₂, (∀ i, z₁ i = G z₁ i) → (∀ i, z₂ i = G z₂ i) → z₁ = z₂ := by
  intro z₁ z₂ h₁ h₂
  -- residual F z = z − G z; equilibrium z = G z ⟺ F z = 0
  set F : (Fin n → ℝ) → (Fin n → ℝ) := fun z => fun i => z i - G z i with hFdef
  have hr₁ : F z₁ = (fun _ : Fin n => (0 : ℝ)) := by
    funext i; simp only [hFdef]; rw [← h₁ i]; ring
  have hr₂ : F z₂ = (fun _ : Fin n => (0 : ℝ)) := by
    funext i; simp only [hFdef]; rw [← h₂ i]; ring
  exact hF.injective hm (hr₁.trans hr₂.symm)

end Lutar.Wave17
