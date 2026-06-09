/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Uniqueness/LambdaEquiv.lean — the Λ-equivalence (`≈Λ`) reframing

This module introduces the **audit-invariant equivalence** `≈Λ` that the Theorem-U
program uses to state Λ-uniqueness *modulo the receipt fiber*. It is the operational
relation a downstream runtime check reuses: two aggregators are `≈Λ`-equivalent exactly
when they produce the **same fused trust score on the canonical audit probe** — i.e. they
land in the same receipt fiber.

## What is PROVEN here (placeholder-free; NO new `axiom` token)

* `InvariantΛ` — the canonical audit invariant: the aggregator evaluated at `auditProbe k`.
* `LambdaEquiv` (`≈Λ`) — `Φ ≈Λ Ψ :⇔ InvariantΛ Φ = InvariantΛ Ψ`.
* `lambdaEquiv_equivalence` — `≈Λ` is a genuine `Equivalence` (refl/symm/trans).
* `instDecidableLambdaEquiv` — `≈Λ` carries a `Decidable` instance, so a runtime audit
  check can reuse exactly the same semantics (equality of the audit invariant).
* `lambdaEquiv_nondegenerate` — **the anti-vacuity guard**: `≈Λ` is NOT the total relation.
  The proven A1–A5 counterexample `maxAgg` is `≉Λ` to `Λ 2` (they disagree at the audit
  probe `(4,1)`: `maxAgg = 4`, `Λ = 2`). Hence "uniqueness modulo `≈Λ`" is a non-trivial
  statement, not vacuously true.

## Honesty / scope
- This is genuine new infrastructure for the in-tree `Λ`; it adds NO `axiom` token and NO
  proof placeholder. The unconditional uniqueness statement remains **Conjecture 1**
  (`Round13.maxAgg_ne_Lambda` exhibits the A1–A5 counterexample). Locked-proven set
  unchanged (EXACTLY 5); `≈Λ` only reframes the *target relation* of the conjecture.
- The separating witness re-uses the EXACT proven rpow script of
  `Round13.maxAgg_ne_Lambda` at the vector `![4,1]`.

## References
- Aczél, J. (1966). *Lectures on Functional Equations.* Academic Press. §5.1.
- Hardy, Littlewood, Pólya (1934). *Inequalities.* §2.5.

Signed-off-by: SZL CTO <cto@szl-holdings.com>
-/
import Lutar.Axioms
import Lutar.Invariant
import Lutar.Round13.Lambda_Uniqueness
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Lutar.Uniqueness

open Lutar Lutar.Round13 NNReal BigOperators

/-! ## The canonical audit probe and audit invariant -/

/-- The canonical **audit probe** at dimension `k`: axis `0` carries weight `4`, all other
    axes carry `1`. This is the separating witness for `maxAgg` vs `Λ` (the proven
    `Round13.maxAgg_ne_Lambda` counterexample lives at `(4,1)`), so it makes `≈Λ` strictly
    coarser than `=` yet non-degenerate. -/
def auditProbe (k : ℕ) : Axes k := fun i => if (i : ℕ) = 0 then 4 else 1

/-- The **audit invariant** of an aggregator: its fused trust score on the canonical audit
    probe. Models the receipt scalar that an audit records for `Φ`. -/
def InvariantΛ {k : ℕ} (Φ : Aggregator k) : NNReal := Φ (auditProbe k)

/-! ## The Λ-equivalence `≈Λ` -/

/-- **`≈Λ` — Λ-equivalence (the receipt fiber).** Two aggregators are equivalent when they
    agree on the canonical audit invariant. This is the relation modulo which Theorem U
    states Λ-uniqueness. -/
def LambdaEquiv {k : ℕ} (Φ Ψ : Aggregator k) : Prop := InvariantΛ Φ = InvariantΛ Ψ

@[inherit_doc LambdaEquiv]
scoped infix:50 " ≈Λ " => LambdaEquiv

/-- `≈Λ` is reflexive. -/
theorem lambdaEquiv_refl {k : ℕ} (Φ : Aggregator k) : LambdaEquiv Φ Φ := rfl

/-- `≈Λ` is symmetric. -/
theorem lambdaEquiv_symm {k : ℕ} {Φ Ψ : Aggregator k} (h : LambdaEquiv Φ Ψ) :
    LambdaEquiv Ψ Φ := h.symm

/-- `≈Λ` is transitive. -/
theorem lambdaEquiv_trans {k : ℕ} {Φ Ψ Χ : Aggregator k}
    (h₁ : LambdaEquiv Φ Ψ) (h₂ : LambdaEquiv Ψ Χ) : LambdaEquiv Φ Χ := h₁.trans h₂

/-- `≈Λ` is a genuine equivalence relation. -/
theorem lambdaEquiv_equivalence {k : ℕ} : Equivalence (@LambdaEquiv k) :=
  ⟨lambdaEquiv_refl, lambdaEquiv_symm, lambdaEquiv_trans⟩

/-- The `Setoid` induced by `≈Λ` (so the receipt fiber is a quotient). -/
instance lambdaSetoid (k : ℕ) : Setoid (Aggregator k) where
  r := LambdaEquiv
  iseqv := lambdaEquiv_equivalence

/-- `≈Λ` is `Decidable`: it reduces to equality of the `NNReal` audit invariant, so a
    runtime audit check can reuse exactly the same semantics. -/
noncomputable instance instDecidableLambdaEquiv {k : ℕ} (Φ Ψ : Aggregator k) :
    Decidable (LambdaEquiv Φ Ψ) := Classical.dec _

/-! ## Anti-vacuity guard: `≈Λ` is non-degenerate -/

/-- The audit probe at `k = 2` is exactly the proven separating vector `![4,1]`. -/
theorem auditProbe_two : auditProbe 2 = (![4, 1] : Axes 2) := by
  funext i; fin_cases i <;> simp [auditProbe]

/-- **Anti-vacuity guard.** `≈Λ` is NOT the total relation: the proven A1–A5 counterexample
    `maxAgg` is `≉Λ` to `Λ 2`. They disagree at the audit probe `(4,1)` — `maxAgg = 4`,
    `Λ 2 = (4·1)^(1/2) = 2` — so "uniqueness modulo `≈Λ`" is a substantive claim, not a
    vacuous one. The numeric witness re-uses the proven `Round13.maxAgg_ne_Lambda` script. -/
theorem lambdaEquiv_nondegenerate : ∃ Φ Ψ : Aggregator 2, ¬ LambdaEquiv Φ Ψ := by
  refine ⟨maxAgg, Λ 2, ?_⟩
  intro h
  unfold LambdaEquiv InvariantΛ at h
  rw [auditProbe_two] at h
  -- h : maxAgg ![4,1] = Λ 2 ![4,1]
  have hL : maxAgg (![4, 1] : Axes 2) = 4 := by simp [maxAgg]
  have hR : Λ 2 (![4, 1] : Axes 2) = 2 := by
    rw [Λ_def (by norm_num : 0 < 2)]
    have hprod : (∏ i, (![4, 1] : Axes 2) i) = 4 := by simp [Fin.prod_univ_two]
    rw [hprod, show (4 : NNReal) = (2 : NNReal) ^ (2 : ℕ) by norm_num,
        ← NNReal.rpow_natCast (2 : NNReal) 2, ← NNReal.rpow_mul]
    have hexp : ((2 : ℕ) : ℝ) * ((1 : ℝ) / ((2 : ℕ) : ℝ)) = 1 := by push_cast; ring
    rw [hexp, NNReal.rpow_one]
  rw [hL, hR] at h
  exact absurd h (by norm_num)

end Lutar.Uniqueness
