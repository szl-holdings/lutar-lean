/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Uniqueness/Existence.lean — the EXISTENCE / realizability half of Theorem U

`TheoremU.lean` proves only the **uniqueness** half of identifiability: *if* an
aggregator `Φ` satisfies the Identifiability Assumptions (IA), then `Φ = Λ k`
(`identifiability_forces_lambda`). On its own that is a CONDITIONAL statement —
it says nothing unless some aggregator actually satisfies IA.

This module supplies the missing **existence** half: a kernel-checked proof that
`Λ k` itself satisfies IA, so the assumption class is NON-EMPTY and Theorem U is
non-vacuous. Combined with uniqueness, this upgrades "uniqueness modulo IA" into
the full, unconditional statement **"Λ is THE identifiable aggregator — it exists
and it is unique"** (the IA-solution set is exactly `{Λ k}`).

This is honest, distinct work and does NOT touch Conjecture 1 (the unconditional
Λ-uniqueness under A1–A5, which is machine-checked FALSE and stays OPEN): IA is
strictly stronger than A1–A5 — it additionally carries the separable/factored
response data that `maxAgg` lacks.

## What is PROVEN here (placeholder-free; NO new `axiom` token)

* `lambda_FactorAssumptions` — `Λ k` carries the `FactorAssumptions` bundle, built
  from the already-proven `Round13.lambda_satisfiesAxioms_round13` (Λ ⊨ A1–A5) and
  `Wave4.BlockConsistency.lambda_factors` (Λ factors with the equal exponents `1/k`).
* `lambda_IA` — **EXISTENCE**: `Λ k` satisfies the Identifiability Assumptions,
  obtained from `lambda_FactorAssumptions` through the proven bridge
  `factorAssumptions_to_IA`.
* `lambda_satisfies_IA` — the Prop-level existence witness: the IA class is
  `Nonempty` at `Λ k`.
* `mem_identifiability_solutions_iff` — **CAPSTONE (∀ Φ): `Φ` is an IA-solution iff
  `Φ = Λ k`** — existence (←) + `identifiability_forces_lambda` (→).
* `identifiability_solution_set_eq_lambda` — the same capstone as a set equality:
  `{Φ | Nonempty (IdentifiabilityAssumptions Φ)} = {Λ k}`.

## Honesty / scope
- Existence is genuinely TRUE and provable today; it needs NEITHER the forbidden
  founder axiom A6/bisymmetry NOR any new `axiom` token, and contains no proof
  placeholder (the `sorry_gate` over `Lutar/Uniqueness/` stays green).
- Locked-proven set unchanged (Theorem U is additive, excluded from the locked
  baseline). The UNCONDITIONAL Λ-uniqueness statement (`Conjecture1_LambdaUnique`)
  stays OPEN / machine-checked-false; Λ stays **Conjecture 1**. Theorem U is now
  the FULL existence+uniqueness statement *for the IA class only* — a strictly
  smaller, satisfiable hypothesis class than A1–A5.

## References
- Aczél, J. (1966). *Lectures on Functional Equations.* §5.1.
- Hardy, Littlewood, Pólya (1934). *Inequalities.* §2.18 (geometric mean).

Signed-off-by: SZL CTO <cto@szl-holdings.com>
-/
import Lutar.Uniqueness.TheoremU
import Lutar.Wave4.LambdaBlockConsistency
import Mathlib.Data.Set.Basic

namespace Lutar.Uniqueness

open Lutar Lutar.Round13

/-! ## Existence: `Λ k` realizes the assumption bundles -/

/-- `Λ k` satisfies the `FactorAssumptions`: it is a well-posed A1–A5 aggregator
    (`Round13.lambda_satisfiesAxioms_round13`) that factors into the equal per-axis
    power laws `t ↦ t^(1/k)` (`Wave4.BlockConsistency.lambda_factors`).
    `noncomputable` because the exponents live in `NNReal`. -/
noncomputable def lambda_FactorAssumptions {k : ℕ} (hk : 0 < k) :
    FactorAssumptions (Λ k) where
  pos := hk
  axioms := lambda_satisfiesAxioms_round13 hk
  exps := fun _ => (1 / k : NNReal)
  factors := Lutar.Wave4.BlockConsistency.lambda_factors hk

/-- **EXISTENCE half of Theorem U.** `Λ k` satisfies the Identifiability
    Assumptions, via the proven bridge `factorAssumptions_to_IA` applied to
    `lambda_FactorAssumptions`. This certifies the IA hypothesis class is
    non-empty, so Theorem U (`identifiability_forces_lambda`) is non-vacuous. -/
noncomputable def lambda_IA {k : ℕ} (hk : 0 < k) :
    IdentifiabilityAssumptions (Λ k) :=
  factorAssumptions_to_IA (lambda_FactorAssumptions hk)

/-- Prop-level existence witness: the Identifiability Assumptions are inhabited at
    `Λ k`. -/
theorem lambda_satisfies_IA {k : ℕ} (hk : 0 < k) :
    Nonempty (IdentifiabilityAssumptions (Λ k)) :=
  ⟨lambda_IA hk⟩

/-! ## Capstone: existence + uniqueness ⟹ the IA-solution set is exactly `{Λ k}` -/

/-- **Capstone (membership form).** For every aggregator `Φ`, `Φ` satisfies the
    Identifiability Assumptions iff `Φ = Λ k`. The `→` direction is Theorem U's
    uniqueness (`identifiability_forces_lambda`); the `←` direction is the
    existence half (`lambda_IA`). -/
theorem mem_identifiability_solutions_iff {k : ℕ} (hk : 0 < k) (Φ : Aggregator k) :
    Nonempty (IdentifiabilityAssumptions Φ) ↔ Φ = Λ k := by
  constructor
  · rintro ⟨ia⟩
    exact identifiability_forces_lambda Φ ia
  · rintro rfl
    exact ⟨lambda_IA hk⟩

/-- **Capstone (set form).** The set of aggregators satisfying the Identifiability
    Assumptions is exactly the singleton `{Λ k}`: Λ exists in the class and is the
    only member. This is the full existence+uniqueness statement of Theorem U over
    the IA class (NOT the unconditional A1–A5 class, which stays Conjecture 1). -/
theorem identifiability_solution_set_eq_lambda {k : ℕ} (hk : 0 < k) :
    {Φ : Aggregator k | Nonempty (IdentifiabilityAssumptions Φ)} = {Λ k} := by
  ext Φ
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  exact mem_identifiability_solutions_iff hk Φ

end Lutar.Uniqueness
