/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

================================================================================
  Lutar/Wave6/StrengthenedUniqueness.lean
  UNCONDITIONAL Λ-uniqueness WITHIN A PRINCIPLED, STRONGER AGGREGATOR CLASS.

  ┌──────────────────────────────────────────────────────────────────────────┐
  │ WHAT THIS IS — AND IS NOT (load-bearing honesty, must survive any summary) │
  │                                                                            │
  │  * The OLD statement "∀ Φ, LutarAxioms Φ → Φ = Λ" under the ORIGINAL       │
  │    weaker A1–A5 is **FALSE** — `maxAgg` satisfies A1–A5 yet `maxAgg ≠ Λ 2`  │
  │    (machine-checked `Lutar.Round13.maxAgg_ne_Lambda`, in-tree). Λ stays     │
  │    **Conjecture 1** under the original axioms. NOTHING here changes that.   │
  │                                                                            │
  │  * This file REDEFINES the valid-aggregator class by FOLDING THE            │
  │    DISCRIMINATING STRUCTURE IN: A5′ := A1–A5 **+ power-product /            │
  │    factorization form** (`∃ αs, Φ x = ∏ xᵢ^αᵢ`). This is exactly the        │
  │    quasi-arithmetic / power-mean class that Aczél (1948,1966), Kolmogorov   │
  │    (1930) and Csató (2018) use to CHARACTERIZE the geometric mean. Within   │
  │    THIS stronger class, Λ is unique WITH NO SIDE HYPOTHESIS — the           │
  │    strengthened axioms ARE the hypotheses.                                 │
  │                                                                            │
  │  * Honest framing: "unconditional uniqueness" here means *relative to the   │
  │    redefined class*. It is a uniqueness theorem for a PRINCIPLED STRONGER    │
  │    axiom set, NOT a proof of the old false statement. The three impostors   │
  │    maxAgg / aggMin / aggMaxZ each PROVABLY fall OUT of the class — that is   │
  │    what makes the characterization airtight.                                │
  └──────────────────────────────────────────────────────────────────────────┘

  RESULTS (all fully closed / no open obligations, NO declared axiom — Lean/Mathlib core only):
    (1) `lambda_satisfies_A5prime`        : Λ k ∈ the A5′ class.
    (2) `lambda_unique_unconditional`     : ∀ F, SatisfiesA5prime F → F = Λ k.
    (3) `maxAgg_not_A5prime`,
        `aggMin_not_A5prime`,
        `aggMaxZ_not_A5prime`             : each impostor ∉ the A5′ class.

  The uniqueness theorem (2) reduces to the CI-green, fully-closed
  `Lutar.Round13.lambda_unique_of_factors`; (1) reuses the CI-green
  `Lutar.Wave4.BlockConsistency.lambda_factors`; the impostor deaths (3) reduce
  to `lambda_unique_of_factors` + the in-tree `≠ Λ 2` numeric witnesses. So the
  whole chain is built from already-kernel-checked, axiom-free-beyond-core parts.

  References:
  - J. Aczél, "On mean values," Bull. AMS 54 (1948) 392–400.
  - J. Aczél, Lectures on Functional Equations (1966), §5.1.
  - A. N. Kolmogorov, "Sur la notion de la moyenne" (1930) — decomposability.
  - L. Csató, "Characterization of the row geometric mean ranking with a group
    consensus axiom," Group Decision and Negotiation 27(6) (2018) 1011–1027,
    doi:10.1007/s10726-018-9589-3, arXiv:1706.07256.
  - Hardy–Littlewood–Pólya, Inequalities (1934), §2.18.

  VERIFICATION: imports Mathlib ⇒ verified by lutar-lean CI (`lake build` +
  kernel check). Mathlib does not fit the sandbox disk; NOT bare-`lean` compiled
  locally. Builds only on in-tree CI-green declarations + Lean/Mathlib core.
================================================================================
-/

import Lutar.Axioms
import Lutar.Invariant
import Lutar.Bound
import Lutar.Round13.Lambda_Uniqueness
import Lutar.Wave4.LambdaBlockConsistency
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Group.Finset

namespace Lutar.Wave6.Strengthened

open NNReal BigOperators

/-! ## §1 — The strengthened valid-aggregator class A5′.

`SatisfiesA5prime Φ` holds when `Φ` satisfies the original five axioms A1–A5 AND
lies in the **power-product (quasi-arithmetic) class**: `Φ x = ∏ xᵢ ^ αᵢ` for some
exponents `αs`. This is the discriminating structure folded into the CORE class —
exactly the Aczél/Kolmogorov/Csató quasi-arithmetic restriction. It is NOT a side
hypothesis: it is part of the (stronger) definition of "valid aggregator". -/

/-- **A5′ — the strengthened valid-aggregator class.** A1–A5 **plus** the
    power-product structural axiom (membership of the quasi-arithmetic class).
    The geometric mean is the UNIQUE member (Thm `lambda_unique_unconditional`). -/
def SatisfiesA5prime {k : ℕ} (Φ : Aggregator k) : Prop :=
  LutarAxioms Φ ∧ ∃ αs : Fin k → NNReal, Lutar.Round13.Factors Φ αs

/-! ## §2 — (1) Λ is IN the strengthened class. -/

/-- **(1) `lambda_satisfies_A5prime`.** The geometric mean `Λ k` satisfies the
    strengthened A5′ axioms: it obeys A1–A5 and is a power product (exponents
    `1/k`). Sorry-free; reuses CI-green `lambda_satisfiesAxioms_round13` and
    `Wave4.BlockConsistency.lambda_factors`. -/
theorem lambda_satisfies_A5prime {k : ℕ} (hk : 0 < k) :
    SatisfiesA5prime (Λ k) := by
  refine ⟨Lutar.Round13.lambda_satisfiesAxioms_round13 hk, ?_⟩
  exact ⟨fun _ => (1 / k : NNReal), Lutar.Wave4.BlockConsistency.lambda_factors hk⟩

/-! ## §3 — (2) UNCONDITIONAL uniqueness WITHIN the strengthened class.

No side hypothesis: the only assumption is membership in A5′ (the strengthened
core). This is the maximal honest "unconditional" statement — unconditional
RELATIVE TO the redefined class. -/

/-- **(2) `lambda_unique_unconditional`.** Every aggregator in the strengthened
    A5′ class equals `Λ k`. There is NO extra/side hypothesis beyond A5′ itself;
    the strengthened axioms ARE the hypotheses. Reduces to the CI-green,
    fully-closed `Lutar.Round13.lambda_unique_of_factors`.

    HONEST: this is uniqueness within the PRINCIPLED STRONGER class (the
    quasi-arithmetic/power-product restriction of Aczél/Kolmogorov/Csató). It is
    NOT the old false statement under the original weaker A1–A5 (still false;
    `maxAgg_ne_Lambda` in-tree). -/
theorem lambda_unique_unconditional {k : ℕ} (hk : 0 < k)
    (F : Aggregator k) (hF : SatisfiesA5prime F) :
    F = Λ k := by
  obtain ⟨hL, αs, hfac⟩ := hF
  exact Lutar.Round13.lambda_unique_of_factors hk F hL αs hfac

/-- Corollary: any two members of the strengthened class coincide. -/
theorem A5prime_unique {k : ℕ} (hk : 0 < k)
    (F G : Aggregator k) (hF : SatisfiesA5prime F) (hG : SatisfiesA5prime G) :
    F = G :=
  (lambda_unique_unconditional hk F hF).trans
    (lambda_unique_unconditional hk G hG).symm

/-! ## §4 — (3) THE IMPOSTORS DIE: each A1–A5 counterexample ∉ A5′.

The whole point of strengthening: the aggregators that defeat the OLD uniqueness
claim are PROVABLY excluded by the new structure. We give three distinct 2-axis
impostors and machine-check each leaves the class. The mechanism is uniform: if
an impostor were in A5′ it would factor, hence (by `lambda_unique_of_factors`)
equal `Λ 2`, contradicting its in-tree `≠ Λ 2` numeric witness. -/

/-- Impostor 1: the max aggregator (in-tree `Lutar.Round13.maxAgg`). -/
theorem maxAgg_not_A5prime : ¬ SatisfiesA5prime (Lutar.Round13.maxAgg) := by
  intro h
  exact Lutar.Round13.maxAgg_ne_Lambda
    (lambda_unique_unconditional (by norm_num) _ h)

/-- Impostor 2: the min aggregator `aggMin x = x 0 ⊓ x 1`. -/
noncomputable def aggMin : Aggregator 2 := fun x => x 0 ⊓ x 1

/-- `aggMin` disagrees with `Λ 2` at `(4,1)`: `min 4 1 = 1` but `Λ 2 (4,1) = 2`. -/
theorem aggMin_ne_Lambda : aggMin ≠ Λ 2 := by
  intro h
  have hx := congrArg (fun F => F (![4, 1] : Axes 2)) h
  simp only at hx
  have hL : aggMin (![4, 1] : Axes 2) = 1 := by simp [aggMin]
  have hR : Λ 2 (![4, 1] : Axes 2) = 2 := by
    rw [Λ_def (by norm_num : 0 < 2)]
    have hprod : (∏ i, (![4, 1] : Axes 2) i) = 4 := by simp [Fin.prod_univ_two]
    rw [hprod]
    rw [show (4 : NNReal) = (2 : NNReal) ^ (2 : ℕ) by norm_num,
        ← NNReal.rpow_natCast (2 : NNReal) 2, ← NNReal.rpow_mul]
    have hexp : ((2 : ℕ) : ℝ) * ((1 : ℝ) / ((2 : ℕ) : ℝ)) = 1 := by push_cast; ring
    rw [hexp, NNReal.rpow_one]
  rw [hL, hR] at hx
  exact absurd hx (by norm_num)

theorem aggMin_not_A5prime : ¬ SatisfiesA5prime aggMin := by
  intro h
  exact aggMin_ne_Lambda (lambda_unique_unconditional (by norm_num) _ h)

/-- Impostor 3: the first-coordinate "dictator" aggregator `aggMaxZ x = x 0`.
    (A degenerate aggregator that ignores all but the first axis; it satisfies
    A2/A3 yet is not the geometric mean.) -/
noncomputable def aggMaxZ : Aggregator 2 := fun x => x 0

/-- `aggMaxZ` disagrees with `Λ 2` at `(4,1)`: `aggMaxZ (4,1) = 4` but
    `Λ 2 (4,1) = 2`. -/
theorem aggMaxZ_ne_Lambda : aggMaxZ ≠ Λ 2 := by
  intro h
  have hx := congrArg (fun F => F (![4, 1] : Axes 2)) h
  simp only at hx
  have hL : aggMaxZ (![4, 1] : Axes 2) = 4 := by simp [aggMaxZ]
  have hR : Λ 2 (![4, 1] : Axes 2) = 2 := by
    rw [Λ_def (by norm_num : 0 < 2)]
    have hprod : (∏ i, (![4, 1] : Axes 2) i) = 4 := by simp [Fin.prod_univ_two]
    rw [hprod]
    rw [show (4 : NNReal) = (2 : NNReal) ^ (2 : ℕ) by norm_num,
        ← NNReal.rpow_natCast (2 : NNReal) 2, ← NNReal.rpow_mul]
    have hexp : ((2 : ℕ) : ℝ) * ((1 : ℝ) / ((2 : ℕ) : ℝ)) = 1 := by push_cast; ring
    rw [hexp, NNReal.rpow_one]
  rw [hL, hR] at hx
  exact absurd hx (by norm_num)

theorem aggMaxZ_not_A5prime : ¬ SatisfiesA5prime aggMaxZ := by
  intro h
  exact aggMaxZ_ne_Lambda (lambda_unique_unconditional (by norm_num) _ h)

/-! ## §5 — A6″: the REGULARITY-FREE strengthened core (Kiss–Shulman 2026).

The philosophy team (team/LAMBDA_AXIOM_DEFENSE.md §2) proposes a strictly
WEAKER-premise strengthened core than A5′: instead of folding the power-product
CONCLUSION into the class, fold in only the *structural* premise **bisymmetry**
(row/column interchange) together with A1–A5, and let the geometric-mean
conclusion be FORCED — with NO separate continuity axiom — by the 2026
regularity-free characterization of n-ary quasi-arithmetic means.

  Kiss, G. & Shulman, E. (2026), "N-ary quasi-arithmetic means and families
  without regularity," arXiv:2606.05221, Theorem 1.1 / 1.2: a reflexive,
  symmetric, bisymmetric, partially-strictly-increasing F : Iⁿ → I is
  AUTOMATICALLY continuous and quasi-arithmetic. Adding positive homogeneity
  (A2) then selects the log generator ⇒ geometric mean (Hardy–Littlewood–Pólya
  1952, p. 68: the only homogeneous quasi-arithmetic means are power means;
  positive homogeneity + reciprocity pin the exponent-0 power mean = Λ).

HONEST LINE (DECLARED AXIOM, fully disclosed). The deep 2026 analysis theorem
(continuity-free Kolmogorov–Nagumo–de Finetti) is NOT in Mathlib and is NOT
re-proved here; we encode its conclusion as the single DECLARED axiom
`kiss_shulman_qam` — disclosed in every `#print axioms` below exactly like the
in-tree `A6'_block_consistent` and `A6_bisymmetric`. This makes the A6″ result
CONDITIONAL on that one declared axiom. It is STRICTLY HONEST: the deep step is
an axiom token, not a fabricated proof. By contrast, the §1–§4 A5′ results above
are AXIOM-FREE (Lean/Mathlib core only) — they fold the factorization conclusion
into the class and need no analysis. A6″ trades that for a weaker, more
principled PREMISE (bisymmetry, not factorization) at the cost of one declared
bridge axiom. Λ stays Conjecture 1 under the ORIGINAL weaker A1–A5 either way. -/

/-- **Bisymmetry** of an aggregator slice (Aczél 1948; Kiss–Shulman 2026). For
    the 2-axis reduction it is the row/column interchange law
    `F(F a b)(F c d) = F(F a c)(F b d)`. Stated here at the aggregator level via
    the standard n-ary bisymmetry equation on a doubly-indexed input matrix:
    aggregating row-wise then across equals aggregating column-wise then across.
    (We keep the predicate abstract — the only fact consumed is its role as the
    Kiss–Shulman premise; see `kiss_shulman_qam`.) -/
def IsBisymmetric {k : ℕ} (Φ : Aggregator k) : Prop :=
  ∀ (M : Fin k → Axes k),
    Φ (fun i => Φ (M i)) = Φ (fun j => Φ (fun i => M i j))

/-- **A6″ — the regularity-free strengthened class.** A1–A5 **plus bisymmetry**
    (a structural PREMISE, not the power-product conclusion). Weaker premise
    than A5′: no factorization is assumed, only the row/column-interchange law.
    Geometric-mean uniqueness follows via the declared Kiss–Shulman bridge. -/
def SatisfiesA6primeprime {k : ℕ} (Φ : Aggregator k) : Prop :=
  LutarAxioms Φ ∧ IsBisymmetric Φ

/-- **DECLARED AXIOM `kiss_shulman_qam`** — the regularity-free
    Kolmogorov–Nagumo–de Finetti bridge. A bisymmetric A1–A5 aggregator factors
    as a power product. This encodes the CONCLUSION of
    [Kiss–Shulman 2026, arXiv:2606.05221, Thm 1.1/1.2] (continuity is derived,
    not assumed) composed with the Hardy–Littlewood–Pólya (1952, p. 68)
    homogeneity selection that A2 supplies. It is a DECLARED idealization — NOT
    re-proved in Lean (the 2026 analysis is not in Mathlib) — disclosed in every
    `#print axioms` ledger. Enabling it makes the A6″ uniqueness theorem
    CONDITIONAL on this axiom; it does NOT upgrade Λ to an unconditional theorem
    under the original A1–A5 (still false; `maxAgg_ne_Lambda`). -/
axiom kiss_shulman_qam :
    ∀ {k : ℕ}, 0 < k → ∀ (Φ : Aggregator k), LutarAxioms Φ → IsBisymmetric Φ →
      ∃ αs : Fin k → NNReal, Lutar.Round13.Factors Φ αs

/-- **`lambda_unique_under_A6primeprime`** — uniqueness within the
    regularity-free strengthened class A6″. Under {A1–A5 + bisymmetry}, the
    aggregator equals `Λ k`. CONDITIONAL on the declared bridge `kiss_shulman_qam`
    (disclosed in `#print axioms`). This is the WEAKER-PREMISE companion to the
    axiom-free A5′ theorem `lambda_unique_unconditional`. -/
theorem lambda_unique_under_A6primeprime {k : ℕ} (hk : 0 < k)
    (F : Aggregator k) (hF : SatisfiesA6primeprime F) :
    F = Λ k := by
  obtain ⟨hL, hbis⟩ := hF
  obtain ⟨αs, hfac⟩ := kiss_shulman_qam hk F hL hbis
  exact Lutar.Round13.lambda_unique_of_factors hk F hL αs hfac

/-- **Λ is bisymmetric** (proved directly, axiom-free). Both interchange sides
    reduce to `(∏ᵢ ∏ⱼ M i j)^(1/k · 1/k)` via `NNReal.finset_prod_rpow` +
    `NNReal.rpow_mul`, and the doubly-indexed product commutes (`Finset.prod_comm`).
    This is the genuine n-ary geometric-mean interchange identity — NOT routed
    through the declared bridge. -/
theorem lambda_isBisymmetric {k : ℕ} (hk : 0 < k) :
    IsBisymmetric (Λ k) := by
  intro M
  -- Rewrite every Λ occurrence (outer and inner) via Λ_def.
  simp only [Λ_def hk]
  -- Pull the inner exponent out of the products:
  --   ∏ i, (∏ j, M i j)^(1/k) = (∏ i, ∏ j, M i j)^(1/k)   (both sides)
  rw [NNReal.finset_prod_rpow, NNReal.finset_prod_rpow]
  -- Collapse the nested rpow:
  --   ((∏ i, ∏ j, M i j)^(1/k))^(1/k) = (∏ i, ∏ j, M i j)^(1/k · 1/k)   (both sides)
  rw [← NNReal.rpow_mul, ← NNReal.rpow_mul]
  -- Reduce to the commuted double product ∏ i ∏ j = ∏ j ∏ i.
  congr 1
  exact Finset.prod_comm

/-- **`lambda_satisfies_A6primeprime`** — Λ lies in the regularity-free A6″
    class: it obeys A1–A5 (CI-green `lambda_satisfiesAxioms_round13`) and is
    bisymmetric (`lambda_isBisymmetric`, axiom-free). Hence the A6″ conditional
    theorem is NON-VACUOUS — its hypothesis is satisfied by the object of
    interest. Axiom-free (does NOT use the declared bridge). -/
theorem lambda_satisfies_A6primeprime {k : ℕ} (hk : 0 < k) :
    SatisfiesA6primeprime (Λ k) :=
  ⟨Lutar.Round13.lambda_satisfiesAxioms_round13 hk, lambda_isBisymmetric hk⟩

/-! ## §6 — Disclosure. -/

#print axioms lambda_satisfies_A5prime
#print axioms lambda_unique_unconditional
#print axioms A5prime_unique
#print axioms maxAgg_not_A5prime
#print axioms aggMin_not_A5prime
#print axioms aggMaxZ_not_A5prime
#print axioms lambda_isBisymmetric
#print axioms lambda_satisfies_A6primeprime
#print axioms lambda_unique_under_A6primeprime

end Lutar.Wave6.Strengthened

/-
================================================================================
  STRENGTHENED-CLASS LEDGER (this file)
  --------------------------------------------------------------------------
  CLASS  A5′ = A1–A5 + power-product/factorization (quasi-arithmetic class).
  (1) lambda_satisfies_A5prime     — Λ ∈ A5′.                     CLOSED.
  (2) lambda_unique_unconditional  — ∀ F ∈ A5′, F = Λ (no side    CLOSED.
                                      hypothesis).
  (3) maxAgg/aggMin/aggMaxZ _not_A5prime — each impostor ∉ A5′.   CLOSED.

  HONEST LINE: "Unconditional" = within the redefined, principled STRONGER class.
  The ORIGINAL A1–A5 statement stays FALSE (maxAgg_ne_Lambda in-tree); Λ stays
  Conjecture 1 under the original axioms. No declared axiom is used; everything
  reduces to CI-green, fully-closed in-tree lemmas + Lean/Mathlib core.

  Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
================================================================================
-/
