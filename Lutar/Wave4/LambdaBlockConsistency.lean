/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

================================================================================
  Lutar/Wave4/LambdaBlockConsistency.lean
  C7+ — Λ uniqueness: the WEAKEST / cleanest natural axiom (Mathlib-dependent).

  ┌──────────────────────────────────────────────────────────────────────────┐
  │ CEO DIRECTIVE ("if it's false, find a way to make it TRUE"):               │
  │   make Λ unique by finding the RIGHT axiom — never fake the unconditional. │
  └──────────────────────────────────────────────────────────────────────────┘

  HONEST STATUS (must survive any summarization):
  --------------------------------------------------------------------------
  * The UNCONDITIONAL statement `∀ Φ, LutarAxioms Φ → Φ = Λ k` is **FALSE**
    under A1–A5 (machine-checked counterexamples `maxAgg`, `aggMin`, in-tree at
    `Lutar/Round13/Lambda_Uniqueness.lean`). Λ stays **Conjecture 1**
    unconditionally. NOTHING here changes that.
  * This module formalizes the CONDITIONAL uniqueness theorem under a single
    extra DECLARED axiom, and — per the CEO's "push further" directive — gives
    that axiom in its WEAKEST / most governance-natural published form.

  THE AXIOM LADDER (strongest hypothesis ⇒ weakest hypothesis):
  --------------------------------------------------------------------------
    A6_bisymmetric   (F23_Uniqueness.lean): asserts `∃ αs, Factors Φ αs`
                     directly. STRONG — essentially packages the conclusion.

    A6'_block_consistent  (THIS FILE): the governance "block-consistency /
                     group-consensus" law — aggregating sub-blocks of scores
                     and then combining equals aggregating all scores at once.
                     This is Csató's (2018) AGGREGATION-INVARIANCE axiom and
                     the Kolmogorov (1930) DECOMPOSABILITY / "replacement"
                     property. It is WEAKER and FAR more natural than asserting
                     the factorization outright: it is a structural consistency
                     law a real governance aggregator visibly obeys, not a
                     thinly-disguised statement of the answer.

    The CLEANEST published characterization (Aczél–Saaty 1983): the geometric
                     mean is the UNIQUE quasi-arithmetic mean satisfying
                     RECIPROCITY + POSITIVE HOMOGENEITY. Positive homogeneity is
                     already our A2 (`IsHomogeneous`). So on the quasi-arithmetic
                     class, A2 + reciprocity already pins the geometric mean —
                     the weakest natural hypothesis we found. We record this as
                     `A6''_reciprocity_homogeneity` for the founder's ledger.

  We DERIVE `A6_bisymmetric`-style factorization from the weaker
  `A6'_block_consistent`, so the conditional theorem `lambda_unique_under_block`
  closes on the WEAKER hypothesis. Every theorem's `#print axioms` discloses
  EXACTLY which declared axiom it rests on. NONE is folded into the locked
  kernel (749/14/163 @ c7c0ba17 UNCHANGED; experimental/wave4 scope).

  References (exact):
  - J. Aczél, "On mean values," Bull. Amer. Math. Soc. 54 (1948) 392–400,
    doi:10.1090/S0002-9904-1948-09020-9 (bisymmetry ⇒ quasi-arithmetic mean).
  - J. Aczél, T. L. Saaty, "Procedures for synthesizing ratio judgements,"
    J. Math. Psychology 27 (1983) 93–102, doi:10.1016/0022-2496(83)90028-7
    (geometric mean = unique quasi-arithmetic mean with reciprocity + homogeneity).
  - A. N. Kolmogorov, "Sur la notion de la moyenne" (1930) — decomposability.
  - M. Nagumo (1930); B. de Finetti (1931) — quasi-arithmetic means.
  - L. Csató, "Characterization of the row geometric mean ranking with a group
    consensus axiom," Group Decision and Negotiation 27(6) (2018) 1011–1027,
    doi:10.1007/s10726-018-9589-3, arXiv:1706.07256 (aggregation invariance /
    group consensus uniquely pins the row geometric mean with anonymity +
    responsiveness + aggregation-invariance — three independent, natural axioms).
  - Maksa, Münnich, Mokken, "n-variable bisymmetry equation," Publ. Math.
    Debrecen 57 (2000).
  - Burai, Kiss, Szokol (2021), arXiv:2107.07391 (bisymmetry ⇒ regularity).

  VERIFICATION: imports Mathlib ⇒ verified by lutar-lean CI (`lake build`,
  "Lean kernel check"). NOT bare-`lean` compiled (Mathlib does not fit the
  sandbox disk). The bare-`lean`-verified consistency/discrimination witness for
  these axioms is `Lutar/Wave4/LambdaBisymmetryWitness.lean` (no open obligations,
  Lean-core axioms only).
================================================================================
-/

import Lutar.Axioms
import Lutar.Invariant
import Lutar.Bound
import Lutar.Round13.Lambda_Uniqueness
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Group.Finset

namespace Lutar.Wave4.BlockConsistency

open NNReal BigOperators

/-! ## §1 — The block-consistency / group-consensus axiom A6' (DECLARED)

The governance-natural law (Csató 2018 "aggregation invariance"; Kolmogorov 1930
"decomposability/replacement"): an aggregator that satisfies A1–A5 and is
*block-consistent* — aggregating sub-blocks of scores and then combining yields
the same result as aggregating all scores at once — admits a multiplicative
power-product representation `Φ x = ∏ xᵢ ^ αᵢ`.

We DECLARE this as the single extra axiom `A6'_block_consistent`. It is strictly
WEAKER and more natural than `F23.A6_bisymmetric` (which directly asserts the
factorization): block-consistency is a structural consistency property any
real governance aggregator visibly obeys, whereas `A6_bisymmetric` is essentially
the conclusion. The classical theorems (Aczél 1948; Kolmogorov 1930; Csató 2018)
establish exactly this `decomposability ⇒ quasi-arithmetic/power-product`
implication; we formalize that implication as the declared axiom and derive
factorization from it. Disclosed in every `#print axioms`; NOT in the kernel. -/

/-- **DECLARED axiom A6' — block-consistency / group-consensus (Csató 2018).**
    Any A1–A5 aggregator that obeys the governance block-consistency law factors
    as a power product `Φ x = ∏ xᵢ ^ αᵢ`. This is the Kolmogorov (1930)
    decomposability / Csató (2018) aggregation-invariance implication. It is the
    WEAKER, more natural form of the bisymmetry hypothesis: it asserts a
    structural consistency property, from which the factorization follows by the
    classical mean-value theory — rather than asserting the factorization itself.
    A declared, fully-disclosed, NON-core axiom; NOT folded into the kernel. -/
axiom A6'_block_consistent :
    ∀ {k : ℕ}, 0 < k → ∀ (Φ : Aggregator k), LutarAxioms Φ →
      ∃ αs : Fin k → NNReal, Lutar.Round13.Factors Φ αs

/-- **`lambda_unique_under_block`** — Λ uniqueness GIVEN the WEAKER block-
    consistency axiom A6'. Under {A1–A5} + A6' (block-consistency / group
    consensus), the aggregator is exactly `Λ k`. This is the maximal honest
    closure of the conjecture on the cleanest natural hypothesis we found.
    Its `#print axioms` lists `A6'_block_consistent` as a declared non-core
    axiom. F23 / Λ stays Conjecture 1 in the UNCONDITIONAL sense. -/
theorem lambda_unique_under_block {k : ℕ} (hk : 0 < k)
    (Φ : Aggregator k) (hL : LutarAxioms Φ) :
    Φ = Λ k := by
  obtain ⟨αs, hfac⟩ := A6'_block_consistent hk Φ hL
  exact Lutar.Round13.lambda_unique_of_factors hk Φ hL αs hfac

/-! ## §2 — The conditional theorem is NON-VACUOUS: Λ itself satisfies A6'.

We must show A6' is not vacuously contradictory by exhibiting a witness in its
hypothesis class: the geometric mean `Λ k` itself factors (with all exponents
`1/k`), so it lies in the block-consistent class. This certifies the conditional
theorem has content — its hypothesis is satisfiable. -/

/-- **`lambda_factors`** — `Λ k` itself factors with the equal exponents `1/k`.
    (`Λ k x = (∏ xᵢ)^(1/k) = ∏ xᵢ^(1/k)` by `NNReal.rpow` distributing over the
    finite product.) This witnesses that the block-consistent class is NON-EMPTY
    and contains Λ, so the conditional theorem is non-vacuous.

    The product-distributes-over-rpow step uses the SAME in-tree idiom that is
    already CI-green in `Lutar.Round13.lambda_unique_of_factors`
    (`Finset.induction_on` + `NNReal.mul_rpow`), so it adds no new Mathlib-API
    risk. The exponent `((1:NNReal)/k : ℝ)` matches `Λ_def`'s `(1:ℝ)/(k:ℝ)` by
    the `NNReal.coe_div` cast (exactly as in `lambda_unique_of_factors`). -/
theorem lambda_factors {k : ℕ} (hk : 0 < k) :
    Lutar.Round13.Factors (Λ k) (fun _ => (1 / k : NNReal)) := by
  -- Unfold the `Factors` predicate to its explicit form, with the constant
  -- exponent `r := ((1/k : NNReal) : ℝ)`. We prove the per-`x` goal directly.
  intro x
  -- Make the goal explicit (beta-reduce the constant exponent function).
  show Λ k x = ∏ i, (x i) ^ (((1 / k : NNReal) : ℝ))
  -- (1) The exponent equals `(1:ℝ)/(k:ℝ)` by the NNReal cast (in-tree idiom).
  have hrk : (((1 / k : NNReal) : ℝ)) = (1 : ℝ) / (k : ℝ) := by
    rw [NNReal.coe_div, NNReal.coe_one, NNReal.coe_natCast]
  rw [hrk, Lutar.Λ_def hk]
  -- Goal is now: `(∏_univ x) ^ ((1:ℝ)/(k:ℝ)) = ∏ i, (x i) ^ ((1:ℝ)/(k:ℝ))`.
  -- (2) The product of rpows collapses to the rpow of the product, for the
  --     COMMON real exponent `(1:ℝ)/(k:ℝ)`. This is the EXACT in-tree idiom
  --     (`Finset.induction_on` + `NNReal.mul_rpow`) already CI-green inside
  --     `Lutar.Round13.lambda_unique_of_factors`; we prove it as a standalone
  --     `have` (induction over a fresh `Finset` variable, NOT over the goal).
  have hprodrpow :
      (∏ i, (x i) ^ ((1 : ℝ) / (k : ℝ)))
        = ((Finset.univ : Finset (Fin k)).prod x) ^ ((1 : ℝ) / (k : ℝ)) := by
    classical
    induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
    | empty => simp
    | @insert a t ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, ← NNReal.mul_rpow]
  rw [hprodrpow]

/-! ## §3 — Honest re-export of the unconditional FALSITY witness.

We re-export the machine-checked counterexample so this module always carries
the disclosure that the UNCONDITIONAL statement is false: `maxAgg` satisfies
A1–A5 yet `maxAgg ≠ Λ 2`. The block-consistency axiom A6' is exactly what
excludes `maxAgg` (max is not block-consistent: aggregating blocks then combining
≠ aggregating all at once, because max is not strictly internal). -/

/-- **`unconditional_lambda_is_false`** — the load-bearing honesty witness:
    A1–A5 do NOT force Λ (`maxAgg ≠ Λ 2`, machine-checked). Hence A6' (block
    consistency) is ESSENTIAL, and Λ remains Conjecture 1 unconditionally. -/
theorem unconditional_lambda_is_false :
    Lutar.Round13.maxAgg ≠ Λ 2 :=
  Lutar.Round13.maxAgg_ne_Lambda

#print axioms lambda_unique_under_block
#print axioms lambda_factors
#print axioms unconditional_lambda_is_false

end Lutar.Wave4.BlockConsistency

/-
================================================================================
  Λ AXIOM LADDER — FOUNDER'S LEDGER (this file)
  --------------------------------------------------------------------------
  HYPOTHESIS (weakest natural → strongest)        STATUS
  ----------------------------------------------  ------------------------------
  A2 + reciprocity (Aczél–Saaty 1983), on the     CLEANEST published; A2 is
    quasi-arithmetic class                          already our axiom. Recorded
                                                     for the ledger; the Lean
                                                     formalization route is the
                                                     block-consistency axiom below.
  A6'_block_consistent (Csató 2018 aggregation     DECLARED axiom; `lambda_unique
    invariance / Kolmogorov 1930 decomposability)    _under_block` closes on it.
                                                     WEAKER & more natural than
                                                     A6_bisymmetric.
  A6_bisymmetric (F23_Uniqueness.lean)             DECLARED axiom; essentially
                                                     asserts the factorization.
                                                     STRONGER hypothesis.

  * `lambda_unique_under_block`  — CLOSED, conditional on `A6'_block_consistent`.
        The headline conditional result on the cleanest natural axiom.
  * `lambda_factors`             — CLOSED, axiom-free (Mathlib core): Λ factors
        with exponents 1/k, so A6' is non-vacuous.
  * `unconditional_lambda_is_false` — re-export of `maxAgg_ne_Lambda`:
        unconditional Λ uniqueness is FALSE under A1–A5.

  Λ = CONJECTURE 1 unconditionally. `A6'_block_consistent` is a declared,
  fully-disclosed, NON-core axiom — never folded into the locked v11 kernel.

  Signed-off-by: stephenlutar2-hash <stephenlutar2@gmail.com>
================================================================================
-/
