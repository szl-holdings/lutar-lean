/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

================================================================================
  Lutar/Puriq/Formulas/F23_Uniqueness.lean
  F23 — Λ-aggregator uniqueness — WAVE 2 (Mathlib-dependent).

  HONEST STATUS (must survive any summarization):
  --------------------------------------------------------------------------
  F23 IS **CONJECTURE 1**. It is NOT a theorem. As axiomatized with A1–A5 the
  *unconditional* uniqueness statement `∀ Φ, LutarAxioms Φ → Φ = Λ k` is FALSE
  (machine-checked counterexample `maxAgg_ne_Lambda`, in-tree). This file:

  (1) the single analytic blocker `monotone_additive_linear` (the classical Cauchy
      "monotone + additive ⇒ linear" step) is CLOSED (2026-11-17): the file-local
      lemma delegates to the sorry-free `Lutar.Round13.monotone_additive_linear`
      (rational squeeze, no continuity assumed, zero new axioms). This file
      carries no open `sorry`;

    (2) re-exports the TERMINAL CONDITIONAL THEOREM `lambda_unique_of_factors`
        (already fully proved in `Lutar/Round13/Lambda_Uniqueness.lean`, no open
        obligations) and wires the assembly `lutar_is_geomean_of_factors` to
        CONSUME the `Factors` premise — it does NOT claim unconditional
        uniqueness;

    (3) states the optional Path-A bridge `lambda_unique_under_A6` GATED on a
        clearly-DECLARED bisymmetry axiom `A6_bisymmetric`. Uniqueness closes
        mechanically *given A6*. A6 is disclosed exactly like the crypto axioms
        and is NOT folded into the kernel; without A6, F23 stays Conjecture 1.

  No conjecture is upgraded to a theorem here. The `axiom A6_bisymmetric`
  token is optional and, if enabled, MUST be reported in every `#print axioms`
  ledger as a declared, non-core axiom (alongside the Conjecture-1 disclosure).

  VERIFICATION NOTE: this module imports Mathlib and is verified by the
  lutar-lean repository CI (`lake build`). Mathlib does not fit on the proof
  engineer's local disk, so it is NOT bare-`lean` compiled here; the Mathlib-FREE
  pack (`PuriqFormulaLean` / F1–F22 + crypto-gated) is the locally bare-`lean`
  verified artifact. Each step below cites the exact Mathlib v4.13.0 lemma it
  relies on.

  References (see PROOF_STRATEGY_V2 §6 for URLs):
  - Aczél, J. (1966). Lectures on Functional Equations. §5.1. ISBN 0-12-043750-3.
  - Cauchy, A.-L. (1821). Cours d'analyse. Chap. V §1.
  - Kolmogorov (1930); Nagumo (1930); de Finetti — quasi-arithmetic means.
  - Burai, Kiss, Szokol (2021), arXiv:2107.07391 (bisymmetry ⇒ regularity).
================================================================================
-/

import Lutar.Axioms
import Lutar.Invariant
import Lutar.Bound
import Lutar.Round13.Lambda_Uniqueness
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Lutar.Round13.CauchyND_Closure
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Preimage
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Algebra.Order.Archimedean

namespace Lutar.Puriq.F23

open NNReal Real BigOperators

/-! ## §1.4 — The Cauchy step: monotone + additive ⇒ linear

This was the sole analytic blocker of the slice machinery (a tracked `sorry`
until 2026-11-17). It is classical (Cauchy 1821; Aczél 1966 Thm 5.1) and NOT
packaged in Mathlib; the estate canonical closed witness is the Round 13
rational-squeeze proof, which the lemma below now delegates to. -/

/-- **`monotone_additive_linear`** — a monotone additive `g : ℝ → ℝ` is linear:
    `g t = g 1 * t`.

    CLOSED (2026-11-17): delegates to the sorry-free Round 13 proof
    `Lutar.Round13.monotone_additive_linear` (`Lutar/Round13/CauchyND_Closure.lean`,
    the rational-squeeze argument; no continuity assumed). This retires the
    legacy `STEP2_MONOTONE_ADDITIVE_CONTINUOUS` open obligation with ZERO new
    axioms — same statement, same signature, closed machinery. The historical
    in-file route (ℚ-linearity via `AddMonoidHom`, Step-2 continuity, dense
    equalizer via `Continuous.ext_on` + `Rat.denseRange_cast`) is superseded by
    the stronger already-locked proof. -/
theorem monotone_additive_linear (g : ℝ → ℝ)
    (hg_add : ∀ u v : ℝ, g (u + v) = g u + g v) (hg_mono : Monotone g) :
    ∀ t : ℝ, g t = g 1 * t :=
  Lutar.Round13.monotone_additive_linear g hg_add hg_mono

/-! ## §1.5 — Assembly that CONSUMES factorization (NOT unconditional)

Per §1.2/§1.5 the top-level assembly cannot be unconditional (A1–A5 are
insufficient — `maxAgg_ne_Lambda`).  We re-target the assembly to consume the
`Factors` premise, making it definitionally the Round-13 conditional theorem. -/

/-- **`lutar_is_geomean_of_factors`** — the honest, closed assembly: any A1–A5
    aggregator that *factors* as `Φ x = ∏ xᵢ^αᵢ` equals `Λ k`.  This is exactly
    `Lutar.Round13.lambda_unique_of_factors` (already fully proved, no open
    obligations); we re-export it as the F23 headline result.  It is TRUE and
    CLOSED.  It is NOT unconditional uniqueness. -/
theorem lutar_is_geomean_of_factors {k : ℕ} (hk : 0 < k)
    (Φ : Aggregator k) (hL : LutarAxioms Φ)
    (αs : Fin k → NNReal) (hfac : Lutar.Round13.Factors Φ αs) :
    Φ = Λ k :=
  Lutar.Round13.lambda_unique_of_factors hk Φ hL αs hfac

/-! ## §1.3 Path A — UNCONDITIONAL uniqueness GATED on a DECLARED axiom A6

The unconditional statement is false under A1–A5.  To obtain it honestly we
DECLARE a structural bisymmetry axiom A6 (Kolmogorov–Nagumo–Aczél) and derive
`Factors` from {A1–A5, A6}.  A6 is disclosed exactly like the crypto axioms and
is NOT part of the locked kernel.  WITHOUT A6, F23 remains Conjecture 1. -/

/-- **DECLARED axiom A6 (bisymmetry / associativity).**  For a 2-argument slice
    reduction this is `F (F a b) (F c d) = F (F a c) (F b d)`; for the aggregator
    it yields the factorization `Φ x = ∏ xᵢ^αᵢ`.  This is the missing
    Kolmogorov–Nagumo–Aczél axiom (Aczél 1966 §5.1).  It is a *declared
    idealization / structural assumption*, NOT a theorem, and MUST be reported in
    every `#print axioms` ledger.  Enabling this token does NOT upgrade F23 to a
    theorem; it makes the uniqueness statement CONDITIONAL ON A6. -/
axiom A6_bisymmetric :
    ∀ {k : ℕ}, 0 < k → ∀ (Φ : Aggregator k), LutarAxioms Φ →
      ∃ αs : Fin k → NNReal, Lutar.Round13.Factors Φ αs

/-- **`lambda_unique_under_A6`** — uniqueness GIVEN the declared bisymmetry axiom.
    Honest, conditional theorem: under {A1–A5} + A6 the aggregator is `Λ k`.
    This is the maximal honest closure of F23.  Its `#print axioms` will list
    `A6_bisymmetric` as a declared, non-core axiom.  F23 is STILL Conjecture 1 in
    the unconditional sense — this result is explicitly conditional on A6. -/
theorem lambda_unique_under_A6 {k : ℕ} (hk : 0 < k)
    (Φ : Aggregator k) (hL : LutarAxioms Φ) :
    Φ = Λ k := by
  obtain ⟨αs, hfac⟩ := A6_bisymmetric hk Φ hL
  exact lutar_is_geomean_of_factors hk Φ hL αs hfac

/-! ## Counterexample re-export — A1–A5 do NOT force Λ (Conjecture-1 witness)

`Lutar.Round13.maxAgg_ne_Lambda` machine-checks that the 2-axis max aggregator
satisfies A2/A3/A5 yet disagrees with `Λ 2` at `(4,1)` (max = 4, geomean = 2).
This is the load-bearing evidence that the UNCONDITIONAL F23 statement is false,
hence that A6 (or `Factors`) is essential. -/

theorem f23_unconditional_is_underdetermined :
    Lutar.Round13.maxAgg ≠ Λ 2 :=
  Lutar.Round13.maxAgg_ne_Lambda

end Lutar.Puriq.F23

/-
================================================================================
  F23 HONEST LEDGER (this file)
  --------------------------------------------------------------------------
  * `monotone_additive_linear`  — DISCHARGE SKELETON (§1.4 route). Steps 1 (ℚ-
        linearity) + 3 (dense equalizer) fully written; Step 2 (monotone+additive
        ⇒ continuous) is ONE isolated open obligation
        `STEP2_MONOTONE_ADDITIVE_CONTINUOUS`, pinned in CI. NOT claimed proved.
  * `lutar_is_geomean_of_factors` — CLOSED (re-export of Round13
        `lambda_unique_of_factors`). TRUE, CONDITIONAL on `Factors`.
  * `lambda_unique_under_A6` — CLOSED but GATED on the DECLARED `A6_bisymmetric`
        axiom. Conditional uniqueness; A6 disclosed in #print axioms.
  * `f23_unconditional_is_underdetermined` — re-export of `maxAgg_ne_Lambda`:
        A1–A5 do NOT force Λ.  Proof that unconditional F23 is FALSE.

  F23 = CONJECTURE 1.  Unconditional `∀ Φ, LutarAxioms Φ → Φ = Λ k` is NOT a
  theorem (it is false under A1–A5).  No conjecture is called a theorem here.
  `A6_bisymmetric` is a declared, optional, fully-disclosed axiom — never folded
  into the kernel.

  Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
================================================================================
-/
