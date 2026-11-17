/-
Copyright © 2026 SZL Holdings.
Released under the Apache-2.0 License.

# Conjecture 1′ — Λ-uniqueness under A6 bisymmetry (FOUNDER-DECISION DRAFT, UNVERIFIED)

**Status: proposals/ scratch mirror. NOT compiled, NOT verified, NOT in `lake build`.**
Staged for PhD review + founder decision on adopting A6, per the tagged
FACTORIZATION_AXIOM_GAP obligation in Lutar/Round13/Lambda_Uniqueness.lean
("needs A6 (bisymmetry / associativity, Kolmogorov–Nagumo–Aczél) … with A6,
closes mechanically via lambda_unique_of_factors") and the BOUNTY.md soundness
caveat (A1–A4 refuted by min; A1–A5 refuted by maxAgg).

## What this draft contributes
1. `Bisymmetric` — the n-ary bisymmetry predicate (Kolmogorov 1930; Aczél 1966 §6.4).
2. `SliceStrictMono` — strict per-slice monotonicity (kills maxAgg/min witnesses:
   their slices are non-strict).
3. `Conjecture1Prime` — the tightened uniqueness statement: A1–A5 + A6 + strict
   slices ⇒ Φ = Λ k. This is the honest replacement for the machine-checked-false
   `Conjecture1_LambdaUnique` (A1–A5 alone).
4. Proof plan with the ONE genuinely new obligation isolated: `A6_to_Separability`
   (Aczél §6.4 route). Everything after it is ALREADY PROVEN estate machinery.

## Proof plan (each step mapped to existing or classical machinery)
- Step 0 (NEW — the genuine work): `A6_to_Separability`. Classical route
  (Aczél 1966 §6.4; HLP §2.18): bisymmetry + symmetry (A5) + idempotence on the
  diagonal (A3 normalize) + strict slice monotonicity ⇒ Φ is a quasi-arithmetic
  mean M_f. A2 (1-homogeneity) then forces the generator family to
  f ∈ {log, t ↦ t^α} — i.e. Φ x = (∏ xᵢ^αᵢ)^(1/Σαᵢ). Deliverable of this step:
  a `SeparableAssumptions Φ` (multiplicative, unit-normalized, monotone slices).
  ⚠️ OPEN. Not formalized here. This is the only step that is new mathematics.
- Step 1 (CLOSED): `separableAssumptions_to_IA` (Lutar/Uniqueness/Identifiability.lean).
- Step 2 (CLOSED): Theorem U machinery: any two IA-solutions agree modulo ≈Λ
  (Lutar/Uniqueness/TheoremU.lean), with strict `=` under Anchored/Normalized.
- Step 3 (CLOSED, direct alternative): `exponents_equal_inv_k_of_symm` pins every
  exponent to 1/k via A5 (Lutar/Round13/CauchyND_Closure.lean), then
  `lambda_unique_of_factors` finishes: Φ = Λ k.
- maxAgg/min do NOT satisfy A6 + strict slices (their witnesses are the very
  counterexamples that falsify the A1–A5-only form), so Conjecture 1′ is
  CONJECTURED TRUE, unlike the A1–A5 form, which is machine-checked false.

## Honesty
- Λ remains Conjecture 1 until a compiled sorry-free proof of Conjecture 1′ lands
  under the bounty CI. This draft upgrades nothing and claims nothing as PASS.
- Adopting A6 (+ strict slices) into the published axiom set is a FOUNDER decision
  (BOUNTY.md). This file only makes that decision concrete and reviewable.
-/

import Lutar.Axioms
import Lutar.Invariant
import Lutar.Round13.Lambda_Uniqueness
import Lutar.Uniqueness.Identifiability

namespace Lutar.Uniqueness.Conjecture1Prime

open Lutar Lutar.Round13 NNReal BigOperators

/-! ## A6 — bisymmetry (the missing axiom, made concrete) -/

/-- **A6 (n-ary bisymmetry; Kolmogorov 1930, Aczél 1966 §6.4).**
    Aggregating a k×k matrix row-first then across the row-means equals
    column-first then across the column-means. For k = 2 this is the classical
    B(x, y) := Φ(Φ(x₀,x₁), Φ(y₀,y₁)) = Φ(Φ(x₀,y₀), Φ(x₁,y₁)). -/
def Bisymmetric {k : ℕ} (Φ : Aggregator k) : Prop :=
  ∀ M : Fin k → Fin k → NNReal,
    Φ (fun i => Φ (M i)) = Φ (fun j => Φ (fun i => M i j))

/-- **Strict slice monotonicity.** Each single-axis slice t ↦ Φ(…,t,…) is
    STRICTLY monotone. This is what excludes `maxAgg` and `min` (their slices
    are monotone but not strictly) and, classically, what gives the quasi-
    arithmetic representation its injectivity. -/
def SliceStrictMono {k : ℕ} (Φ : Aggregator k) : Prop :=
  ∀ (i : Fin k) (s t : NNReal), s < t →
    Φ (fun j => if j = i then s else 1) < Φ (fun j => if j = i then t else 1)

/-! ## Conjecture 1′ — the tightened statement (FOUNDER-DECISION DRAFT) -/

/-- **Conjecture 1′ (Λ-Aggregator Uniqueness, A6 form).** Any aggregator satisfying
    A1–A5, n-ary bisymmetry (A6), and strict slice monotonicity equals `Λ k`.

    Unlike `Conjecture1_LambdaUnique` (A1–A5 alone — machine-checked FALSE via
    `maxAgg_ne_Lambda`), this form is CONJECTURED TRUE:
      * the classical Aczél §6.4 route turns A6 + A5 + A3-diagonal + strict slices
        into the quasi-arithmetic shape; A2 pins the generator to log/power;
      * the estate's CLOSED machinery then finishes
        (`exponents_equal_inv_k_of_symm` + `lambda_unique_of_factors`, or
        `separableAssumptions_to_IA` + Theorem U under Anchored).

    Stated as a `Prop` with NO proof: the remaining obligation is the single
    lemma `A6_to_Separability` (Step 0 in the file header). Do NOT upgrade any
    `Conjecture` declaration until a sorry-free compiled proof lands. -/
def Conjecture1Prime : Prop :=
  ∀ {k : ℕ} (_hk : 0 < k) (Φ : Aggregator k),
    LutarAxioms Φ → Bisymmetric Φ → SliceStrictMono Φ → Φ = Λ k

/-! ## The isolated new obligation (NOT PROVEN — the genuine remaining work) -/

/-- **`A6_to_Separability` (OPEN).** From A6 bisymmetry + A5 symmetry + A3
    diagonal normalization + strict slice monotonicity, derive a
    `SeparableAssumptions Φ` — the multiplicative, unit-normalized, monotone
    per-axis slices whose product reconstructs Φ.

    This is the ONLY genuinely new mathematics between Conjecture 1′ and the
    estate's closed uniqueness machinery (Steps 1–3 in the file header). The
    classical proof sketch (Aczél 1966 §6.4, HLP §2.18) supplies the mathematics;
    the Lean formalization is future work, honestly left open here. -/
theorem A6_to_Separability {k : ℕ} (hk : 0 < k)
    (Φ : Aggregator k) (hL : LutarAxioms Φ)
    (hB : Bisymmetric Φ) (hS : SliceStrictMono Φ) :
    SeparableAssumptions Φ := by
  -- OPEN OBLIGATION (A6_QUASIARITHMETIC_ROUTE). UNVERIFIED DRAFT — no proof
  -- is claimed or fabricated. Classical route: Aczél 1966 §6.4. This theorem
  -- statement exists so the founder decision and the PhD review have an exact,
  -- checkable target. Per HONESTY-OVER-CHECKLIST: no closed proof of an
  -- unformalized derivation is shipped.
  sorry

end Lutar.Uniqueness.Conjecture1Prime
