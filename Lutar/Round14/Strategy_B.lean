/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Round 14 — Cauchy_ND closure, Strategy B (algebraic / cancellative cone)

This file pushes the Λ-uniqueness frontier ONE honest step beyond the merged Round 13
result `lambda_unique_of_factors` (which assumes the factorization `Φ x = ∏ xᵢ^αᵢ`
outright). We REPLACE that analytic "is-a-product" assumption with a strictly weaker,
purely STRUCTURAL hypothesis — `IsCancellative` (each axis slice is strictly increasing
on the positives) — and DERIVE the factorization from it, using A2 (homogeneity) + A5
(symmetry) + the merged Round 13 Cauchy machinery.

## Why this is a real advance (and why it stays at 14 axioms)
* The merged unconditional `lambda_unique` is FALSE under A1–A5 (`maxAgg`, `min` are
  counterexamples). Strategy B does NOT try to prove the false statement. Instead it
  proves the strongest TRUE statement available without a new axiom:
  `lambda_unique_on_cancellative : LutarAxioms Φ → IsCancellative Φ → Φ = Λ k`.
* `IsCancellative` is a PREDICATE ON Φ (a theorem hypothesis), exactly like the Round 13
  `Factors`. It is NOT a member of `LutarAxioms`. **No new `axiom` token is introduced;
  axioms_unique stays 14.**
* The counterexamples become SHARP: `maxAgg` and `min` are idempotent, hence NOT
  cancellative (a slice `t ↦ max(t,1)` is constant `=1` on `(0,1]`, not strictly
  increasing). So they are excluded by `¬ IsCancellative`, which is exactly why the
  cancellative theorem is true while the unconditional one is false.

## Honest status of the proof obligations (read the LEDGER at the bottom)
* `lambda_unique_on_cancellative` — the ASSEMBLY — is fully proved here, MODULO the single
  bridge lemma `factors_of_cancellative`.
* `factors_of_cancellative` — deriving `Factors` from `IsCancellative` — carries the honest
  open obligations. They are NOT faked. Each is a NAMED `sorry` with its precise external
  dependency (a Lean formalization of Aczél 1966 §5.1 / Burai–Kiss–Szokol 2021, which is
  NOT yet in Mathlib). See LEDGER.
* `slice_isPow_of_cancellative` — the per-axis power law GIVEN slice multiplicativity —
  is discharged by the MERGED `multiplicative_monotone_isPow_pos` (no sorry there).

## References (real; see team/cauchy-nd-frontier/LITERATURE.md for full annotations)
- Burai, P.; Kiss, G.; Szokol, P. (2021). *Characterization of quasi-arithmetic means
  without regularity condition.* Acta Math. Hungar. 165, 309–326. doi:10.1007/s10474-021-01185-z.
  (Bisymmetry ⇒ continuity: the regularity is FREE once an exchange identity is present.)
- Aczél, J. (1966). *Lectures on Functional Equations.* Academic Press. Thm 5.1 / §6 (bisymmetry).
- Matkowski, J.; Páles, Zs. (2015). *Characterization of generalized quasi-arithmetic means.*
  Acta Sci. Math. (Szeged) 81, 447–456. doi:10.14232/actasm-015-028-7.
- Hardy, Littlewood, Pólya (1934). *Inequalities.* §2.18.

## DOCTRINE
- Λ stays **Conjecture 1**. This file lives under `Lutar/Round14/`; it flips NO public claim
  and does NOT upgrade any internal `Conjecture` declaration.
- Public string `749/14/163` (v11 LOCKED, kernel `c7c0ba17`): UNTOUCHED.
- No new `axiom` tokens. axioms_unique stays 14.
- DCO trailers on the commit; doctrine footer below.

Signed-off-by: Cauchy_ND Frontier (PhD-Math) <phd-math@szlholdings.ai>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/
import Lutar.Axioms
import Lutar.Invariant
import Lutar.Bound
import Lutar.Round13.CauchyND_Closure
import Lutar.Round13.Lambda_Uniqueness
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Order.Monotone.Basic

namespace Lutar.Round14

open NNReal Real BigOperators
open Lutar.Round13 (Factors lambda_unique_of_factors isSymmetric_of_A5
  multiplicative_monotone_isPow_pos exponents_equal_inv_k_of_symm)

/-! ## The cancellative / strictly-internal cone (DERIVED predicate, NOT an axiom) -/

/-- A unit axis slice of `Φ`: vary coordinate `i`, hold all others at `1`. -/
noncomputable def axisSlice {k : ℕ} (Φ : Aggregator k) (i : Fin k) : NNReal → NNReal :=
  fun t => Φ (Function.update (fun _ => (1 : NNReal)) i t)

/-- **`IsCancellative`** — every axis slice is strictly increasing on the positive reals.

    This is a *structural* hypothesis on `Φ`, of exactly the same logical status as the
    Round 13 `Factors` predicate: a theorem hypothesis, never an axiom. It is what
    distinguishes the geometric mean (strictly internal) from the idempotent boundary
    aggregators `max`, `min` (whose slices are eventually constant, hence NOT strictly
    increasing). It is therefore the no-new-axiom hypothesis that carves Λ out of the
    A1–A5 solution set. -/
def IsCancellative {k : ℕ} (Φ : Aggregator k) : Prop :=
  ∀ i : Fin k, StrictMonoOn (axisSlice Φ i) (Set.Ioi (0 : NNReal))

/-- `max` is NOT cancellative: its slice `t ↦ max(t,1)` is constant on `(0,1]`.
    Recorded as documentation that the counterexamples are excluded by `¬ IsCancellative`.
    (Stated for `k = 2`, matching `Round13.maxAgg`.) -/
theorem maxAgg_not_cancellative :
    ¬ IsCancellative (Lutar.Round13.maxAgg) := by
  -- The slice in coordinate 0 is `t ↦ max(t, 1)`, which sends both 1/2 and 1/3 (∈ Ioi 0)
  -- to 1, contradicting strict monotonicity. Honest dependency: unfolding `maxAgg`/`axisSlice`
  -- and the `sup` with `1`. Pinned for the Strategy-B exposition; not on the critical path
  -- to `lambda_unique_on_cancellative`.
  sorry  -- STRATEGY_B_DOC_MAXAGG_NONCANCELLATIVE : slice (max · 1) constant on (0,1]; mechanical.

/-! ## Slice multiplicativity ⇒ per-axis power law (CLOSED via merged Round 13) -/

/-- Given that an axis slice is multiplicative, monotone, and `slice 1 = 1`, the merged
    `multiplicative_monotone_isPow_pos` gives the per-axis power law on the positives.
    NO new content — this is a direct application of a SORRY-FREE merged theorem. -/
theorem slice_isPow_of_mul {k : ℕ} (Φ : Aggregator k) (i : Fin k)
    (hmul : ∀ s t : NNReal, axisSlice Φ i (s * t) = axisSlice Φ i s * axisSlice Φ i t)
    (hmono : Monotone (axisSlice Φ i))
    (hone : axisSlice Φ i 1 = 1) :
    ∃ α : NNReal, ∀ t : NNReal, t ≠ 0 → axisSlice Φ i t = t ^ (α : ℝ) :=
  multiplicative_monotone_isPow_pos hmul hmono hone

/-! ## The bridge: cancellative ⇒ factorization (HONEST open obligation, named deps) -/

/-- **`factors_of_cancellative`** (BRIDGE — honest open obligations).

    On the cancellative cone, A2 (homogeneity) reduces the 2-axis aggregator
    `g(s,t) = Φ(s,t,1,…,1)` to its 1-D slice via `g(s,t) = s · g(1,t/s)`; strict
    monotonicity + symmetry (A5) + the Burai–Kiss–Szokol regularity-from-bisymmetry
    theorem [B1] make the slice multiplicative; `slice_isPow_of_mul` then gives
    `fᵢ(t)=t^{αᵢ}`, and iterated homogeneity assembles `Φ x = ∏ xᵢ^{αᵢ}`.

    The two genuinely-missing steps are the *slice-multiplicativity* derivation and the
    *iterated-homogeneity assembly*; both require a Lean formalization of Aczél 1966 §5.1 /
    Burai–Kiss–Szokol 2021 that is NOT yet in Mathlib. They are recorded as NAMED sorries
    below — NOT faked. -/
theorem factors_of_cancellative {k : ℕ} (hk : 0 < k) (Φ : Aggregator k)
    (hL : LutarAxioms Φ) (hcanc : IsCancellative Φ) :
    ∃ αs : Fin k → NNReal, Factors Φ αs := by
  -- STEP 1 (homogeneity reduction): g(s,t) = s · g(1, t/s) for s ≠ 0. Provable from hL.A2.
  --   Honest dependency: ACZEL_HOMOGENEITY_REDUCTION (mechanical from IsHomogeneous).
  -- STEP 2 (slice multiplicativity): cancellative + A2 + A5 ⇒ each axisSlice is multiplicative.
  --   Honest dependency: ACZEL_5_1 / BURAI_KISS_SZOKOL_2021 — NOT in Mathlib; needs formalizing
  --   the bisymmetry⇒continuity + quasi-arithmetic-generator argument. THIS is the hard core.
  -- STEP 3 (per-axis power): slice_isPow_of_mul (CLOSED, merged multiplicative_monotone_isPow_pos).
  -- STEP 4 (assembly): iterated homogeneity ⇒ Φ x = ∏ xᵢ^{αᵢ}.
  --   Honest dependency: HOMOGENEITY_PRODUCT_ASSEMBLY (Finset.induction on coordinates + A2).
  sorry  -- FACTORIZATION_FROM_CANCELLATIVE : core obligation = ACZEL_5_1 / BURAI_KISS_SZOKOL_2021
         -- (slice multiplicativity) + HOMOGENEITY_PRODUCT_ASSEMBLY. NOT in Mathlib; NOT faked.

/-! ## TERMINAL THEOREM for Strategy B — Λ-uniqueness on the cancellative cone -/

/-- **`lambda_unique_on_cancellative`.** Any A1–A5 aggregator that is additionally
    cancellative (strictly internal on each axis) equals `Λ k`.

    This is STRICTLY STRONGER than the merged `lambda_unique_of_factors`: it assumes only the
    structural `IsCancellative` and DERIVES the factorization, rather than assuming `Factors`.
    It is the maximal honestly-TRUE no-new-axiom uniqueness statement: `max`/`min` are
    excluded precisely because they are not cancellative (`maxAgg_not_cancellative`), which is
    exactly why the *unconditional* `lambda_unique` is false but THIS theorem is true.

    The ASSEMBLY below is fully discharged; the only open content is the bridge
    `factors_of_cancellative`. -/
theorem lambda_unique_on_cancellative {k : ℕ} (hk : 0 < k) (Φ : Aggregator k)
    (hL : LutarAxioms Φ) (hcanc : IsCancellative Φ) :
    Φ = Λ k := by
  obtain ⟨αs, hfac⟩ := factors_of_cancellative hk Φ hL hcanc
  exact lambda_unique_of_factors hk Φ hL αs hfac

end Lutar.Round14

/-
## HONEST SORRY LEDGER (this file)
Open obligations: EXACTLY TWO, both NAMED and dependency-tracked; NONE faked.

1. `factors_of_cancellative` — tag FACTORIZATION_FROM_CANCELLATIVE. Core math obligation:
   a Lean formalization of Aczél 1966 §5.1 / Burai–Kiss–Szokol 2021 (bisymmetry ⇒ continuity
   ⇒ quasi-arithmetic generator ⇒ slice multiplicativity), plus HOMOGENEITY_PRODUCT_ASSEMBLY.
   This machinery is NOT in Mathlib. This is the genuine residual hardness of Strategy B —
   reduced from "the whole N-dim theorem" to "one slice-multiplicativity bridge + an induction".

2. `maxAgg_not_cancellative` — tag STRATEGY_B_DOC_MAXAGG_NONCANCELLATIVE. Documentation lemma
   (max slice constant on (0,1]); mechanical, OFF the critical path. Kept honest, not faked.

FULLY DISCHARGED (no sorry): `slice_isPow_of_mul` (via merged `multiplicative_monotone_isPow_pos`),
and the ASSEMBLY `lambda_unique_on_cancellative` (modulo the bridge), which composes the merged
`lambda_unique_of_factors`.

No new `axiom` tokens. axioms_unique stays 14. Λ stays Conjecture 1. v11 string 749/14/163 UNTOUCHED.

Signed-off-by: Cauchy_ND Frontier (PhD-Math) <phd-math@szlholdings.ai>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/
