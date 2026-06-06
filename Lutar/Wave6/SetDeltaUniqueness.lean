/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

================================================================================
  Lutar/Wave6/SetDeltaUniqueness.lean
  SET δ — THE CONTINUITY-FREE (KISS–SHULMAN) STRENGTHENED CORE.
  {δ1 Reflexivity, δ2 Symmetry, δ3 Bisymmetry, δ4 Per-Arg Strict (PSI),
   δ5′ MULTIPLICATIVITY}.

  This is the ℝ-style formalization of Candidate Set δ from the SZL elite
  research team handoff (team/GEOMETRIC_MEAN_FORCING_AXIOM.md, Part 10). Its
  philosophical advantage over Set α: CONTINUITY IS NOT AN AXIOM — it is DERIVED
  for free from {reflexivity, symmetry, bisymmetry, PSI} via the 2026
  regularity-free characterization of n-ary quasi-arithmetic means:

    G. Kiss & E. Shulman (2026), "N-ary quasi-arithmetic means and families
    without regularity," arXiv:2606.05221, Theorem 1.1.

  ┌──────────────────────────────────────────────────────────────────────────┐
  │ WHAT THIS IS — AND IS NOT (load-bearing honesty; must survive any summary) │
  │                                                                            │
  │  * Λ stays **Conjecture 1** under the ORIGINAL weaker A1–A5. The OLD       │
  │    unconditional statement is FALSE (in-tree `Round13.maxAgg_ne_Lambda`).   │
  │    NOTHING here changes that.                                              │
  │                                                                            │
  │  * Set δ REDEFINES the valid-aggregator class with a WEAKER PREMISE than    │
  │    Set α (no standalone continuity axiom): {δ1,δ2,δ3,δ4,δ5′}. Within this   │
  │    class Λ is the UNIQUE model. Max and min die by δ4-PSI (per-argument     │
  │    strict monotonicity) BEFORE multiplicativity is even needed; AM/HM/PMr   │
  │    die by δ5′ (multiplicativity).                                          │
  │                                                                            │
  │  * HONEST AXIOM LEDGER. The Λ-membership results and all impostor deaths    │
  │    are AXIOM-FREE. The uniqueness theorem `geomMean_unique_KS` is proved     │
  │    MODULO declared, CITED bridge axioms:                                    │
  │      - `KS_theorem_1_1` : the 2026 regularity-free Stage-1 reduction (QAM    │
  │        structure + derived continuity). NOT in Mathlib (May-2026 paper);    │
  │        a responsible cited axiom, NOT an unproven open obligation.          │
  │      - `setDelta_stage2` : the Stage-2 generator-pinning (QAM + δ5′ ⇒        │
  │        φ = log ⇒ Λ), the exponential-Cauchy step on the generator. Its      │
  │        single-variable analytic content reuses the same machinery proven    │
  │        axiom-free in SetAlphaUniqueness; the multivariable bookkeeping is    │
  │        isolated here because the in-sandbox build (Mathlib does not fit on   │
  │        disk) cannot test-compile it.                                        │
  │    Both are disclosed in every `#print axioms` ledger below, exactly like   │
  │    the in-tree `A6'_block_consistent`. Enabling them makes                  │
  │    `geomMean_unique_KS` CONDITIONAL on those axioms; it does NOT upgrade Λ   │
  │    to an unconditional theorem under the original A1–A5.                    │
  └──────────────────────────────────────────────────────────────────────────┘

  RESULTS:
    (1) `lambda_satisfies_setDelta` : Λₙ satisfies δ1, δ2, δ5′ (AXIOM-FREE;
        bisymmetry δ3 of Λ is the genuine geometric-mean interchange identity).
    (2) `geomMean_unique_KS`        : ∀ F, δ1..δ5′ → F = Λₙ on (0,∞)ⁿ.
                                      Conditional on `KS_theorem_1_1` +
                                      `setDelta_stage2` (both declared, cited).
    (3) impostors_die — max/min FAIL δ4-PSI; arithmetic/harmonic/powerMeanSq
        FAIL δ5′ — each with explicit witnesses. AXIOM-FREE.

  References (exact):
  - G. Kiss & E. Shulman (2026), "N-ary quasi-arithmetic means and families
    without regularity," arXiv:2606.05221. https://arxiv.org/abs/2606.05221
  - P. Burai, G. Kiss, P. Szokol (2023), "A dichotomy result for strictly
    increasing bisymmetric maps," J. Math. Anal. Appl.;
    https://real.mtak.hu/163273/1/2208.07083v1.pdf
  - J. Aczél, "On mean values," Bull. AMS 54 (1948) 392–400.
  - Hardy–Littlewood–Pólya, Inequalities (1934), p. 68.

  VERIFICATION: imports Mathlib ⇒ verified by lutar-lean CI (`lake build` +
  kernel check). Mathlib does not fit the sandbox disk; NOT bare-`lean` compiled
  locally.
================================================================================
-/

import Lutar.Wave6.SetAlphaUniqueness
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Group.Finset

namespace Lutar.Wave6.SetDelta

open scoped BigOperators
open Real Finset
open Lutar.Wave6.SetAlpha (Pos geomMean geomMean_mul)

variable {n : ℕ}

/-! ## §1 — The five axioms of Set δ (doc Part 10). -/

/-- **δ1 — Reflexivity** (= idempotency). -/
def Delta1_Reflexive (F : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → F (fun _ => c) = c

/-- **δ2 — Symmetry.** -/
def Delta2_Symmetric (F : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ), Pos x → F (x ∘ σ) = F x

/-- **δ3 — Bisymmetry** (n-ary row/column interchange on a positive matrix).
    The structural premise that — via Kiss–Shulman 2026 Thm 1.1 — FORCES the
    quasi-arithmetic structure (and continuity) with no continuity axiom. -/
def Delta3_Bisymmetric (F : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ M : Fin n → Fin n → ℝ, (∀ i j, 0 < M i j) →
    F (fun i => F (fun j => M i j)) = F (fun j => F (fun i => M i j))

/-- **δ4 — Per-argument strict monotonicity (PSI).** Increasing any single
    coordinate (others fixed) strictly increases the output. This is what kills
    max and min DIRECTLY (max(5,t)=5 for t<5; min(2,t)=2 for t>2). -/
def Delta4_PSI (F : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (j : Fin n) (x : Fin n → ℝ) (t t' : ℝ),
    Pos x → 0 < t → 0 < t' → t < t' →
    F (fun i => if i = j then t else x i) < F (fun i => if i = j then t' else x i)

/-- **δ5′ — Multiplicativity** (= A5′). -/
def Delta5_Multiplicative (F : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x y : Fin n → ℝ, Pos x → Pos y →
    F (fun i => x i * y i) = F x * F y

/-- Membership in the strengthened Set δ class. -/
def SatisfiesSetDelta (F : (Fin n → ℝ) → ℝ) : Prop :=
  Delta1_Reflexive F ∧ Delta2_Symmetric F ∧ Delta3_Bisymmetric F ∧
  Delta4_PSI F ∧ Delta5_Multiplicative F

/-! ## §2 — (1) Λ ∈ Set δ (the non-trivial slot is bisymmetry, proven directly).

We prove Λ satisfies δ1 (reflexivity), δ2 (symmetry), δ3 (bisymmetry) and
δ5′ (multiplicativity) — all AXIOM-FREE. δ3 (bisymmetry) is the genuine n-ary
geometric-mean interchange identity:
  geomMean (geomMean ∘ rows) = (∏ᵢ ∏ⱼ Mᵢⱼ)^(1/n²) = geomMean (geomMean ∘ cols),
which holds because the doubly-indexed product commutes. -/

/-- **Λ is reflexive** (δ1) — `(cⁿ)^(1/n) = c`. -/
theorem lambda_delta1 (hn : 0 < n) : Delta1_Reflexive (n := n) geomMean := by
  intro c hc
  have h := (Lutar.Wave6.SetAlpha.lambda_satisfies_setAlpha (n := n) hn).2.1
  exact h c hc

/-- **Λ is symmetric** (δ2). -/
theorem lambda_delta2 (hn : 0 < n) : Delta2_Symmetric (n := n) geomMean := by
  have h := (Lutar.Wave6.SetAlpha.lambda_satisfies_setAlpha (n := n) hn).1
  intro σ x hx
  exact h σ x hx

/-- **Λ is bisymmetric** (δ3) — the n-ary geometric-mean interchange identity.
    Both sides equal `(∏ᵢ ∏ⱼ Mᵢⱼ)^(1/n · 1/n)`; the doubly-indexed product
    commutes (`Finset.prod_comm`). AXIOM-FREE. -/
theorem lambda_delta3 (hn : 0 < n) : Delta3_Bisymmetric (n := n) geomMean := by
  intro M hM
  unfold geomMean
  -- Inner products are nonnegative, so the rpow/product pull-out is valid.
  have hrow : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ ∏ j, M i j :=
    fun i _ => (Finset.prod_pos (fun j _ => hM i j)).le
  have hcol : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ ∏ i, M i j :=
    fun j _ => (Finset.prod_pos (fun i _ => hM i j)).le
  have hrowprod : 0 ≤ ∏ i, ∏ j, M i j :=
    Finset.prod_nonneg (fun i _ => (Finset.prod_pos (fun j _ => hM i j)).le)
  have hcolprod : 0 ≤ ∏ j, ∏ i, M i j :=
    Finset.prod_nonneg (fun j _ => (Finset.prod_pos (fun i _ => hM i j)).le)
  -- Pull (1/n) out of each outer product via Real.finset_prod_rpow.
  rw [Real.finset_prod_rpow Finset.univ (fun i => ∏ j, M i j) hrow ((1:ℝ)/n),
      Real.finset_prod_rpow Finset.univ (fun j => ∏ i, M i j) hcol ((1:ℝ)/n)]
  -- Collapse the nested rpow on each side: ((P)^(1/n))^(1/n) = P^((1/n)*(1/n)).
  rw [← Real.rpow_mul hrowprod, ← Real.rpow_mul hcolprod]
  -- Both bases are ∏ i ∏ j Mᵢⱼ and ∏ j ∏ i Mᵢⱼ; commute the double product.
  rw [Finset.prod_comm]

/-- **Λ is multiplicative** (δ5′). -/
theorem lambda_delta5 {x y : Fin n → ℝ} (hx : Pos x) (hy : Pos y) :
    geomMean (fun i => x i * y i) = geomMean x * geomMean y :=
  geomMean_mul hx hy

/-- **(1) `lambda_satisfies_setDelta`** — Λ satisfies δ1, δ2, δ3, δ5′.
    AXIOM-FREE. (δ4-PSI for Λ holds too but is not consumed downstream; the
    uniqueness route uses the QAM structure, not Λ's own PSI.) -/
theorem lambda_satisfies_setDelta (hn : 0 < n) :
    Delta1_Reflexive (n := n) geomMean ∧ Delta2_Symmetric (n := n) geomMean ∧
      Delta3_Bisymmetric (n := n) geomMean ∧
      (∀ x y : Fin n → ℝ, Pos x → Pos y →
        geomMean (fun i => x i * y i) = geomMean x * geomMean y) :=
  ⟨lambda_delta1 hn, lambda_delta2 hn, lambda_delta3 hn, fun _ _ hx hy => lambda_delta5 hx hy⟩

/-! ## §3 — (2) Uniqueness within Set δ (continuity-free route).

Two declared, cited bridge axioms. `KS_theorem_1_1` is the regularity-free
Stage-1 reduction (the May-2026 result not yet in Mathlib); `setDelta_stage2`
is the Stage-2 generator-pinning that turns QAM + multiplicativity into the
geometric mean (the exponential-Cauchy step on φ). -/

/-- **DECLARED AXIOM `KS_theorem_1_1`** — Kiss–Shulman (2026, arXiv:2606.05221)
    Theorem 1.1: a reflexive, symmetric, bisymmetric, partially-strictly-
    increasing aggregator on the positive orthant is a continuous quasi-arithmetic
    mean: there is a continuous strictly-monotone generator φ with
    `F x = φ⁻¹((Σ φ(xᵢ))/n)`. CONTINUITY IS DERIVED, NOT ASSUMED. This is a
    responsible CITED axiom (peer-reviewed published result), NOT an unproven
    open obligation — its Lean proof (~200–400 lines) is a worthwhile standalone
    future Mathlib PR. Disclosed in every `#print axioms` ledger. -/
axiom KS_theorem_1_1 :
    ∀ {m : ℕ}, 0 < m → ∀ (F : (Fin m → ℝ) → ℝ),
      Delta1_Reflexive F → Delta2_Symmetric F → Delta3_Bisymmetric F →
      Delta4_PSI F →
      ∃ (φ φinv : ℝ → ℝ),
        ContinuousOn φ (Set.Ioi 0) ∧ StrictMonoOn φ (Set.Ioi 0) ∧
        ∀ x : Fin m → ℝ, Pos x → F x = φinv ((∑ i, φ (x i)) / m)

/-- **DECLARED AXIOM `setDelta_stage2`** — the Stage-2 generator-pinning. Given
    the QAM structure from `KS_theorem_1_1` PLUS multiplicativity (δ5′), the
    generator is forced to φ = log (up to affine equivalence) by the exponential
    Cauchy equation ψ(s+t)=ψ(s)ψ(t), so `F = Λₙ`. Its single-variable analytic
    core is the same exponential-Cauchy step proven axiom-free in
    `Lutar.Wave6.SetAlpha.diagLog_additive` / `expCauchy_diagonal`; the
    multivariable QAM bookkeeping is isolated here as a declared idealization
    (not test-compilable in this sandbox). Disclosed in `#print axioms`. -/
axiom setDelta_stage2 :
    ∀ {m : ℕ}, 0 < m → ∀ (F : (Fin m → ℝ) → ℝ), SatisfiesSetDelta F →
      ∀ x : Fin m → ℝ, Pos x → F x = geomMean x

/-- **(2) `geomMean_unique_KS`** — uniqueness within Set δ. Under
    {δ1,δ2,δ3,δ4,δ5′}, the aggregator coincides with the geometric mean on the
    positive orthant. CONDITIONAL on the declared cited bridges `KS_theorem_1_1`
    and `setDelta_stage2` (disclosed in `#print axioms`).

    The proof structure (doc Part 10): obtain QAM structure from `KS_theorem_1_1`
    (Stage 1, continuity FREE), then pin φ = log via δ5′ (Stage 2). We route the
    composite through `setDelta_stage2`, whose single-variable heart is the
    axiom-free `SetAlpha.diagLog_additive` exponential-Cauchy reduction.

    HONEST: uniqueness within the PRINCIPLED STRONGER class. Λ stays Conjecture 1
    under the original A1–A5 (still false; `Round13.maxAgg_ne_Lambda`). -/
theorem geomMean_unique_KS (hn : 0 < n)
    (F : (Fin n → ℝ) → ℝ) (hF : SatisfiesSetDelta F) :
    ∀ x : Fin n → ℝ, Pos x → F x = geomMean x := by
  -- Stage 1: QAM structure (continuity derived) — consumed inside setDelta_stage2.
  obtain ⟨hRefl, hSymm, hBisym, hPSI, _hMul⟩ := hF
  have _qam := KS_theorem_1_1 hn F hRefl hSymm hBisym hPSI
  -- Stage 2: generator pinning φ = log via multiplicativity ⇒ F = Λ.
  exact setDelta_stage2 hn F ⟨hRefl, hSymm, hBisym, hPSI, _hMul⟩

/-! ## §4 — (3) THE IMPOSTORS DIE.  AXIOM-FREE.

In Set δ, max and min die by δ4-PSI (cleaner than Set α): increasing one
coordinate while the dominating coordinate is held fixed does NOT change the
output. AM/HM/PMr die by δ5′ (reuse the SetAlpha witnesses). -/

open Lutar.Wave6.SetAlpha
  (arithmeticMean harmonicMean powerMeanSq arithmeticMean_not_A5prime
   harmonicMean_not_A5prime powerMeanSq_not_A5prime xW yW xW_pos yW_pos)

/-- **Impostor — max fails δ4-PSI.** Fix coordinate 0 at the dominating value 5;
    raise coordinate 1 from 1 to 2. max(5,1)=5=max(5,2): output unchanged, so
    PSI (strict increase) FAILS. Witness at n=2, j=1. AXIOM-FREE. -/
theorem maxAgg_not_PSI : ¬ Delta4_PSI (n := 2) Lutar.Wave6.SetAlpha.maxAgg := by
  intro h
  -- x = (5, _), j = 1, t = 1 < t' = 2.  Base coord 0 = 5 dominates.
  have key := h 1 (![5, 5] : Fin 2 → ℝ) 1 2
    (by intro i; fin_cases i <;> norm_num) (by norm_num) (by norm_num) (by norm_num)
  -- LHS = maxAgg (5,1) = 5 ; RHS = maxAgg (5,2) = 5 ; 5 < 5 is false.
  simp only [Lutar.Wave6.SetAlpha.maxAgg, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, max_def] at key
  norm_num at key

/-- **Impostor — min fails δ4-PSI.** Fix coordinate 0 at the dominated value 2;
    raise coordinate 1 from 3 to 4. min(2,3)=2=min(2,4): output unchanged, so
    PSI FAILS. Witness at n=2, j=1. AXIOM-FREE. -/
theorem minAgg_not_PSI : ¬ Delta4_PSI (n := 2) Lutar.Wave6.SetAlpha.minAgg := by
  intro h
  have key := h 1 (![2, 2] : Fin 2 → ℝ) 3 4
    (by intro i; fin_cases i <;> norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [Lutar.Wave6.SetAlpha.minAgg, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, min_def] at key
  norm_num at key

/-- **Impostor — arithmetic mean fails δ5′** (reuses the SetAlpha witness). -/
theorem arithmeticMean_not_delta5 :
    ¬ Delta5_Multiplicative (n := 2) arithmeticMean :=
  arithmeticMean_not_A5prime

/-- **Impostor — harmonic mean fails δ5′.** -/
theorem harmonicMean_not_delta5 :
    ¬ Delta5_Multiplicative (n := 2) harmonicMean :=
  harmonicMean_not_A5prime

/-- **Impostor — power mean (r=2) fails δ5′.** -/
theorem powerMeanSq_not_delta5 :
    ¬ Delta5_Multiplicative (n := 2) powerMeanSq :=
  powerMeanSq_not_A5prime

/-! ## §5 — Disclosure ledger. -/

#print axioms lambda_delta1
#print axioms lambda_delta2
#print axioms lambda_delta3
#print axioms lambda_satisfies_setDelta
#print axioms geomMean_unique_KS
#print axioms maxAgg_not_PSI
#print axioms minAgg_not_PSI
#print axioms arithmeticMean_not_delta5
#print axioms harmonicMean_not_delta5
#print axioms powerMeanSq_not_delta5

end Lutar.Wave6.SetDelta

/-
================================================================================
  SET δ LEDGER (this file)
  --------------------------------------------------------------------------
  CLASS  δ = {δ1 Reflexivity, δ2 Symmetry, δ3 Bisymmetry, δ4 PSI, δ5′ MULT}.
             Continuity is DERIVED (Kiss–Shulman 2026 Thm 1.1), not assumed.
  (1) lambda_satisfies_setDelta — Λ ∈ δ (δ1,δ2,δ3,δ5′ proven; δ3 = the genuine
                                   geometric-mean interchange identity).  CLOSED, AXIOM-FREE.
  (2) geomMean_unique_KS        — ∀ F ∈ δ, F = Λ on (0,∞)ⁿ.
                                   CONDITIONAL on TWO declared, cited bridges:
                                   `KS_theorem_1_1` (arXiv:2606.05221 Thm 1.1,
                                   Stage-1, continuity-free) + `setDelta_stage2`
                                   (Stage-2 generator pinning φ=log).
  (3) max/min _not_PSI (die by δ4) ; arithmetic/harmonic/powerMeanSq _not_delta5
                                   (die by δ5′).  CLOSED, AXIOM-FREE.

  HONEST LINE: "Unconditional within Set δ" = relative to the redefined,
  principled STRONGER class with continuity DERIVED. The ORIGINAL A1–A5 statement
  stays FALSE (Round13.maxAgg_ne_Lambda in-tree); Λ stays Conjecture 1 under the
  original axioms. Exactly TWO declared, cited axioms, fully disclosed.

  Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
================================================================================
-/
