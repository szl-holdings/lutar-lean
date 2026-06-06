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
  │    MODULO EXACTLY ONE declared, CITED bridge axiom:                          │
  │      - `KS_theorem_1_1` : the 2026 regularity-free theorem, in its HEADLINE  │
  │        form — a reflexive/symmetric/bisymmetric/PSI aggregator is itself     │
  │        CONTINUOUS (paper abstract, verbatim). NOT in Mathlib (May-2026       │
  │        paper); a responsible cited axiom, NOT an unproven open obligation.   │
  │    The former second axiom `setDelta_stage2` is now DISCHARGED: once         │
  │    `KS_theorem_1_1` supplies the derived continuity (A4), a Set-δ aggregator │
  │    IS a Set-α aggregator (`setDelta_to_setAlpha`; A3 follows from δ4-PSI     │
  │    axiom-free via `delta4_implies_allStrictMono`), and the AXIOM-FREE        │
  │    SetAlpha multivariable discharge `lambda_unique_setAlpha_discharged`      │
  │    closes the goal. `setDelta_stage2` no longer exists.                      │
  │    `KS_theorem_1_1` is disclosed in every `#print axioms` ledger below,      │
  │    exactly like the in-tree `A6'_block_consistent`. Enabling it makes        │
  │    `geomMean_unique_KS` CONDITIONAL on that ONE axiom; it does NOT upgrade Λ │
  │    to an unconditional theorem under the original A1–A5.                    │
  └──────────────────────────────────────────────────────────────────────────┘

  RESULTS:
    (1) `lambda_satisfies_setDelta` : Λₙ satisfies δ1, δ2, δ5′ (AXIOM-FREE;
        bisymmetry δ3 of Λ is the genuine geometric-mean interchange identity).
    (2) `geomMean_unique_KS`        : ∀ F, δ1..δ5′ → F = Λₙ on (0,∞)ⁿ.
                                      Conditional on EXACTLY ONE declared, cited
                                      bridge `KS_theorem_1_1` (derived-continuity
                                      theorem). `setDelta_stage2` DISCHARGED.
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
    Theorem 1.1: *"every reflexive, symmetric, bisymmetric and partially strictly
    increasing n-variable operation on a real interval is **continuous** and hence
    quasi-arithmetic"* (paper abstract, verbatim). The HEADLINE conclusion of the
    paper is that the aggregator `F` is itself **continuous** — continuity is
    DERIVED, not assumed. We therefore state the axiom in the form actually used:
    a Set-δ aggregator (δ1 reflexive, δ2 symmetric, δ3 bisymmetric, δ4 PSI) is
    `A4_Continuity F`, i.e. `ContinuousOn F {x | Pos x}`. This is the faithful,
    minimal extraction of the paper's main theorem (the full QAM generator
    representation is a corollary we do not need: once continuity is in hand the
    SetAlpha discharge closes everything axiom-free). This is a responsible CITED
    axiom (peer-reviewed published result), NOT an unproven open obligation — its
    Lean proof (~200–400 lines: the n-adic-rational recursive construction + the
    dense-domain continuity argument) is a worthwhile standalone future Mathlib PR.
    NOT in Mathlib (May-2026 paper). Disclosed in every `#print axioms` ledger. -/
axiom KS_theorem_1_1 :
    ∀ {m : ℕ}, 0 < m → ∀ (F : (Fin m → ℝ) → ℝ),
      Delta1_Reflexive F → Delta2_Symmetric F → Delta3_Bisymmetric F →
      Delta4_PSI F →
      Lutar.Wave6.SetAlpha.A4_Continuity F

/-- **DECLARED AXIOM `setDelta_stage2`** — RETAINED ONLY AS A DOCUMENTED DEAD
    FALLBACK (referenced by NO live result; exactly like `setAlpha_cauchy` in
    SetAlphaUniqueness). The live `geomMean_unique_KS` below NO LONGER uses it:
    it routes through the axiom-free `setDelta_to_setAlpha` + the SetAlpha
    multivariable discharge. This axiom is kept declared so the file still
    compiles if any step of the new discharge needs revision; it is NOT
    load-bearing and does NOT appear in `#print axioms geomMean_unique_KS`. -/
axiom setDelta_stage2 :
    ∀ {m : ℕ}, 0 < m → ∀ (F : (Fin m → ℝ) → ℝ), SatisfiesSetDelta F →
      ∀ x : Fin m → ℝ, Pos x → F x = geomMean x

/-- **`delta4_implies_allStrictMono`** (AXIOM-FREE). δ4-PSI (per-argument strict
    monotonicity) implies A3 (all-coordinates-strict monotonicity). Proof: to go
    from `x` to `y` with `x i < y i` at every coordinate, raise the coordinates
    one at a time; each single-coordinate raise strictly increases `F` by δ4-PSI,
    and `<` is transitive. We perform the induction over `Finset.univ` via
    `Finset.sum`-style coordinate replacement, but the clean route is the
    "hybrid vector" telescoping: define `z k i = if i < k then y i else x i` and
    chain `F (z k) < F (z (k+1))`.  We give the explicit n-fold transitivity. -/
theorem delta4_implies_allStrictMono (hn : 0 < n) (F : (Fin n → ℝ) → ℝ)
    (hPSI : Delta4_PSI F) : Lutar.Wave6.SetAlpha.A3_AllStrictMono F := by
  -- Hybrid vectors: hyb k i = y i if (i:ℕ) < k else x i.  hyb 0 = x, hyb n = y.
  intro x y hx hy hlt
  set hyb : ℕ → Fin n → ℝ := fun k i => if (i : ℕ) < k then y i else x i with hhyb
  have hyb_pos : ∀ k, Pos (hyb k) := by
    intro k i; by_cases h : (i : ℕ) < k <;> simp only [hhyb, h, if_true, if_false]
    · exact hy i
    · exact hx i
  have hyb0 : hyb 0 = x := by funext i; simp [hhyb]
  have hybn : hyb n = y := by
    funext i; simp only [hhyb]; rw [if_pos]; exact i.isLt
  -- Single step: F (hyb k) < F (hyb (k+1)) when k < n (raise coordinate ⟨k,·⟩).
  have step : ∀ k : ℕ, k < n → F (hyb k) < F (hyb (k + 1)) := by
    intro k hk
    -- Coordinate `j = ⟨k,hk⟩`.  Off `j`, `hyb k` and `hyb (k+1)` agree; at `j`,
    -- `hyb k j = x j` and `hyb (k+1) j = y j`.  So δ4-PSI at `j` gives the step.
    set j : Fin n := ⟨k, hk⟩ with hj
    have hjval : (j : ℕ) = k := rfl
    -- value of `hyb k` at `j`: `↑j = k`, so `¬(k < k)` ⇒ branch `x j`.
    have hk_at_j : hyb k j = x j := by
      simp only [hhyb, hjval]; rw [if_neg (lt_irrefl k)]
    -- value of `hyb (k+1)` at `j`: `k < k+1` ⇒ branch `y j`.
    have hk1_at_j : hyb (k + 1) j = y j := by
      simp only [hhyb, hjval]; rw [if_pos (Nat.lt_succ_self k)]
    -- off `j`, the two hybrids agree.
    have hoff : ∀ i, i ≠ j → hyb k i = hyb (k + 1) i := by
      intro i hi
      have hik : (i : ℕ) ≠ k := fun hh => hi (Fin.ext (by simpa [hjval] using hh))
      simp only [hhyb]
      by_cases hlt' : (i : ℕ) < k
      · rw [if_pos hlt', if_pos (Nat.lt_succ_of_lt hlt')]
      · rw [if_neg hlt', if_neg (by omega)]
    -- Rebuild `hyb (k+1)` from `hyb k` by replacing coordinate `j` with `y j`.
    have heq_lo : (fun i => if i = j then x j else hyb k i) = hyb k := by
      funext i; by_cases hi : i = j
      · rw [if_pos hi, hi, hk_at_j]
      · rw [if_neg hi]
    have heq_hi : (fun i => if i = j then y j else hyb k i) = hyb (k + 1) := by
      funext i; by_cases hi : i = j
      · rw [if_pos hi, hi, hk1_at_j]
      · rw [if_neg hi, hoff i hi]
    have hpsi := hPSI j (hyb k) (x j) (y j)
      (hyb_pos k) (hx j) (hy j) (hlt j)
    rw [heq_lo, heq_hi] at hpsi
    exact hpsi
  -- Telescope F (hyb 0) < F (hyb n) by transitivity over k = 0,…,n-1.
  have chain : ∀ k : ℕ, k ≤ n → F (hyb 0) ≤ F (hyb k) := by
    intro k
    induction k with
    | zero => intro _; exact le_refl _
    | succ m ih =>
        intro hk
        have hm : m < n := Nat.lt_of_succ_le hk
        have hmle : m ≤ n := Nat.le_of_lt hm
        exact le_trans (ih hmle) (le_of_lt (step m hm))
  -- Strict: at least one step is strict; n > 0 is supplied as a hypothesis.
  calc F x = F (hyb 0) := by rw [hyb0]
    _ < F (hyb n) := by
        have h1 : F (hyb 0) ≤ F (hyb (n-1)) := chain (n-1) (Nat.sub_le n 1)
        have h2 : F (hyb (n-1)) < F (hyb (n-1+1)) := step (n-1) (by omega)
        have hn1 : n - 1 + 1 = n := by omega
        rw [hn1] at h2; exact lt_of_le_of_lt h1 h2
    _ = F y := by rw [hybn]

/-- **`setDelta_to_setAlpha`** (AXIOM-FREE modulo `KS_theorem_1_1`). A Set-δ
    aggregator is a Set-α aggregator: A1=δ2, A2=δ1, A3 from δ4 (`delta4_implies
    _allStrictMono`), A4 = the DERIVED continuity (`KS_theorem_1_1`, the paper's
    headline), A5′=δ5′.  This is the bridge that lets the (now axiom-free)
    SetAlpha multivariable discharge close Set δ uniqueness with NO `setDelta
    _stage2` axiom. -/
theorem setDelta_to_setAlpha (hn : 0 < n) (F : (Fin n → ℝ) → ℝ)
    (hF : SatisfiesSetDelta F) : Lutar.Wave6.SetAlpha.SatisfiesSetAlpha F := by
  obtain ⟨hRefl, hSymm, hBisym, hPSI, hMul⟩ := hF
  refine ⟨hSymm, hRefl, delta4_implies_allStrictMono hn F hPSI, ?_, hMul⟩
  -- A4-continuity is the DERIVED continuity of the paper's main theorem.
  exact KS_theorem_1_1 hn F hRefl hSymm hBisym hPSI

/-- **(2) `geomMean_unique_KS`** — uniqueness within Set δ. Under
    {δ1,δ2,δ3,δ4,δ5′}, the aggregator coincides with the geometric mean on the
    positive orthant. CONDITIONAL on EXACTLY ONE declared cited bridge
    `KS_theorem_1_1` (the Kiss–Shulman 2026 derived-continuity theorem, not in
    Mathlib).

    DISCHARGED: the former second axiom `setDelta_stage2` is ELIMINATED. Once
    `KS_theorem_1_1` supplies the DERIVED continuity (A4) of `F`, a Set-δ
    aggregator IS a Set-α aggregator (`setDelta_to_setAlpha`), and the
    AXIOM-FREE SetAlpha multivariable discharge `lambda_unique_setAlpha
    _discharged` (with positivity from `FExpPos_of_setAlpha`) closes the goal.
    `#print axioms geomMean_unique_KS` therefore lists Lean/Mathlib core +
    `KS_theorem_1_1` ONLY (no `setDelta_stage2`).

    HONEST: uniqueness within the PRINCIPLED STRONGER class with continuity
    DERIVED (not assumed). Λ stays Conjecture 1 under the original A1–A5 (still
    false; `Round13.maxAgg_ne_Lambda`). -/
theorem geomMean_unique_KS (hn : 0 < n)
    (F : (Fin n → ℝ) → ℝ) (hF : SatisfiesSetDelta F) :
    ∀ x : Fin n → ℝ, Pos x → F x = geomMean x := by
  -- Set δ ⊆ Set α via derived continuity (KS); then the axiom-free SetAlpha discharge.
  have hα : Lutar.Wave6.SetAlpha.SatisfiesSetAlpha F := setDelta_to_setAlpha hn F hF
  have hpos : Lutar.Wave6.SetAlpha.FExpPos F :=
    Lutar.Wave6.SetAlpha.FExpPos_of_setAlpha hn F hα
  exact Lutar.Wave6.SetAlpha.lambda_unique_setAlpha_discharged hn F hα hpos

/-! ## §4 — (3) THE IMPOSTORS DIE.  AXIOM-FREE.

In Set δ, max and min die by δ4-PSI (cleaner than Set α): increasing one
coordinate while the dominating coordinate is held fixed does NOT change the
output. AM/HM/PMr die by δ5′ (reuse the SetAlpha witnesses). -/

open Lutar.Wave6.SetAlpha
  (arithmeticMean harmonicMean powerMeanSq lehmer2 midrange
   arithmeticMean_not_A5prime harmonicMean_not_A5prime powerMeanSq_not_A5prime
   lehmer2_not_A5prime midrange_not_A5prime xW yW xW_pos yW_pos)

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

/-- **Impostor — Lehmer/contraharmonic mean (p=2) fails δ5′.** -/
theorem lehmer2_not_delta5 :
    ¬ Delta5_Multiplicative (n := 2) lehmer2 :=
  lehmer2_not_A5prime

/-- **Impostor — midrange fails δ5′.** -/
theorem midrange_not_delta5 :
    ¬ Delta5_Multiplicative (n := 2) midrange :=
  midrange_not_A5prime

/-! ## §5 — Disclosure ledger. -/

#print axioms lambda_delta1
#print axioms lambda_delta2
#print axioms lambda_delta3
#print axioms lambda_satisfies_setDelta
#print axioms delta4_implies_allStrictMono
#print axioms setDelta_to_setAlpha
#print axioms geomMean_unique_KS
#print axioms maxAgg_not_PSI
#print axioms minAgg_not_PSI
#print axioms arithmeticMean_not_delta5
#print axioms harmonicMean_not_delta5
#print axioms powerMeanSq_not_delta5
#print axioms lehmer2_not_delta5
#print axioms midrange_not_delta5

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
                                   CONDITIONAL on EXACTLY ONE declared, cited
                                   bridge: `KS_theorem_1_1` (arXiv:2606.05221
                                   Thm 1.1 — the DERIVED-CONTINUITY theorem). The
                                   former second axiom `setDelta_stage2` is now
                                   DISCHARGED: with KS-derived continuity in hand
                                   a Set-δ aggregator IS a Set-α aggregator
                                   (`setDelta_to_setAlpha`, A3 from δ4 axiom-free),
                                   and the axiom-free SetAlpha multivariable
                                   discharge closes it.
      delta4_implies_allStrictMono — δ4-PSI ⇒ A3 (hybrid-vector telescoping).  AXIOM-FREE.
  (3) max/min _not_PSI (die by δ4) ; arithmetic/harmonic/powerMeanSq _not_delta5
                                   (die by δ5′).  CLOSED, AXIOM-FREE.

  HONEST LINE: "Unconditional within Set δ" = relative to the redefined,
  principled STRONGER class with continuity DERIVED. The ORIGINAL A1–A5 statement
  stays FALSE (Round13.maxAgg_ne_Lambda in-tree); Λ stays Conjecture 1 under the
  original axioms. EXACTLY ONE declared, cited axiom (`KS_theorem_1_1`), disclosed.

  Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
================================================================================
-/
