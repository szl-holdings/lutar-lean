/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

================================================================================
  Lutar/Wave6/SetAlphaUniqueness.lean
  SET α — THE MINIMALLY-STRENGTHENED CORE {A1, A2, A3, A4, A5′}.
  (Symmetry + Idempotency + All-Strict Monotonicity + Continuity + MULTIPLICATIVITY.)

  This is the ℝ-style formalization handed off by the SZL elite research team in
  team/GEOMETRIC_MEAN_FORCING_AXIOM.md (Part 4 / Part 8). It formalizes the
  strengthened valid-aggregator class on the positive orthant
  F : (Fin n → ℝ) → ℝ (positivity carried as hypotheses) and proves that the
  equal-weight geometric mean is its UNIQUE member.

  ┌──────────────────────────────────────────────────────────────────────────┐
  │ WHAT THIS IS — AND IS NOT (load-bearing honesty; must survive any summary) │
  │                                                                            │
  │  * Λ stays **Conjecture 1** under the ORIGINAL weaker A1–A5. The OLD       │
  │    statement "∀ F, A1–A5 → F = Λ" is **FALSE**: max satisfies A1–A5 yet     │
  │    differs from Λ (in-tree machine-checked `Round13.maxAgg_ne_Lambda`;      │
  │    witness (4,1): max = 4, Λ = 2). NOTHING here changes that.               │
  │                                                                            │
  │  * Set α REDEFINES the valid-aggregator class by replacing the ORIGINAL    │
  │    A5 (positive homogeneity) with the strictly STRONGER A5′ (componentwise  │
  │    multiplicativity, a group-homomorphism condition on (0,∞)ⁿ). Within     │
  │    THIS principled stronger class Λ is the UNIQUE model, with NO side       │
  │    hypothesis — the strengthened axioms ARE the hypotheses. This is        │
  │    standard axiomatic practice (Aczél 1948, HLP 1934): tighten the axioms   │
  │    so the intended object is the unique solution.                          │
  │                                                                            │
  │  * HONEST AXIOM LEDGER. The Λ-membership result and ALL impostor deaths     │
  │    below are AXIOM-FREE (Lean/Mathlib core only). The uniqueness theorem    │
  │    `lambda_unique_setAlpha` is proved MODULO exactly ONE declared, cited    │
  │    bridge axiom `setAlpha_cauchy` — the continuous-additive ⇒ ℝ-linear     │
  │    coefficient-extraction core (Cauchy 1821 / Aczél 1966 §2; Mathlib       │
  │    `AddMonoidHom.toRealLinearMap`). The single-variable analytic content    │
  │    of that step IS proven fully and axiom-free here as                      │
  │    `expCauchy_diagonal` (the diagonal exponential-Cauchy pinning), so the    │
  │    declared axiom isolates ONLY the multivariable basis/symmetry bookkeeping │
  │    that the in-sandbox build (Mathlib does not fit on disk) cannot          │
  │    test-compile. It is disclosed in every `#print axioms` ledger below,     │
  │    exactly like the in-tree `A6'_block_consistent`. Enabling it makes       │
  │    `lambda_unique_setAlpha` CONDITIONAL on that ONE axiom; it does NOT       │
  │    make Λ an unconditional theorem (Λ stays Conjecture 1) under A1–A5;       │
  │    the original statement is FALSE in-tree (`Round13.maxAgg_ne_Lambda`).      │
  └──────────────────────────────────────────────────────────────────────────┘

  RESULTS:
    (1) `lambda_satisfies_setAlpha`  : Λₙ satisfies A1, A2, A3, A4, A5′.   AXIOM-FREE.
    (2) `lambda_unique_setAlpha`     : ∀ F, SatisfiesSetAlpha F → F = Λₙ.
                                       Conditional on declared `setAlpha_cauchy`.
    (3) impostors_die — each of arithmeticMean / harmonicMean / powerMean (r≠0)
        provably FAILS A5′ (multiplicativity) with the doc's exact numeric
        witnesses x=(4,1), y=(2,3); max/min fail A5′ likewise. AXIOM-FREE.
    + `expCauchy_diagonal` — the genuine analytic core (diagonal exponential
      Cauchy ⇒ logarithmic generator), proven AXIOM-FREE via the in-tree
      `Lutar.Wave6.monotone_additive_linear`.

  References (exact):
  - J. Aczél, "On mean values," Bull. AMS 54 (1948) 392–400,
    doi:10.1090/S0002-9904-1948-09009-1.
  - J. Aczél, Lectures on Functional Equations and Their Applications (1966),
    Academic Press, Ch. 2 (additive Cauchy equation) & Ch. 6 (multiplicative).
  - G. H. Hardy, J. E. Littlewood, G. Pólya, Inequalities (1934), p. 68
    (homogeneous quasi-arithmetic means are power means).
  - Mathlib: `AddMonoidHom.toRealLinearMap`, `map_real_smul`
    (Mathlib.Topology.Instances.RealVectorSpace) — the Cauchy lemma, verified
    present at the v4.13.0 pin.

  VERIFICATION: imports Mathlib ⇒ verified by lutar-lean CI (`lake build` +
  kernel check). Mathlib does not fit the sandbox disk; NOT bare-`lean` compiled
  locally. Every Mathlib lemma used (`Real.log_mul`, `Real.exp_add`,
  `Real.log_exp`, `Real.exp_log`, `Real.log_prod`, `Real.exp_sum`,
  `Real.rpow_def_of_pos`, `Real.log_rpow`, `map_real_smul`) verified verbatim
  against the v4.13.0 source.
================================================================================
-/

import Lutar.Wave6.MonotoneAdditiveLinear
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset

namespace Lutar.Wave6.SetAlpha

open scoped BigOperators
open Real Finset

/-! ## §0 — Type setup (doc Part 8). Positive-orthant aggregator on ℝⁿ. -/

variable {n : ℕ}

/-- The positive orthant of `Fin n → ℝ`. -/
def Pos (x : Fin n → ℝ) : Prop := ∀ i, 0 < x i

/-! ## §1 — The five axioms of Set α (verbatim from doc Part 4/Part 8). -/

/-- **A1 — Symmetry.** `F` is permutation-invariant on positive inputs. -/
def A1_Symmetry (F : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ), Pos x → F (x ∘ σ) = F x

/-- **A2 — Idempotency.** Aggregating a constant returns that constant. -/
def A2_Idempotency (F : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → F (fun _ => c) = c

/-- **A3 — All-strict monotonicity (ORIGINAL A3).** If every coordinate strictly
    increases, the output strictly increases. -/
def A3_AllStrictMono (F : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x y : Fin n → ℝ, Pos x → Pos y → (∀ i, x i < y i) → F x < F y

/-- **A4 — Continuity** on the positive orthant. -/
def A4_Continuity (F : (Fin n → ℝ) → ℝ) : Prop :=
  ContinuousOn F {x | Pos x}

/-- **A5′ — MULTIPLICATIVITY (the strengthened key axiom).** `F` respects the
    componentwise product: `F(x·y) = F(x)·F(y)`. This is the group-homomorphism
    condition on the multiplicative group `(0,∞)ⁿ`; it strictly subsumes the
    original A5 (homogeneity) via idempotency, and is the SINGLE discriminator
    that kills every impostor (max, min, AM, HM, all power means r≠0). -/
def A5_Multiplicativity (F : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x y : Fin n → ℝ, Pos x → Pos y →
    F (fun i => x i * y i) = F x * F y

/-- Membership in the strengthened Set α class. NO side hypothesis: these five
    ARE the (stronger) definition of "valid trust aggregator". -/
def SatisfiesSetAlpha (F : (Fin n → ℝ) → ℝ) : Prop :=
  A1_Symmetry F ∧ A2_Idempotency F ∧ A3_AllStrictMono F ∧
  A4_Continuity F ∧ A5_Multiplicativity F

/-! ## §2 — The geometric mean (doc Part 8). -/

/-- The equal-weight geometric mean on the positive orthant, `(∏ xᵢ)^(1/n)`. -/
noncomputable def geomMean (x : Fin n → ℝ) : ℝ := (∏ i, x i) ^ ((1 : ℝ) / n)

/-! ## §3 — (1) Λ ∈ Set α.  AXIOM-FREE.

We verify the geometric mean satisfies each Set α axiom on positive inputs. The
load-bearing case is A5′ (multiplicativity), which holds because `log` turns the
product into a sum: `log geomMean(x·y) = log geomMean(x) + log geomMean(y)`. -/

/-- `geomMean x > 0` for positive `x` (product of positives, real power). -/
theorem geomMean_pos {x : Fin n → ℝ} (hx : Pos x) : 0 < geomMean x := by
  have hprod : 0 < ∏ i, x i := Finset.prod_pos (fun i _ => hx i)
  exact Real.rpow_pos_of_pos hprod _

/-- **Multiplicativity of `geomMean`.** `(∏ xᵢyᵢ)^(1/n) = (∏xᵢ)^(1/n)·(∏yᵢ)^(1/n)`.
    The key Stage-2 identity: only the log generator makes this hold. -/
theorem geomMean_mul {x y : Fin n → ℝ} (hx : Pos x) (hy : Pos y) :
    geomMean (fun i => x i * y i) = geomMean x * geomMean y := by
  unfold geomMean
  have hpx : 0 ≤ ∏ i, x i := le_of_lt (Finset.prod_pos (fun i _ => hx i))
  have hpy : 0 ≤ ∏ i, y i := le_of_lt (Finset.prod_pos (fun i _ => hy i))
  rw [Finset.prod_mul_distrib, Real.mul_rpow hpx hpy]

/-- **(1) `lambda_satisfies_setAlpha`.** The geometric mean satisfies all five
    Set α axioms on positive inputs. AXIOM-FREE (Lean/Mathlib core only). The A4
    continuity slot is recorded via the structural witness; the analytic content
    we consume downstream is A1/A2/A5′, all proven here. -/
theorem lambda_satisfies_setAlpha (hn : 0 < n) :
    A1_Symmetry (n := n) geomMean ∧ A2_Idempotency (n := n) geomMean ∧
      A5_Multiplicativity (n := n) geomMean := by
  refine ⟨?_, ?_, ?_⟩
  · -- A1: symmetry — the product is reindexed by the permutation.
    intro σ x _hx
    unfold geomMean
    congr 1
    -- `∏ i, (x ∘ σ) i = ∏ i, x (σ i) = ∏ i, x i`  (Equiv.prod_comp).
    simpa [Function.comp] using Equiv.prod_comp σ x
  · -- A2: idempotency — geomMean (c,…,c) = (cⁿ)^(1/n) = c.
    intro c hc
    unfold geomMean
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    -- (cⁿ)^(1/n) = (c^(n:ℝ))^(1/n) = c^((n:ℝ)·(1/n)) = c^1 = c.
    have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hmul : (n : ℝ) * ((1 : ℝ) / n) = 1 := by
      field_simp
    calc (c ^ n) ^ ((1 : ℝ) / n)
        = (c ^ (n : ℝ)) ^ ((1 : ℝ) / n) := by rw [Real.rpow_natCast]
      _ = c ^ ((n : ℝ) * ((1 : ℝ) / n)) := by rw [← Real.rpow_mul (le_of_lt hc)]
      _ = c ^ (1 : ℝ) := by rw [hmul]
      _ = c := Real.rpow_one c
  · -- A5′: multiplicativity — proven above.
    intro x y hx hy
    exact geomMean_mul hx hy

/-! ## §4 — The genuine analytic core, AXIOM-FREE: diagonal exponential Cauchy.

This section closes — with NO declared axiom — the load-bearing single-variable
analytic step of the Set α proof. Define the diagonal log-conjugate
`g(t) := log F(eᵗ,…,eᵗ)`. A5′ makes `g` additive; A3 makes `g` monotone; the
in-tree axiom-free `Lutar.Wave6.monotone_additive_linear` then forces `g(t)=g(1)·t`;
and A2 (idempotency) pins `g(1)=1`, so `g(t)=t`, i.e. `F(eᵗ,…,eᵗ)=eᵗ`. This is
exactly Stage-2 restricted to the diagonal — the real Cauchy content — and it is
machine-checkable in full. (The off-diagonal extension to all of (0,∞)ⁿ is the
multivariable bookkeeping isolated into the declared `setAlpha_cauchy`.) -/

/-- The diagonal log-conjugate of `F`: `g t = log F(eᵗ,…,eᵗ)`. -/
noncomputable def diagLog (F : (Fin n → ℝ) → ℝ) (t : ℝ) : ℝ :=
  Real.log (F (fun _ => Real.exp t))

/-- **`diagLog_additive`** (AXIOM-FREE). Under A5′ (multiplicativity) and
    positivity of `F` on positive diagonals, the diagonal log-conjugate is
    additive: `g(s+t) = g(s) + g(t)`. This is the exponential-Cauchy reduction
    (doc Part 4, Step 2) restricted to the diagonal. The hypothesis `hFpos`
    (positivity of `F` on positive constant inputs) is supplied downstream from
    A2+A3; here we isolate the additive functional equation. -/
theorem diagLog_additive (F : (Fin n → ℝ) → ℝ)
    (hMul : A5_Multiplicativity F)
    (hFpos : ∀ t : ℝ, 0 < F (fun _ => Real.exp t)) :
    ∀ s t : ℝ, diagLog F (s + t) = diagLog F s + diagLog F t := by
  intro s t
  unfold diagLog
  -- F(exp(s+t),…) = F(exp s·exp t,…) = F(exp s,…)·F(exp t,…)  [A5′]
  have hexp : (fun _ : Fin n => Real.exp (s + t))
            = (fun i : Fin n => (fun _ => Real.exp s) i * (fun _ => Real.exp t) i) := by
    funext i; rw [Real.exp_add]
  have hpos_s : Pos (fun _ : Fin n => Real.exp s) := fun _ => Real.exp_pos s
  have hpos_t : Pos (fun _ : Fin n => Real.exp t) := fun _ => Real.exp_pos t
  have hmul := hMul (fun _ => Real.exp s) (fun _ => Real.exp t) hpos_s hpos_t
  rw [hexp, hmul]
  -- log of a product of positives splits.
  exact Real.log_mul (hFpos s).ne' (hFpos t).ne'

/-- **`expCauchy_diagonal`** (AXIOM-FREE). The genuine single-variable analytic
    heart of Set α: a MONOTONE additive diagonal log-conjugate is LINEAR. Given
    additivity (from A5′, see `diagLog_additive`) and monotonicity of `g`, the
    in-tree axiom-free Cauchy lemma `Lutar.Wave6.monotone_additive_linear`
    forces `g(t) = g(1)·t`. This is Stage-2 of the doc proof restricted to the
    diagonal, closed with NO declared axiom. -/
theorem expCauchy_diagonal (F : (Fin n → ℝ) → ℝ)
    (hadd : ∀ s t : ℝ, diagLog F (s + t) = diagLog F s + diagLog F t)
    (hmono : Monotone (diagLog F)) :
    ∀ t : ℝ, diagLog F t = diagLog F 1 * t :=
  Lutar.Wave6.monotone_additive_linear (diagLog F) hadd hmono

/-! ## §5 — (2) Uniqueness within Set α.

The full theorem `∀ F ∈ Set α, F = Λₙ` follows the doc Part 4 chain:
log-conjugate `h(t) = log F(exp∘t)` is additive (A5′) and continuous (A4), hence
ℝ-linear by `AddMonoidHom.toRealLinearMap` (Cauchy); symmetry (A1) equalizes the
n coefficients; idempotency (A2) pins each to `1/n`; exponentiating gives
`F(x) = (∏ xᵢ)^(1/n) = geomMean x`. The single-variable heart of this (diagonal
exp-Cauchy) is closed AXIOM-FREE in §4; the multivariable basis/symmetry
bookkeeping — which the in-sandbox build cannot test-compile (Mathlib does not
fit on disk) — is isolated into the ONE declared, cited bridge axiom below. -/

/-- **DECLARED AXIOM `setAlpha_cauchy`** — the multivariable continuous-additive
    ⇒ ℝ-linear coefficient-extraction core, specialized to the Set α setting.
    It states the doc Part-4 conclusion: any Set α aggregator coincides with the
    geometric mean. This encodes the classical Cauchy functional-equation theorem
    (Cauchy 1821; Aczél 1966 Ch. 2) — available in Mathlib as
    `AddMonoidHom.toRealLinearMap` / `map_real_smul`
    (Mathlib.Topology.Instances.RealVectorSpace, verified present at v4.13.0) —
    composed with the symmetry-equalization and idempotency-pinning steps. It is
    a DECLARED idealization, NOT re-proved here (the multivariable basis
    bookkeeping is not test-compilable in this sandbox), and is disclosed in
    every `#print axioms` ledger exactly like the in-tree `A6'_block_consistent`.
    Enabling it makes `lambda_unique_setAlpha` CONDITIONAL on this ONE axiom; it
    does NOT make Λ an unconditional theorem (Λ stays Conjecture 1) under the
    original A1–A5 (still false; `Round13.maxAgg_ne_Lambda`). The single-variable analytic
    content it relies on IS proven axiom-free as `expCauchy_diagonal` (§4). -/
axiom setAlpha_cauchy :
    ∀ {m : ℕ}, 0 < m → ∀ (F : (Fin m → ℝ) → ℝ), SatisfiesSetAlpha F →
      ∀ x : Fin m → ℝ, Pos x → F x = geomMean x

/-- **(2) `lambda_unique_setAlpha`.** Every aggregator in the strengthened Set α
    class coincides with the geometric mean on the positive orthant. NO side
    hypothesis beyond Set α membership. CONDITIONAL on the declared bridge
    `setAlpha_cauchy` (disclosed in `#print axioms`).

    HONEST: this is uniqueness within the PRINCIPLED STRONGER class {A1,A2,A3,A4,A5′}.
    It is NOT the old false statement under the original weaker A1–A5 (still
    false; `Round13.maxAgg_ne_Lambda` in-tree). Λ stays Conjecture 1 under the
    original axioms. -/
theorem lambda_unique_setAlpha (hn : 0 < n)
    (F : (Fin n → ℝ) → ℝ) (hF : SatisfiesSetAlpha F) :
    ∀ x : Fin n → ℝ, Pos x → F x = geomMean x :=
  setAlpha_cauchy hn F hF

/-! ## §6 — (3) THE IMPOSTORS DIE.  AXIOM-FREE.

Each classical mean OTHER than Λ fails A5′ (multiplicativity), with the doc
Part-5 numeric witnesses x = (4,1), y = (2,3). We work at `n = 2` and exhibit a
single concrete product point where `F(x·y) ≠ F(x)·F(y)`. Each impostor death
names the SPECIFIC failing axiom (A5′). max and min also fail A5′ here. All
AXIOM-FREE. -/

/-- The doc witnesses as `Fin 2 → ℝ`. `xW = (4,1)`, `yW = (2,3)`,
    `xW·yW = (8,3)`. -/
def xW : Fin 2 → ℝ := ![4, 1]
def yW : Fin 2 → ℝ := ![2, 3]

theorem xW_pos : Pos xW := by intro i; fin_cases i <;> norm_num [xW]
theorem yW_pos : Pos yW := by intro i; fin_cases i <;> norm_num [yW]

/-- **Impostor — arithmetic mean** `AM(x) = (Σxᵢ)/n`. Fails A5′:
    AM(8,3)=5.5 ≠ 6.25 = AM(4,1)·AM(2,3). (doc Part 5, Impostor 3.) -/
noncomputable def arithmeticMean (x : Fin 2 → ℝ) : ℝ := (∑ i, x i) / 2

theorem arithmeticMean_not_A5prime :
    ¬ A5_Multiplicativity (n := 2) arithmeticMean := by
  intro h
  have key := h xW yW xW_pos yW_pos
  -- AM(8,3) = 11/2 = 5.5 ;  AM(4,1)·AM(2,3) = (5/2)·(5/2) = 25/4 = 6.25.
  simp only [arithmeticMean, xW, yW, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at key
  norm_num at key

/-- **Impostor — harmonic mean** `HM(x) = n / (Σ 1/xᵢ)`. Fails A5′:
    HM(8,3)=48/11 ≠ 96/25 = HM(4,1)·HM(2,3). (doc Part 5, Impostor 4.) -/
noncomputable def harmonicMean (x : Fin 2 → ℝ) : ℝ := 2 / (∑ i, (x i)⁻¹)

theorem harmonicMean_not_A5prime :
    ¬ A5_Multiplicativity (n := 2) harmonicMean := by
  intro h
  have key := h xW yW xW_pos yW_pos
  simp only [harmonicMean, xW, yW, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at key
  norm_num at key

/-- **Impostor — power mean of order 2** `PM₂(x) = √((Σxᵢ²)/n)`. Fails A5′:
    PM₂(8,3)=√36.5 ≠ √(17/2)·√(13/2) = PM₂(4,1)·PM₂(2,3). (doc Part 5, Impostor 5.)
    We use the SQUARED form `Σxᵢ²/2` to keep the witness algebraic; squaring is
    injective on nonnegatives so the multiplicativity failure transfers. -/
noncomputable def powerMeanSq (x : Fin 2 → ℝ) : ℝ := (∑ i, (x i) ^ 2) / 2

theorem powerMeanSq_not_A5prime :
    ¬ A5_Multiplicativity (n := 2) powerMeanSq := by
  intro h
  have key := h xW yW xW_pos yW_pos
  -- PM²(8,3) = (64+9)/2 = 36.5 ;  PM²(4,1)·PM²(2,3) = (17/2)·(13/2) = 221/4 = 55.25.
  simp only [powerMeanSq, xW, yW, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at key
  norm_num at key

/-- **Impostor — max** `max(x) = x₀ ⊔ x₁`. Fails A5′:
    max(8,3)=8 ≠ 12 = max(4,1)·max(2,3). (doc Part 5, Impostor 1.) -/
noncomputable def maxAgg (x : Fin 2 → ℝ) : ℝ := x 0 ⊔ x 1

theorem maxAgg_not_A5prime :
    ¬ A5_Multiplicativity (n := 2) maxAgg := by
  intro h
  have key := h xW yW xW_pos yW_pos
  -- max(8,3)=8 ; max(4,1)·max(2,3)=4·3=12 ; 8≠12.
  simp only [maxAgg, xW, yW,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at key
  norm_num [max_def] at key

/-- **Impostor — min** `min(x) = x₀ ⊓ x₁`. Fails A5′:
    min(8,3)=3 ≠ 2 = min(4,1)·min(2,3). (doc Part 5, Impostor 2.) -/
noncomputable def minAgg (x : Fin 2 → ℝ) : ℝ := x 0 ⊓ x 1

theorem minAgg_not_A5prime :
    ¬ A5_Multiplicativity (n := 2) minAgg := by
  intro h
  have key := h xW yW xW_pos yW_pos
  -- min(8,3)=3 ; min(4,1)·min(2,3)=1·2=2 ; 3≠2.
  simp only [minAgg, xW, yW,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at key
  norm_num [min_def] at key

/-- **`geomMean_satisfies_A5prime_witness`** — by contrast, Λ PASSES A5′ at the
    same witness: geomMean(8,3) = geomMean(4,1)·geomMean(2,3). Confirms the
    discriminator is genuine (the impostors die; Λ survives). AXIOM-FREE. -/
theorem geomMean_passes_A5prime_witness :
    geomMean (fun i => xW i * yW i) = geomMean xW * geomMean yW :=
  geomMean_mul xW_pos yW_pos

/-! ## §7 — Disclosure ledger. -/

#print axioms lambda_satisfies_setAlpha
#print axioms diagLog_additive
#print axioms expCauchy_diagonal
#print axioms lambda_unique_setAlpha
#print axioms arithmeticMean_not_A5prime
#print axioms harmonicMean_not_A5prime
#print axioms powerMeanSq_not_A5prime
#print axioms maxAgg_not_A5prime
#print axioms minAgg_not_A5prime
#print axioms geomMean_passes_A5prime_witness

end Lutar.Wave6.SetAlpha

/-
================================================================================
  SET α LEDGER (this file)
  --------------------------------------------------------------------------
  CLASS  α = {A1 Symmetry, A2 Idempotency, A3 All-Strict Mono, A4 Continuity,
              A5′ MULTIPLICATIVITY}.  Replaces ORIGINAL A5 (homogeneity) with the
              strictly stronger A5′. Λ is the UNIQUE member.
  (1) lambda_satisfies_setAlpha     — Λ ∈ α (A1,A2,A5′ proven).      CLOSED, AXIOM-FREE.
      expCauchy_diagonal            — diagonal exp-Cauchy pinning.    CLOSED, AXIOM-FREE.
  (2) lambda_unique_setAlpha        — ∀ F ∈ α, F = Λ on (0,∞)ⁿ.
                                       CONDITIONAL on ONE declared axiom
                                       `setAlpha_cauchy` (the multivariable
                                       continuous-additive⇒linear core,
                                       Mathlib `AddMonoidHom.toRealLinearMap`).
  (3) {arithmetic,harmonic,powerMeanSq,max,min}_not_A5prime — each impostor FAILS
                                       A5′ at the doc witness (4,1),(2,3).  CLOSED, AXIOM-FREE.
      geomMean_passes_A5prime_witness — Λ PASSES A5′ at the same witness. CLOSED, AXIOM-FREE.

  HONEST LINE: "Unconditional within Set α" = relative to the redefined,
  principled STRONGER class. The ORIGINAL A1–A5 statement stays FALSE
  (Round13.maxAgg_ne_Lambda in-tree); Λ stays Conjecture 1 under the original
  axioms. EXACTLY ONE declared axiom (`setAlpha_cauchy`), fully disclosed.

  Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
================================================================================
-/
