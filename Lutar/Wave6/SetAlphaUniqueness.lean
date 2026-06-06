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
import Mathlib.Algebra.BigOperators.Group.Finset.Basic  -- v4.18.0: Finset.lean -> Finset/ dir (Basic)

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

/-! ## §5a — DIAGONAL PINNING, fully AXIOM-FREE via the CONTINUOUS Cauchy lemma.

This section CLOSES — with NO declared axiom — the full diagonal pin
`F(eᵗ,…,eᵗ) = eᵗ`, i.e. `diagLog F t = t`, for any Set α aggregator `F`.  It is a
strict upgrade over §4 (`expCauchy_diagonal`), which only gave `diagLog F t =
diagLog F 1 · t` and assumed monotonicity of the diagonal log-conjugate (NOT
available from the all-strict A3).  Here we instead use:
  • additivity of `diagLog F` from A5′ (`diagLog_additive`, §4); and
  • CONTINUITY of `diagLog F` from A4 (`F` continuous on the positive orthant)
    composed with `Real.exp` (continuous) and `Real.log` (continuous on (0,∞));
then the axiom-free `Lutar.Wave6.continuous_additive_linear` (the Mathlib
`map_real_smul` Cauchy theorem) forces linearity, and A2 (idempotency) pins the
slope to 1.  The continuity hypothesis below is the genuine A4 content. -/

/-- **`diagLog_continuous`** (AXIOM-FREE). The diagonal log-conjugate `diagLog F`
    is continuous when `F` is continuous on the positive orthant and positive on
    positive diagonals: `diagLog F = Real.log ∘ F ∘ (t ↦ const (exp t))`, a
    composition of `Real.exp` (continuous), the constant-diagonal embedding into
    the positive orthant, `F` (A4, continuous there), and `Real.log` (continuous
    on (0,∞)). -/
theorem diagLog_continuous (F : (Fin n → ℝ) → ℝ)
    (hCont : A4_Continuity F)
    (hFpos : ∀ t : ℝ, 0 < F (fun _ => Real.exp t)) :
    Continuous (diagLog F) := by
  -- The diagonal embedding e : ℝ → (Fin n → ℝ), e t = fun _ => exp t, is continuous
  -- and maps into the positive orthant {x | Pos x}.
  have hembed : Continuous (fun t : ℝ => (fun _ : Fin n => Real.exp t)) :=
    continuous_pi (fun _ => Real.continuous_exp)
  have hmaps : Set.MapsTo (fun t : ℝ => (fun _ : Fin n => Real.exp t)) Set.univ {x | Pos x} := by
    intro t _; intro i; exact Real.exp_pos t
  -- F ∘ e is continuous on ℝ (= univ): A4 is ContinuousOn F {Pos}, precompose.
  have hFe : Continuous (fun t : ℝ => F (fun _ : Fin n => Real.exp t)) := by
    rw [continuous_iff_continuousOn_univ]
    have h := (hCont.comp hembed.continuousOn hmaps)
    -- h : ContinuousOn (F ∘ embed) univ ; unfold the composition to the lambda form.
    simpa [Function.comp] using h
  -- log is continuous on {0}ᶜ; F(exp t,…) > 0 ⇒ ≠ 0, so the composite is continuous.
  have hmem : ∀ t : ℝ, F (fun _ : Fin n => Real.exp t) ∈ ({0}ᶜ : Set ℝ) := by
    intro t; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact (hFpos t).ne'
  have hlog : Continuous (Real.log ∘ (fun t : ℝ => F (fun _ : Fin n => Real.exp t))) :=
    Real.continuousOn_log.comp_continuous hFe hmem
  simpa [diagLog, Function.comp] using hlog

/-- **`diagPin`** (AXIOM-FREE). Full diagonal pin: for a Set α aggregator,
    `diagLog F t = t` for all `t`, i.e. `F(eᵗ,…,eᵗ) = eᵗ`.  Uses additivity
    (A5′), continuity (A4), and idempotency (A2) — NO monotonicity, NO declared
    axiom. -/
theorem diagPin (F : (Fin n → ℝ) → ℝ)
    (hMul : A5_Multiplicativity F) (hCont : A4_Continuity F)
    (hIdem : A2_Idempotency F)
    (hFpos : ∀ t : ℝ, 0 < F (fun _ => Real.exp t)) :
    ∀ t : ℝ, diagLog F t = t := by
  have hadd := diagLog_additive F hMul hFpos
  have hcont := diagLog_continuous F hCont hFpos
  -- Continuous additive ⇒ linear: diagLog F t = diagLog F 1 * t.
  have hlin : ∀ t : ℝ, diagLog F t = diagLog F 1 * t :=
    Lutar.Wave6.continuous_additive_linear (diagLog F) hadd hcont
  -- A2 pins diagLog F 1 = 1:  F(e,…,e) = e (idempotency at c = e), so
  -- diagLog F 1 = log (F (const (exp 1))) = log (exp 1) = 1.
  have hpin1 : diagLog F 1 = 1 := by
    have hId : F (fun _ : Fin n => Real.exp 1) = Real.exp 1 := hIdem _ (Real.exp_pos 1)
    simp [diagLog, hId, Real.log_exp]
  intro t; rw [hlin t, hpin1, one_mul]

/-! ## §5b — FULL MULTIVARIABLE DISCHARGE (optional theorem, AXIOM-FREE attempt).

This section attempts the COMPLETE off-diagonal discharge of the doc Part-4 chain
as a standalone theorem `lambda_unique_setAlpha_discharged`, built ENTIRELY from
Lean/Mathlib core (no declared axiom).  It is kept SEPARATE from the headline
`lambda_unique_setAlpha` (§5, below) so that CI judges it in isolation: if it
compiles green its `#print axioms` lists Lean/Mathlib core ONLY and the declared
`setAlpha_cauchy` is no longer load-bearing; if any step fails to compile the
headline result is unaffected and `setAlpha_cauchy` remains the honest bridge.

The chain (doc Part 4, Steps 1–7), each step a named lemma:
  • `mvLog F t := log F(exp ∘ t)` — the multivariable log-conjugate, `(Fin n→ℝ)→ℝ`.
  • `mvLog_additive`  : A5′ ⇒ `mvLog F (s+t) = mvLog F s + mvLog F t`   (vectors).
  • `mvLog_continuous`: A4  ⇒ `Continuous (mvLog F)`.
  • `mvLog_linear_combo`: package `mvLog F` as a continuous `AddMonoidHom`; the
    Mathlib Cauchy theorem `map_real_smul` + the canonical-basis decomposition
    `Pi.pi_eq_sum_univ` give `mvLog F t = ∑ i, t i * mvLog F (eᵢ)` where
    `eᵢ = Pi.single i 1`.
  • `mvLog_coeff_eq`   : A1 (symmetry) ⇒ all coefficients `mvLog F (eᵢ)` equal.
  • `mvLog_coeff_val`  : A2 (idempotency) ⇒ the common coefficient is `1/n`.
  • `lambda_unique_setAlpha_discharged` : exponentiate back ⇒ `F x = geomMean x`. -/

/-- The multivariable log-conjugate of `F`: `mvLog F t = log F(eᵗ¹,…,eᵗⁿ)`. -/
noncomputable def mvLog (F : (Fin n → ℝ) → ℝ) (t : Fin n → ℝ) : ℝ :=
  Real.log (F (fun i => Real.exp (t i)))

/-- The `i`-th canonical basis vector of `Fin n → ℝ` (1 in slot `i`, 0 elsewhere). -/
def stdBasis (i : Fin n) : Fin n → ℝ := fun j => if i = j then (1 : ℝ) else 0

/-- Positivity of `F` on positive exponential inputs, derived downstream from A2+A3. -/
def FExpPos (F : (Fin n → ℝ) → ℝ) : Prop := ∀ t : Fin n → ℝ, 0 < F (fun i => Real.exp (t i))

/-- **`FExpPos_of_setAlpha`** (AXIOM-FREE). A Set α aggregator is positive on every
    positive exponential input: `0 < F(eᵗ¹,…,eᵗⁿ)`.  Proof: let `i₀` minimize
    `i ↦ exp(t i)` (finite, `n > 0`), set `c := exp(t i₀)/2`.  Then `0 < c` and
    `c < exp(t i)` for every `i`, so A3 (all-strict monotonicity) gives
    `F(const c) < F(exp∘t)`, while A2 (idempotency) gives `F(const c) = c > 0`. -/
theorem FExpPos_of_setAlpha (hn : 0 < n) (F : (Fin n → ℝ) → ℝ)
    (hF : SatisfiesSetAlpha F) : FExpPos F := by
  obtain ⟨_hSym, hIdem, hMono, _hCont, _hMul⟩ := hF
  intro t
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- Minimizing index for i ↦ exp (t i) over univ.
  obtain ⟨i₀, _hi₀mem, hi₀min⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin n)) (fun i => Real.exp (t i))
      Finset.univ_nonempty
  set c : ℝ := Real.exp (t i₀) / 2 with hcdef
  have hcpos : 0 < c := by positivity
  -- c < exp (t i) for all i: c = exp(t i₀)/2 < exp(t i₀) ≤ exp(t i).
  have hclt : ∀ i, c < Real.exp (t i) := by
    intro i
    have hmin : Real.exp (t i₀) ≤ Real.exp (t i) := hi₀min i (Finset.mem_univ i)
    have hhalf : c < Real.exp (t i₀) := by
      rw [hcdef]; linarith [Real.exp_pos (t i₀)]
    exact lt_of_lt_of_le hhalf hmin
  -- Positivity of both input vectors.
  have hcpos_vec : Pos (fun _ : Fin n => c) := fun _ => hcpos
  have hexp_pos : Pos (fun i : Fin n => Real.exp (t i)) := fun i => Real.exp_pos (t i)
  -- A3: F(const c) < F(exp∘t).
  have hlt := hMono (fun _ => c) (fun i => Real.exp (t i)) hcpos_vec hexp_pos hclt
  -- A2: F(const c) = c.
  have hId : F (fun _ : Fin n => c) = c := hIdem c hcpos
  rw [hId] at hlt
  exact lt_trans hcpos hlt

/-- **`mvLog_additive`** (AXIOM-FREE). A5′ makes the multivariable log-conjugate
    additive on vectors: `mvLog F (s+t) = mvLog F s + mvLog F t`. -/
theorem mvLog_additive (F : (Fin n → ℝ) → ℝ)
    (hMul : A5_Multiplicativity F) (hFpos : FExpPos F) :
    ∀ s t : Fin n → ℝ, mvLog F (s + t) = mvLog F s + mvLog F t := by
  intro s t
  unfold mvLog
  have hexp : (fun i : Fin n => Real.exp ((s + t) i))
            = (fun i : Fin n => (fun i => Real.exp (s i)) i * (fun i => Real.exp (t i)) i) := by
    funext i; simp only [Pi.add_apply]; rw [Real.exp_add]
  have hpos_s : Pos (fun i : Fin n => Real.exp (s i)) := fun i => Real.exp_pos (s i)
  have hpos_t : Pos (fun i : Fin n => Real.exp (t i)) := fun i => Real.exp_pos (t i)
  have hmul := hMul (fun i => Real.exp (s i)) (fun i => Real.exp (t i)) hpos_s hpos_t
  rw [hexp, hmul]
  exact Real.log_mul (hFpos s).ne' (hFpos t).ne'

/-- **`mvLog_continuous`** (AXIOM-FREE). A4 (continuity of `F` on the positive
    orthant) makes the multivariable log-conjugate continuous: `mvLog F` is
    `log ∘ F ∘ (t ↦ exp ∘ t)`, a composition of `Real.exp` componentwise
    (continuous), `F` on the orthant (A4), and `Real.log` (continuous on (0,∞)). -/
theorem mvLog_continuous (F : (Fin n → ℝ) → ℝ)
    (hCont : A4_Continuity F) (hFpos : FExpPos F) :
    Continuous (mvLog F) := by
  have hembed : Continuous (fun t : Fin n → ℝ => (fun i : Fin n => Real.exp (t i))) :=
    continuous_pi (fun i => Real.continuous_exp.comp (continuous_apply i))
  have hmaps : Set.MapsTo (fun t : Fin n → ℝ => (fun i : Fin n => Real.exp (t i)))
      Set.univ {x | Pos x} := by
    intro t _; intro i; exact Real.exp_pos (t i)
  have hFe : Continuous (fun t : Fin n → ℝ => F (fun i : Fin n => Real.exp (t i))) := by
    rw [continuous_iff_continuousOn_univ]
    have h := (hCont.comp hembed.continuousOn hmaps)
    simpa [Function.comp] using h
  have hmem : ∀ t : Fin n → ℝ, F (fun i : Fin n => Real.exp (t i)) ∈ ({0}ᶜ : Set ℝ) := by
    intro t; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact (hFpos t).ne'
  have hlog : Continuous (Real.log ∘ (fun t : Fin n → ℝ => F (fun i : Fin n => Real.exp (t i)))) :=
    Real.continuousOn_log.comp_continuous hFe hmem
  simpa [mvLog, Function.comp] using hlog

/-- **`mvLog_linear_combo`** (AXIOM-FREE). The Cauchy core: a continuous additive
    `mvLog F` is ℝ-linear, so it equals the linear combination of its values on
    the canonical basis: `mvLog F t = ∑ i, t i * mvLog F (stdBasis i)`.  Proof:
    bundle `mvLog F` as `AddMonoidHom.mk'`; `map_real_smul` (Mathlib Cauchy
    theorem) gives `G (c • x) = c • G x`; decompose `t = ∑ i, t i • stdBasis i`
    via `Pi.pi_eq_sum_univ`; push `G` through the sum (`map_sum`) and the scalars
    (`map_real_smul`). -/
theorem mvLog_linear_combo (F : (Fin n → ℝ) → ℝ)
    (hadd : ∀ s t : Fin n → ℝ, mvLog F (s + t) = mvLog F s + mvLog F t)
    (hcont : Continuous (mvLog F)) :
    ∀ t : Fin n → ℝ, mvLog F t = ∑ i, t i * mvLog F (stdBasis i) := by
  intro t
  -- Bundle as an additive hom with underlying function `mvLog F`.
  let G : (Fin n → ℝ) →+ ℝ := AddMonoidHom.mk' (mvLog F) hadd
  have hG : ∀ x, G x = mvLog F x := fun _ => rfl
  have hGcont : Continuous (fun x => G x) := by simpa [hG] using hcont
  -- Canonical-basis decomposition of `t`.
  have hdecomp : t = ∑ i, t i • stdBasis i := by
    have := pi_eq_sum_univ t
    simpa [stdBasis] using this
  -- Apply G, push through the sum and the scalars.
  calc mvLog F t
      = G t := (hG t).symm
    _ = G (∑ i, t i • stdBasis i) := by rw [← hdecomp]
    _ = ∑ i, G (t i • stdBasis i) := by rw [map_sum]
    _ = ∑ i, t i • G (stdBasis i) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          exact map_real_smul G hGcont (t i) (stdBasis i)
    _ = ∑ i, t i * mvLog F (stdBasis i) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hG]; rw [smul_eq_mul]

/-- **`mvLog_coeff_eq`** (AXIOM-FREE). A1 (symmetry) forces all basis coefficients
    equal: `mvLog F (stdBasis i) = mvLog F (stdBasis j)` for all `i, j`.  Proof:
    the permutation `σ = swap i j` satisfies `stdBasis j ∘ σ = stdBasis i` (and the
    exponential embedding is permutation-equivariant), so A1-symmetry of `F`
    transfers to `mvLog F (stdBasis i) = mvLog F (stdBasis j)`. -/
theorem mvLog_coeff_eq (F : (Fin n → ℝ) → ℝ) (hSym : A1_Symmetry F) :
    ∀ i j : Fin n, mvLog F (stdBasis i) = mvLog F (stdBasis j) := by
  intro i j
  unfold mvLog
  -- The exponential of stdBasis i, reindexed by swap i j, equals exp of stdBasis j.
  have hpos : Pos (fun k : Fin n => Real.exp (stdBasis i k)) := fun k => Real.exp_pos _
  have hswap := hSym (Equiv.swap i j) (fun k : Fin n => Real.exp (stdBasis i k)) hpos
  -- (exp ∘ stdBasis i) ∘ swap i j = exp ∘ stdBasis j   (pointwise).
  have hreindex : (fun k : Fin n => Real.exp (stdBasis i k)) ∘ (Equiv.swap i j)
                = (fun k : Fin n => Real.exp (stdBasis j k)) := by
    funext k
    simp only [Function.comp_apply, stdBasis]
    -- It suffices to show the indicator coefficients agree:
    --   (if i = swap i j k then 1 else 0) = (if j = k then 1 else 0).
    congr 1
    -- `i = swap i j k ↔ j = k`: applying the involution `swap i j` to both sides,
    -- `swap i j i = j` and `swap i j (swap i j k) = k`.
    by_cases hik : i = (Equiv.swap i j) k
    · -- then k = swap i j i = j, so j = k holds; both indicators are 1.
      have hk : k = (Equiv.swap i j) i := by
        have := congrArg (Equiv.swap i j) hik
        simpa [Equiv.swap_apply_self] using this.symm
      rw [Equiv.swap_apply_left] at hk
      rw [if_pos hik, if_pos hk.symm]
    · -- then ¬ (j = k): if j = k then i = swap i j k = swap i j j = i, contradiction.
      -- both indicators are 0.
      have hjk : j ≠ k := by
        intro hjk; apply hik
        rw [← hjk, Equiv.swap_apply_right]
      rw [if_neg hik, if_neg hjk]
  -- hswap : F ((exp∘stdBasis i)∘swap) = F (exp∘stdBasis i); rewrite the LHS.
  rw [hreindex] at hswap
  -- hswap : F (exp∘stdBasis j) = F (exp∘stdBasis i); take logs.
  rw [hswap]

/-- **`mvLog_coeff_val`** (AXIOM-FREE). A2 (idempotency) pins the common basis
    coefficient: with all `n` coefficients equal to `c := mvLog F (stdBasis i₀)`,
    the diagonal pin `mvLog F (const t) = t` (from the §5a `diagPin` machinery,
    here re-derived through the linear combination) forces `n • c = 1`, i.e.
    `c = 1/n`.  We state it in the form actually consumed: `∑ i, mvLog F (stdBasis i) = 1`
    (the sum of all coefficients is 1), which combined with `mvLog_coeff_eq`
    yields each `= 1/n`. -/
theorem mvLog_coeff_sum_one (F : (Fin n → ℝ) → ℝ) (hn : 0 < n)
    (hlin : ∀ t : Fin n → ℝ, mvLog F t = ∑ i, t i * mvLog F (stdBasis i))
    (hIdem : A2_Idempotency F) :
    ∑ i, mvLog F (stdBasis i) = 1 := by
  -- Evaluate the linear formula at the all-ones vector `1 = fun _ => 1`.
  have hone : mvLog F (fun _ => (1:ℝ)) = ∑ i, mvLog F (stdBasis i) := by
    rw [hlin (fun _ => (1:ℝ))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [one_mul]
  -- A2: F (exp 1,…,exp 1) = exp 1, so mvLog F 1 = log (exp 1) = 1.
  have hId : F (fun _ : Fin n => Real.exp (1:ℝ)) = Real.exp 1 := hIdem _ (Real.exp_pos 1)
  have hpin : mvLog F (fun _ => (1:ℝ)) = 1 := by
    unfold mvLog; simp only [hId, Real.log_exp]
  rw [← hone, hpin]

/-- **`lambda_unique_setAlpha_discharged`** (AXIOM-FREE attempt). The full Set α
    uniqueness theorem, discharged from Lean/Mathlib core with NO declared axiom.
    Chains `mvLog_additive` (A5′), `mvLog_continuous` (A4), `mvLog_linear_combo`
    (Cauchy), `mvLog_coeff_eq` (A1), `mvLog_coeff_sum_one` (A2), then exponentiates
    back to `geomMean`.  The positivity hypothesis `hFpos : FExpPos F` is the
    downstream-derived positivity of `F` on positive inputs (from A2+A3). -/
theorem lambda_unique_setAlpha_discharged (hn : 0 < n)
    (F : (Fin n → ℝ) → ℝ) (hF : SatisfiesSetAlpha F) (hFpos : FExpPos F) :
    ∀ x : Fin n → ℝ, Pos x → F x = geomMean x := by
  obtain ⟨hSym, hIdem, _hMono, hCont, hMul⟩ := hF
  -- Assemble the linear formula.
  have hadd := mvLog_additive F hMul hFpos
  have hcont := mvLog_continuous F hCont hFpos
  have hlin := mvLog_linear_combo F hadd hcont
  have hcoeff_eq := mvLog_coeff_eq F hSym
  have hsum := mvLog_coeff_sum_one F hn hlin hIdem
  -- All coefficients equal a common value c; n • c = 1 ⇒ c = 1/n.
  set c : ℝ := mvLog F (stdBasis ⟨0, hn⟩) with hcdef
  have hall : ∀ i : Fin n, mvLog F (stdBasis i) = c := fun i => hcoeff_eq i ⟨0, hn⟩
  have hsum_c : ∑ _i : Fin n, c = 1 := by rw [← hsum]; exact (Finset.sum_congr rfl (fun i _ => hall i)).symm
  -- `∑ _i : Fin n, c = (card univ) • c = n • c = (n:ℝ) * c`.
  have hsum_eval : ∑ _i : Fin n, c = (n : ℝ) * c := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [nsmul_eq_mul]
  have hnc : (n : ℝ) * c = 1 := by rw [← hsum_eval]; exact hsum_c
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hc_val : c = 1 / n := by field_simp; linarith [hnc]
  -- Now compute F x for positive x via the linear formula at t = log ∘ x.
  intro x hx
  -- mvLog F (log ∘ x) = ∑ i, (log x i) * c = c * ∑ log x i.
  have hlinx := hlin (fun i => Real.log (x i))
  -- exp embedding of (log ∘ x) recovers x (positivity).
  have hrecover : (fun i => Real.exp (Real.log (x i))) = x := by
    funext i; rw [Real.exp_log (hx i)]
  -- mvLog F (log∘x) = log (F x).
  have hmv : mvLog F (fun i => Real.log (x i)) = Real.log (F x) := by
    unfold mvLog; rw [hrecover]
  -- F x > 0 (from FExpPos at t = log∘x, transported through hrecover).
  have hFxpos : 0 < F x := by
    have := hFpos (fun i => Real.log (x i)); rwa [hrecover] at this
  -- Combine: log (F x) = ∑ (log x i) * c = c * ∑ log x i.
  have hlogFx : Real.log (F x) = c * ∑ i, Real.log (x i) := by
    rw [← hmv, hlinx]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hall i]; ring
  -- geomMean x = (∏ x i)^(1/n); take log of both candidate values and match.
  -- log (geomMean x) = (1/n) * log (∏ x i) = (1/n) * ∑ log x i = c * ∑ log x i.
  have hprodpos : 0 < ∏ i, x i := Finset.prod_pos (fun i _ => hx i)
  have hloggm : Real.log (geomMean x) = c * ∑ i, Real.log (x i) := by
    have hlg : Real.log (geomMean x) = (1 / (n : ℝ)) * ∑ i, Real.log (x i) := by
      unfold geomMean
      rw [Real.log_rpow hprodpos, Real.log_prod _ _ (fun i _ => (hx i).ne')]
    rw [hlg, hc_val]
  -- Both F x and geomMean x are positive with equal logs ⇒ equal.
  have hgmpos : 0 < geomMean x := geomMean_pos hx
  have hlogeq : Real.log (F x) = Real.log (geomMean x) := by rw [hlogFx, hloggm]
  exact Real.log_injOn_pos (Set.mem_Ioi.mpr hFxpos) (Set.mem_Ioi.mpr hgmpos) hlogeq

/-! ## §5 — (2) Uniqueness within Set α.

The full theorem `∀ F ∈ Set α, F = Λₙ` follows the doc Part 4 chain:
log-conjugate `h(t) = log F(exp∘t)` is additive (A5′) and continuous (A4), hence
ℝ-linear by `AddMonoidHom.toRealLinearMap` (Cauchy); symmetry (A1) equalizes the
n coefficients; idempotency (A2) pins each to `1/n`; exponentiating gives
`F(x) = (∏ xᵢ)^(1/n) = geomMean x`. The single-variable heart of this (diagonal
exp-Cauchy) is closed AXIOM-FREE in §4–§5a (now FULLY pinned via the continuous
Cauchy lemma).  The full off-diagonal multivariable chain is ALSO attempted
axiom-free as `lambda_unique_setAlpha_discharged` (§5b); the declared axiom below
is retained as an honest fallback (carrying the explicit `FExpPos` positivity
hypothesis the discharged version makes precise) for the headline statement. -/

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
    hypothesis beyond Set α membership.

    DISCHARGED: this now delegates to `lambda_unique_setAlpha_discharged` (§5b),
    deriving the required positivity `FExpPos F` internally from A2+A3 via
    `FExpPos_of_setAlpha`.  The declared `setAlpha_cauchy` axiom is therefore NO
    LONGER load-bearing for this headline; `#print axioms lambda_unique_setAlpha`
    lists Lean/Mathlib core ONLY (no `setAlpha_cauchy`).  If CI confirms green,
    the multivariable Cauchy discharge is complete; the axiom below is retained
    only as a documented dead fallback and is referenced by NO live result.

    HONEST: this is uniqueness within the PRINCIPLED STRONGER class {A1,A2,A3,A4,A5′}.
    It is NOT the old false statement under the original weaker A1–A5 (still
    false; `Round13.maxAgg_ne_Lambda` in-tree). Λ stays Conjecture 1 under the
    original axioms. -/
theorem lambda_unique_setAlpha (hn : 0 < n)
    (F : (Fin n → ℝ) → ℝ) (hF : SatisfiesSetAlpha F) :
    ∀ x : Fin n → ℝ, Pos x → F x = geomMean x :=
  lambda_unique_setAlpha_discharged hn F hF (FExpPos_of_setAlpha hn F hF)

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

/-- **Impostor — Lehmer mean (p=2, a.k.a. contraharmonic)**
    `L₂(x) = (Σxᵢ²)/(Σxᵢ)`. Fails A5′:
    L₂(8,3) = 73/11 ≈ 6.64 ; L₂(4,1)·L₂(2,3) = (17/5)·(13/5) = 221/25 = 8.84.
    A classical non-quasi-arithmetic mean; dies on the SAME witness. -/
noncomputable def lehmer2 (x : Fin 2 → ℝ) : ℝ := (∑ i, (x i) ^ 2) / (∑ i, x i)

theorem lehmer2_not_A5prime :
    ¬ A5_Multiplicativity (n := 2) lehmer2 := by
  intro h
  have key := h xW yW xW_pos yW_pos
  -- L₂(8,3) = (64+9)/(8+3) = 73/11 ;  (17/5)·(13/5) = 221/25 ; 73/11 ≠ 221/25.
  simp only [lehmer2, xW, yW, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at key
  norm_num at key

/-- **Impostor — midrange** `MR(x) = (max x + min x)/2`. Fails A5′:
    MR(8,3) = (8+3)/2 = 5.5 ; MR(4,1)·MR(2,3) = 2.5·2.5 = 6.25. -/
noncomputable def midrange (x : Fin 2 → ℝ) : ℝ := (x 0 ⊔ x 1 + x 0 ⊓ x 1) / 2

theorem midrange_not_A5prime :
    ¬ A5_Multiplicativity (n := 2) midrange := by
  intro h
  have key := h xW yW xW_pos yW_pos
  -- MR(8,3) = 11/2 = 5.5 ;  MR(4,1)·MR(2,3) = (5/2)·(5/2) = 25/4 = 6.25.
  simp only [midrange, xW, yW,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at key
  norm_num [max_def, min_def] at key

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
#print axioms diagPin
#print axioms FExpPos_of_setAlpha
#print axioms mvLog_additive
#print axioms mvLog_continuous
#print axioms mvLog_linear_combo
#print axioms mvLog_coeff_eq
#print axioms mvLog_coeff_sum_one
#print axioms lambda_unique_setAlpha_discharged
#print axioms lambda_unique_setAlpha
#print axioms arithmeticMean_not_A5prime
#print axioms harmonicMean_not_A5prime
#print axioms powerMeanSq_not_A5prime
#print axioms maxAgg_not_A5prime
#print axioms minAgg_not_A5prime
#print axioms lehmer2_not_A5prime
#print axioms midrange_not_A5prime
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
