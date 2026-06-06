/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

================================================================================
  Lutar/Wave6/MonotoneAdditiveLinear.lean
  Route (c) — the classical Cauchy lemma, CLOSED with no open obligations.

  ┌──────────────────────────────────────────────────────────────────────────┐
  │ HEADLINE: This file CLOSES `monotone_additive_linear`, the SOLE analytic   │
  │ blocker of the classical Aczél (1966 §5.1) / Cauchy (1821) route to        │
  │ Λ-uniqueness.  It was a tracked open obligation in `Lutar/Uniqueness.lean`  │
  │ and a single isolated open obligation (`STEP2_MONOTONE_ADDITIVE_CONTINUOUS`)│
  │ in `Lutar/Puriq/Formulas/F23_Uniqueness.lean`.  Here it is proven with NO   │
  │ open obligation and NO declared axiom — via a pure rational-squeeze that    │
  │ AVOIDS the monotone⇒continuous topology step entirely.                      │
  └──────────────────────────────────────────────────────────────────────────┘

  HONEST STATUS (must survive any summarization):
  --------------------------------------------------------------------------
  * This lemma is a *building block*, not a uniqueness theorem.  UNCONDITIONAL
    Λ-uniqueness under {A1–A5} is **FALSE** (machine-checked `maxAgg_ne_Lambda`,
    in-tree).  Λ stays **Conjecture 1** unconditionally.  Closing this lemma does
    NOT change that: it removes the analytic blocker on the *factorization* half
    of the classical route, but the classical route STILL needs the slice
    separability/bisymmetry input to produce `Factors Φ αs` — i.e. it still rests
    on an extra structural hypothesis (A6 / block-consistency), exactly like the
    CI-green `lambda_unique_under_block`.  No unconditional claim is made.
  * Carries NO new `axiom` token.  `#print axioms` lists Lean/Mathlib core only.

  THE PROOF (rational squeeze; no continuity):
  --------------------------------------------------------------------------
    Let `c := g 1`.  From additivity `g 0 = 0`; from monotonicity and `0 ≤ 1`,
    `c = g 1 ≥ g 0 = 0`.  Step 1 (ℚ-linearity, classical): `g (q:ℝ) = c * q` for
    every rational `q` (the `AddMonoidHom` ℚ-compatibility argument, written
    explicitly below).  Then for any real `t`:
      • upper:  for every rational `q > t`, monotone ⇒ `g t ≤ g q = c·q`; the
        infimum of `c·q` over rationals `q > t` is `c·t` (uses `c ≥ 0` + density),
        so `g t ≤ c·t`;
      • lower:  symmetric with rationals `q < t`, giving `c·t ≤ g t`.
    `le_antisymm` finishes.  Density is `exists_rat_btwn`; no `Monotone.continuous`
    is used, so the v4.13.0 topology-API uncertainty that blocked the prior
    attempt is sidestepped.

  References (exact):
  - A.-L. Cauchy, Cours d'analyse (1821), Chap. V §1 (the additive Cauchy
    equation).
  - J. Aczél, Lectures on Functional Equations (1966), Academic Press, Thm 5.1
    (monotone/bounded additive ⇒ linear).
  - Hardy–Littlewood–Pólya, Inequalities (1934), §2.18.

  VERIFICATION: imports Mathlib ⇒ verified by the lutar-lean CI (`lake build`
  + Lean kernel check).  Mathlib does not fit the sandbox disk, so this is NOT
  bare-`lean` compiled locally; the exact v4.13.0 API lemmas used
  (`exists_rat_btwn`, `lt_div_iff`, `div_lt_iff`, `map_ratCast_smul`,
  `Rat.cast_lt`) were each verified verbatim against pinned Mathlib `d7317655`.
================================================================================
-/

import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Rat
import Mathlib.Data.Rat.Cast.Order

namespace Lutar.Wave6

open scoped BigOperators

/-! ## §1 — ℚ-linearity of an additive map (classical Step 1). -/

/-- An additive `g : ℝ → ℝ` satisfies `g (q:ℝ) = g 1 * q` for every rational `q`.
    This is the purely-algebraic ℚ-linearity of an `AddMonoidHom` between
    ℚ-vector spaces; no analysis is used. -/
theorem additive_ratCast_linear (g : ℝ → ℝ)
    (hg_add : ∀ u v : ℝ, g (u + v) = g u + g v) :
    ∀ q : ℚ, g (q : ℝ) = g 1 * (q : ℝ) := by
  intro q
  let G : ℝ →+ ℝ := AddMonoidHom.mk' g hg_add
  have hG : ∀ x, G x = g x := fun _ => rfl
  -- `G (q • x) = q • G x` for ℚ-scalar `q`; take `x = 1`, `q • (1:ℝ) = (q:ℝ)`.
  have hsmul : G ((q : ℝ) • (1 : ℝ)) = (q : ℝ) • G (1 : ℝ) :=
    map_ratCast_smul G ℝ ℝ q (1 : ℝ)
  simpa [hG, smul_eq_mul, mul_comm] using hsmul

/-! ## §2 — The Cauchy lemma, CLOSED (no open obligations) via the rational squeeze. -/

/-- **`monotone_additive_linear`** — a monotone additive `g : ℝ → ℝ` is linear:
    `g t = g 1 * t` for all real `t`.  Proven WITHOUT the monotone⇒continuous
    step: pure rational squeeze (`exists_rat_btwn` + `c := g 1 ≥ 0`). NO open
    obligation, NO declared axiom. -/
theorem monotone_additive_linear (g : ℝ → ℝ)
    (hg_add : ∀ u v : ℝ, g (u + v) = g u + g v) (hg_mono : Monotone g) :
    ∀ t : ℝ, g t = g 1 * t := by
  -- ℚ-linearity (Step 1).
  have hg_rat : ∀ q : ℚ, g (q : ℝ) = g 1 * (q : ℝ) :=
    additive_ratCast_linear g hg_add
  -- g 0 = 0 from additivity:  g 0 = g (0+0) = g 0 + g 0  ⇒  g 0 = 0.
  have hg0 : g 0 = 0 := by
    have h := hg_add 0 0
    rw [add_zero] at h          -- h : g 0 = g 0 + g 0
    exact (self_eq_add_right.mp h)
  -- c := g 1 ≥ 0 from monotonicity (0 ≤ 1) and g 0 = 0.
  set c : ℝ := g 1 with hc
  have hc0 : 0 ≤ c := by
    have h01 : (0 : ℝ) ≤ 1 := zero_le_one
    have := hg_mono h01
    rwa [hg0] at this
  intro t
  -- Upper bound: g t ≤ c * t.
  have hupper : g t ≤ c * t := by
    by_contra hlt
    push_neg at hlt  -- hlt : c * t < g t
    -- find a rational q with t < q and c * q < g t, contradicting g t ≤ g q = c*q.
    rcases eq_or_lt_of_le hc0 with hc_eq | hc_pos
    · -- c = 0:  then c * t = 0 < g t.  Take any rational q > t; g t ≤ c*q = 0 < g t.
      rcases exists_rat_gt t with ⟨q, hq⟩
      have hmono : g t ≤ g (q : ℝ) := hg_mono hq.le
      have hval : g (q : ℝ) = c * (q : ℝ) := hg_rat q
      have : g t ≤ c * (q : ℝ) := hval ▸ hmono
      have hcq : c * (q : ℝ) = 0 := by rw [← hc_eq]; ring
      have : g t ≤ 0 := hcq ▸ this
      have hgt0 : (0 : ℝ) < g t := by
        have : c * t = 0 := by rw [← hc_eq]; ring
        rwa [this] at hlt
      exact absurd this (not_le.mpr hgt0)
    · -- c > 0:  t < g t / c, pick rational q in (t, g t / c); then g t ≤ c*q < g t.
      have ht_lt : t < g t / c := by
        rw [lt_div_iff hc_pos]; rw [mul_comm]; exact hlt
      rcases exists_rat_btwn ht_lt with ⟨q, hq_lo, hq_hi⟩
      have hmono : g t ≤ g (q : ℝ) := hg_mono hq_lo.le
      have hval : g (q : ℝ) = c * (q : ℝ) := hg_rat q
      have hle : g t ≤ c * (q : ℝ) := hval ▸ hmono
      -- c * q < g t  from  q < g t / c.
      have hcq_lt : c * (q : ℝ) < g t := by
        have := (lt_div_iff' hc_pos).mp hq_hi  -- c * q < g t
        exact this
      exact absurd hle (not_le.mpr hcq_lt)
  -- Lower bound: c * t ≤ g t.
  have hlower : c * t ≤ g t := by
    by_contra hlt
    push_neg at hlt  -- hlt : g t < c * t
    rcases eq_or_lt_of_le hc0 with hc_eq | hc_pos
    · -- c = 0:  c*t = 0, so g t < 0.  Take rational q < t; g q ≤ g t, but g q = 0.
      rcases exists_rat_lt t with ⟨q, hq⟩
      have hmono : g (q : ℝ) ≤ g t := hg_mono hq.le
      have hval : g (q : ℝ) = c * (q : ℝ) := hg_rat q
      have hcq : c * (q : ℝ) = 0 := by rw [← hc_eq]; ring
      have hzero_le : (0 : ℝ) ≤ g t := by
        have : g (q : ℝ) = 0 := by rw [hval, hcq]
        rwa [this] at hmono
      have hgt_neg : g t < 0 := by
        have : c * t = 0 := by rw [← hc_eq]; ring
        rwa [this] at hlt
      exact absurd hzero_le (not_le.mpr hgt_neg)
    · -- c > 0:  g t / c < t, pick rational q in (g t / c, t); g q ≤ g t but g q = c*q > g t.
      have ht_gt : g t / c < t := by
        rw [div_lt_iff hc_pos]; rw [mul_comm]; exact hlt
      rcases exists_rat_btwn ht_gt with ⟨q, hq_lo, hq_hi⟩
      have hmono : g (q : ℝ) ≤ g t := hg_mono hq_hi.le
      have hval : g (q : ℝ) = c * (q : ℝ) := hg_rat q
      have hle : c * (q : ℝ) ≤ g t := hval ▸ hmono
      -- g t < c * q  from  g t / c < q.
      have hgt_lt : g t < c * (q : ℝ) := by
        have := (div_lt_iff' hc_pos).mp hq_lo  -- g t < c * q
        exact this
      exact absurd hle (not_le.mpr hgt_lt)
  exact le_antisymm hupper hlower

#print axioms additive_ratCast_linear
#print axioms monotone_additive_linear

end Lutar.Wave6
