/-
Copyright © 2026 Stephen P. Lutar Jr. (SZL Holdings).
Released under the Apache-2.0 License.

# Entanglement — the Λ-v5 coherence → entanglement-capacity bound, machine-checked.

## What is NEW here (vs the existing kernel)

`Lutar/QuantumBio/CoherenceDecay.lean` already proves (Wave24, merged) that under
pure-dephasing Lindblad dynamics the l₁ coherence monotone obeys
`C t = C₀ · exp (−γ t)` and is strictly antitone in `t`.

Streltsov et al. (2015, PRL 115 020403) established that l₁-coherence upper-bounds
the entanglement a system can GENERATE under incoherent operations. Composing the
two gives SZL's PROPOSED unifying bound on the *entanglement-generating capacity*:

    E_max t  ≤  C₀ · exp (−γ t)

This file machine-checks the order-theoretic backbone of that bound: define the
capacity envelope `capBound C₀ γ t = C₀ · exp (−γ t)` and prove (a) it is the
non-negative decaying coherence envelope, (b) it is antitone in `t` for `γ ≥ 0`,
`C₀ ≥ 0`, and (c) any entanglement measure dominated by it at every time inherits
that decay. No `sorry`; Mathlib/Lean-core axioms only.

## What this does NOT do (doctrine hard gate)

Adds NOTHING to the locked-proven set (stays EXACTLY 8). Does NOT touch Λ:
unconditional Λ-uniqueness stays **Conjecture 1**; Λ-v5 and this capacity bound
stay **PROPOSED engineering gates**, never theorems about Λ. This is a CAPACITY
UPPER BOUND, not a uniqueness or existence claim about entanglement. Trust never
100%. Citations: Streltsov et al. 2015; SZL Λ-v5 CoherenceDecay (merged).
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Order.Monotone.Basic

namespace Lutar.Entanglement

open Real

/-- The Λ-v5 coherence envelope = the entanglement-generating-capacity upper bound:
`capBound C₀ γ t = C₀ · exp (−γ t)`. (Streltsov 2015 ∘ SZL Wave24 decay.) -/
noncomputable def capBound (C₀ γ t : ℝ) : ℝ := C₀ * Real.exp (-γ * t)

/-- The capacity bound is non-negative whenever the initial coherence is. -/
theorem capBound_nonneg {C₀ γ t : ℝ} (hC : 0 ≤ C₀) : 0 ≤ capBound C₀ γ t := by
  unfold capBound
  exact mul_nonneg hC (Real.exp_nonneg _)

/-- At `t = 0` the capacity bound equals the initial coherence `C₀`. -/
theorem capBound_zero (C₀ γ : ℝ) : capBound C₀ γ 0 = C₀ := by
  unfold capBound
  simp

/-- The capacity bound is antitone in time for non-negative `C₀` and `γ`:
entanglement-generating capacity can only decay. -/
theorem capBound_antitone {C₀ γ : ℝ} (hC : 0 ≤ C₀) (hγ : 0 ≤ γ) :
    Antitone (fun t => capBound C₀ γ t) := by
  intro a b hab
  unfold capBound
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  -- -γ*b ≤ -γ*a  ⇐  γ*a ≤ γ*b  ⇐  a ≤ b (γ ≥ 0)
  have : γ * a ≤ γ * b := mul_le_mul_of_nonneg_left hab hγ
  linarith

/-- Capacity-domination is inherited: any entanglement measure `E` that never
exceeds the capacity bound is itself bounded by the decaying envelope at every
time. (The honest content of `E_max t ≤ C₀·exp(−γ t)`.) -/
theorem entanglement_decays_under_bound
    {C₀ γ : ℝ} (E : ℝ → ℝ) (hdom : ∀ t, E t ≤ capBound C₀ γ t) (t : ℝ) :
    E t ≤ C₀ * Real.exp (-γ * t) := hdom t

end Lutar.Entanglement
