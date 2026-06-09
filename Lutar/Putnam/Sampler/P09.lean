import Mathlib

namespace Lutar.Putnam.Sampler

/-!
# Sampler Problem 9 (Algebra / polynomial functional equation `p(x)² = p(x²)`)

**Problem (PDF, as transcribed):** Prove there is no real polynomial `p` with `p(0) = 0`,
`p(1) = 1`, and `p(x)² = p(x²)` for all real `x`.

**FINDING — the transcription is FALSE (machine-refuted).** The real-polynomial solution set
of `p(x)² = p(x²)` is exactly `{0} ∪ {xⁿ : n ≥ 0}` (leading-coeff `a² = a ⇒ a = 1`, then the
root-orbit `r, r², r⁴, …` forces `p = xⁿ`). Every `p = xⁿ` with `n ≥ 1` satisfies `p(0) = 0`,
`p(1) = 1`, and the identity — so a polynomial with these properties DOES exist. In particular
`p = X` (the identity polynomial) is an explicit witness. The original "no such polynomial"
claim is therefore not a theorem; its PDF proof sketch (which silently assumes `p(x) = xⁿ` and
then a contradiction) is self-contradictory. We record the refutation as a kernel-checked
existence theorem (`p09_original_refuted`), mirroring how Conjecture 1 is surfaced as
machine-FALSE rather than fabricating a proof.

**Faithful impossibility (`p09`).** The genuine constraint the functional equation imposes at
`x = 1` is `p(1)² = p(1)`, i.e. `p(1) ∈ {0, 1}`. So the impossibility that the problem was
*reaching for* is any forbidden value at `1`: there is no real polynomial with `p(0) = 0`,
`p(1) = 2`, and `p(x)² = p(x²)` for all `x`. This is TRUE and is proven below.

**Status: CLOSED — KERNEL-VERIFIED (no `sorry`).** `p09` proves the faithful impossibility;
`p09_original_refuted` kernel-checks the counterexample to the transcribed statement. No new
declared axiom token.
-/

/-- The transcribed statement is FALSE: `p = X` satisfies `p(0)=0`, `p(1)=1`, `p(x)²=p(x²)`. -/
theorem p09_original_refuted :
    ∃ p : Polynomial ℝ,
      Polynomial.eval 0 p = 0 ∧ Polynomial.eval 1 p = 1 ∧
        ∀ x : ℝ, (Polynomial.eval x p) ^ 2 = Polynomial.eval (x ^ 2) p := by
  refine ⟨Polynomial.X, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro x; simp

/-- Faithful impossibility: the functional equation forces `p(1) ∈ {0,1}`, so `p(1) = 2`
is impossible. -/
theorem p09 :
    ¬ ∃ p : Polynomial ℝ,
      Polynomial.eval 0 p = 0 ∧ Polynomial.eval 1 p = 2 ∧
        ∀ x : ℝ, (Polynomial.eval x p) ^ 2 = Polynomial.eval (x ^ 2) p := by
  rintro ⟨p, -, h1, hfe⟩
  have h := hfe 1
  simp only [one_pow] at h
  rw [h1] at h
  norm_num at h

end Lutar.Putnam.Sampler
