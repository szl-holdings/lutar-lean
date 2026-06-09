import Mathlib

namespace Lutar.Putnam.Sampler

/-!
# Sampler Problem 5 (Functional equation / Cauchy)

**Problem (PDF):** Let `f : ℝ → ℝ` satisfy `f(x+y) = f(x) + f(y)` for all `x, y` and be
continuous (here: continuous at `0`). Prove `f` is linear: `∃ c, ∀ x, f x = c·x` (with `c = f 1`).

**Math:** Additivity gives `ℚ`-linearity (`f(qx) = q f(x)` for rational `q`); continuity at
a point upgrades a group homomorphism to continuity everywhere, hence `ℝ`-linearity by density
of `ℚ`. Then `f x = x · f 1`.

**Status: HONEST OPEN ATTEMPT.** The result is standard, but a clean kernel-checked Lean
proof (additive → `ℚ`-linear → continuous-everywhere → `ℝ`-linear via density) is not yet
closed here. The residual below is an explicitly-labeled `sorry`, NOT a hidden one. Counted
as OPEN, not proven.
-/

theorem p05 (f : ℝ → ℝ) (hadd : ∀ x y : ℝ, f (x + y) = f x + f y)
    (hcont : ContinuousAt f 0) : ∃ c : ℝ, ∀ x : ℝ, f x = c * x := by
  sorry -- sorry_sampler_p05: Cauchy FE + continuity ⇒ linear — open attempt (honest residual)

end Lutar.Putnam.Sampler
