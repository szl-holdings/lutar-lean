import Mathlib

namespace Lutar.Putnam.Sampler

/-!
# Sampler Problem 5 (Functional equation / Cauchy)

**Problem (PDF):** Let `f : ℝ → ℝ` satisfy `f(x+y) = f(x) + f(y)` for all `x, y` and be
continuous (here: continuous at `0`). Prove `f` is linear: `∃ c, ∀ x, f x = c·x` (with `c = f 1`).

**Math:** Additivity makes `f` an `AddMonoidHom ℝ ℝ`; continuity at `0` upgrades a topological
group hom to continuity everywhere (`continuous_of_continuousAt_zero`); a continuous additive
map on `ℝ` is `ℝ`-linear (`map_real_smul`), so `f x = x · f 1 = f 1 · x`.

**Status: CLOSED — KERNEL-VERIFIED (no `sorry`).** Built directly on Mathlib: package `f` as
`AddMonoidHom.mk' f hadd`, promote `ContinuousAt _ 0` to `Continuous` via
`continuous_of_continuousAt_zero`, then `map_real_smul` (continuous additive ⇒ `ℝ`-linear)
gives `f x = x • f 1`. No new declared axiom token.
-/

theorem p05 (f : ℝ → ℝ) (hadd : ∀ x y : ℝ, f (x + y) = f x + f y)
    (hcont : ContinuousAt f 0) : ∃ c : ℝ, ∀ x : ℝ, f x = c * x := by
  let g : ℝ →+ ℝ := AddMonoidHom.mk' f hadd
  have hcoe : ∀ y : ℝ, g y = f y := fun _ => rfl
  have hgcont : Continuous g := continuous_of_continuousAt_zero g hcont
  refine ⟨f 1, fun x => ?_⟩
  have hsmul := map_real_smul g hgcont x (1 : ℝ)
  simp only [smul_eq_mul, mul_one] at hsmul
  rw [hcoe x, hcoe 1] at hsmul
  rw [hsmul]; ring

end Lutar.Putnam.Sampler
