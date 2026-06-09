import Mathlib

namespace Lutar.Putnam.P_B2

open MeasureTheory

/-!
# Putnam 2025 B2

**Problem.** Let `f : [0,1] → [0,∞)` be strictly increasing and continuous. Let
`R` be the region bounded by `x = 0`, `x = 1`, `y = 0`, `y = f(x)`. Let `x₁` be
the `x`-coordinate of the centroid of `R`, and `x₂` the `x`-coordinate of the
centroid of the solid obtained by rotating `R` about the `x`-axis. Prove
`x₁ < x₂`.

**Honest status: DEMO** — faithful statement, proof DEFERRED (`sorry`).
The centroid `x`-coordinates are the standard moment ratios:
`x₁ = (∫ x f) / (∫ f)` and `x₂ = (∫ x f²) / (∫ f²)` over `[0,1]`.
-/

/-- `x`-coordinate of the centroid of the planar region under `f`. -/
noncomputable def x1 (f : ℝ → ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..1, x * f x) / (∫ x in (0 : ℝ)..1, f x)

/-- `x`-coordinate of the centroid of the solid of revolution about the
`x`-axis. -/
noncomputable def x2 (f : ℝ → ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..1, x * (f x) ^ 2) / (∫ x in (0 : ℝ)..1, (f x) ^ 2)

/-- Faithful statement of Putnam 2025 B2 (DEMO: proof deferred). -/
theorem putnam_B2_correct (f : ℝ → ℝ)
    (hmono : StrictMonoOn f (Set.Icc 0 1))
    (hcont : ContinuousOn f (Set.Icc 0 1))
    (hpos : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 < f x) :
    x1 f < x2 f := by
  sorry

end Lutar.Putnam.P_B2
