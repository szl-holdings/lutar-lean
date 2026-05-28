/-
# R1-G1 — False-position (aha) gate calibration

The Egyptian *aha* method of the Rhind Mathematical Papyrus (~1650 BCE)
solves a linear equation by trial-and-rescale. For an affine gate
`f(x) = m·x + c`, two known sample points `(x₁, y₁) = (x₁, m·x₁ + c)` and
`(x₂, y₂) = (x₂, m·x₂ + c)` with `x₁ ≠ x₂` determine `m, c` uniquely. Given
a target `T`, the input `x*` with `f(x*) = T` is

    x* = x₁ + (T − y₁) · (x₂ − x₁) / (y₂ − y₁).

This module proves `false_position_correct`: for any affine `f` and any
two non-degenerate samples, the closed-form `x*` recovers the target
exactly.

Sources:
  * Imhausen, A. (2016), *Mathematics in Ancient Egypt: A Contextual History*,
    Princeton University Press, ISBN 978-0691117133, ch. 3 §3.4.
  * Robins, G. & Shute, C. (1987), *The Rhind Mathematical Papyrus*,
    British Museum Press, ISBN 978-0714109442 (RMP Problems 24–27).
  * Gillings, R. J. (1972), *Mathematics in the Time of the Pharaohs*,
    MIT Press, ISBN 978-0262570954, ch. 14.

Runtime counterpart:
  `a11oy/web/packages/a11oy-core/src/calibration/false-position.ts`.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace Lutar.Calibration

/-- Closed-form one-step false-position correction. -/
noncomputable def falsePosition
    (x₁ y₁ x₂ y₂ T : ℝ) : ℝ :=
  x₁ + (T - y₁) * (x₂ - x₁) / (y₂ - y₁)

/-- **R1-G1 theorem.** For any affine gate `f(x) = m·x + c` with `m ≠ 0`,
    the closed-form false-position correction at two samples
    `(x₁, m·x₁ + c)` and `(x₂, m·x₂ + c)` recovers any target `T`
    exactly: `f(x*) = T`. Closes by `field_simp` + `ring`. -/
theorem false_position_correct
    (m c x₁ x₂ T : ℝ) (hm : m ≠ 0) (hx : x₁ ≠ x₂) :
    let y₁ := m * x₁ + c
    let y₂ := m * x₂ + c
    let xStar := falsePosition x₁ y₁ x₂ y₂ T
    m * xStar + c = T := by
  -- y₂ − y₁ = m * (x₂ − x₁), non-zero by hm and hx
  have hdx : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hdy : m * x₂ + c - (m * x₁ + c) ≠ 0 := by
    have : m * x₂ + c - (m * x₁ + c) = m * (x₂ - x₁) := by ring
    rw [this]
    exact mul_ne_zero hm hdx
  -- Unfold and discharge.
  simp only [falsePosition]
  -- Mathlib v4.13.0: field_simp needs the denominator in the exact form it produces.
  -- After unfolding, the denominator is `-(m * x₁) + m * x₂`.
  -- hdy says `m * x₂ + c - (m * x₁ + c) ≠ 0`; ring-simplify to get the right form.
  have hden_ne : -(m * x₁) + m * x₂ ≠ 0 := by
    intro h
    apply hdy
    linarith
  field_simp [hden_ne]
  ring

/-- Identity sanity: target equals `y₁` recovers `x₁`. -/
theorem false_position_identity
    (m c x₁ x₂ : ℝ) (hm : m ≠ 0) (hx : x₁ ≠ x₂) :
    let y₁ := m * x₁ + c
    let y₂ := m * x₂ + c
    falsePosition x₁ y₁ x₂ y₂ y₁ = x₁ := by
  simp only [falsePosition]
  ring

end Lutar.Calibration
