/-
# Hamilton Quaternion Algebra

The four-dimensional real algebra of quaternions, with the Hamilton product
and its key invariant: the product is norm-multiplicative (the quaternion
norm is a multiplicative function from ℍ to ℝ≥0).  As an immediate
corollary, unit quaternions are closed under the Hamilton product, which
is the invariant the a11oy `quaternion-state` governance token relies on
for receipt composition.

## References

- Hamilton, W. R. (1843). "On a New Species of Imaginary Quantities,
  Connected with a Theory of Quaternions." Proc. Royal Irish Academy
  2:424–434.  JSTOR 20520177.
- Hamilton, W. R. (1853). *Lectures on Quaternions.* Dublin: Hodges &
  Smith.

## Companion Lean modules

- `Lutar.Invariant` (Λ_k geometric mean) — independent.
- `Lutar.Bound` (sub-ms bound) — independent.

This module is self-contained: it does not depend on any other Lutar
module and provides the algebraic foundation for the quaternion
governance state token used in `a11oy-core/governance/quaternion-state.ts`.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Lutar.Quaternion

/-- A quaternion as a 4-tuple of reals. -/
structure Quaternion where
  w : ℝ
  x : ℝ
  y : ℝ
  z : ℝ
deriving Repr

namespace Quaternion

/-- The doctrinal identity quaternion: zero rotation. -/
def one : Quaternion := ⟨1, 0, 0, 0⟩

/-- The Hamilton product on ℍ.

  (q₁ q₂).w = w₁w₂ − x₁x₂ − y₁y₂ − z₁z₂
  (q₁ q₂).x = w₁x₂ + x₁w₂ + y₁z₂ − z₁y₂
  (q₁ q₂).y = w₁y₂ − x₁z₂ + y₁w₂ + z₁x₂
  (q₁ q₂).z = w₁z₂ + x₁y₂ − y₁x₂ + z₁w₂
-/
def mul (q1 q2 : Quaternion) : Quaternion where
  w := q1.w * q2.w - q1.x * q2.x - q1.y * q2.y - q1.z * q2.z
  x := q1.w * q2.x + q1.x * q2.w + q1.y * q2.z - q1.z * q2.y
  y := q1.w * q2.y - q1.x * q2.z + q1.y * q2.w + q1.z * q2.x
  z := q1.w * q2.z + q1.x * q2.y - q1.y * q2.x + q1.z * q2.w

instance : Mul Quaternion := ⟨mul⟩

/-- Squared norm ||q||² = w² + x² + y² + z². -/
def normSq (q : Quaternion) : ℝ :=
  q.w * q.w + q.x * q.x + q.y * q.y + q.z * q.z

/-- The squared norm is always non-negative. -/
lemma normSq_nonneg (q : Quaternion) : 0 ≤ q.normSq := by
  unfold normSq
  have h1 : 0 ≤ q.w * q.w := mul_self_nonneg _
  have h2 : 0 ≤ q.x * q.x := mul_self_nonneg _
  have h3 : 0 ≤ q.y * q.y := mul_self_nonneg _
  have h4 : 0 ≤ q.z * q.z := mul_self_nonneg _
  linarith

/-- The unit quaternion `one` has squared norm 1. -/
@[simp] lemma normSq_one : Quaternion.one.normSq = 1 := by
  unfold normSq one
  ring

/--
The Hamilton product is norm-squared-multiplicative:

  ||q₁ q₂||² = ||q₁||² · ||q₂||².

This is the four-square identity (Euler 1748; cited in Hamilton 1843 as
the algebraic seed of quaternion multiplication).  The proof is direct
polynomial expansion, closed by `ring`.
-/
theorem hamilton_product_normSq_multiplicative (q1 q2 : Quaternion) :
    (q1 * q2).normSq = q1.normSq * q2.normSq := by
  show (mul q1 q2).normSq = q1.normSq * q2.normSq
  unfold mul normSq
  simp only
  ring

/--
Corollary: unit quaternions are closed under the Hamilton product.
If ||q₁||² = 1 and ||q₂||² = 1, then ||q₁ q₂||² = 1.

This is the algebraic invariant that the `quaternion-state` governance
token relies on: composing two unit-norm receipts produces a unit-norm
receipt, so the token remains on S³ ⊂ ℝ⁴ under composition.
-/
theorem unit_quaternion_closed_under_multiplication
    (q1 q2 : Quaternion) (h1 : q1.normSq = 1) (h2 : q2.normSq = 1) :
    (q1 * q2).normSq = 1 := by
  rw [hamilton_product_normSq_multiplicative, h1, h2]
  ring

/--
The doctrinal identity is a left identity for the Hamilton product.
-/
theorem one_mul (q : Quaternion) : Quaternion.one * q = q := by
  show mul Quaternion.one q = q
  unfold mul one
  -- (1·w - 0 - 0 - 0, 1·x + 0 + 0 - 0, 1·y - 0 + 0 + 0, 1·z + 0 - 0 + 0)
  simp
  -- Reduce by cases on the record fields.
  cases q with
  | mk w x y z => simp

/--
The doctrinal identity is a right identity for the Hamilton product.
-/
theorem mul_one (q : Quaternion) : q * Quaternion.one = q := by
  show mul q Quaternion.one = q
  unfold mul one
  simp
  cases q with
  | mk w x y z => simp

/--
Quaternion multiplication is associative.  Direct polynomial expansion
closed by `ring`.
-/
theorem mul_assoc (q1 q2 q3 : Quaternion) :
    (q1 * q2) * q3 = q1 * (q2 * q3) := by
  show mul (mul q1 q2) q3 = mul q1 (mul q2 q3)
  unfold mul
  -- Element-wise equality of records, each component closed by `ring`.
  congr 1 <;> ring

end Quaternion
end Lutar.Quaternion
