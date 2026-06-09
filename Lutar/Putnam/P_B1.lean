import Mathlib

namespace Lutar.Putnam.P_B1

/-!
# Putnam 2025 B1

**Problem.** Suppose each point of the plane is colored red or green so that:
for every three noncollinear points `A, B, C` of the same color, the center of
the circle through `A, B, C` is also that color. Prove that all points of the
plane are the same color.

**Honest status: DEMO** — faithful statement, proof DEFERRED (`sorry`).
The circumcenter is encoded via its defining equidistance property: `O` is the
center of the circle through `A, B, C` exactly when `O` is equidistant from all
three (`dist O A = dist O B = dist O C`), which for noncollinear `A, B, C`
determines `O` uniquely. This avoids any fragile circumcenter API.
-/

/-- The two colors. -/
inductive Color
  | red
  | green

/-- A coloring of the Euclidean plane. -/
abbrev Coloring := EuclideanSpace ℝ (Fin 2) → Color

/-- The coloring is closed under circumcenters of monochromatic noncollinear
triples (the circumcenter = the unique point equidistant from the three
points). -/
def CircleClosed (c : Coloring) : Prop :=
  ∀ A B C O : EuclideanSpace ℝ (Fin 2),
    ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) →
    c A = c B → c B = c C →
    dist O A = dist O B → dist O B = dist O C → c O = c A

/-- Faithful statement of Putnam 2025 B1 (DEMO: proof deferred). -/
theorem putnam_B1_correct (c : Coloring) (hc : CircleClosed c) :
    (∀ p : EuclideanSpace ℝ (Fin 2), c p = Color.red) ∨
    (∀ p : EuclideanSpace ℝ (Fin 2), c p = Color.green) := by
  sorry

end Lutar.Putnam.P_B1
