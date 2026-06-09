/-
# Putnam 2001 A1 — REAL (kernel-checked)

Problem. A binary operation `*` on a set `S` satisfies `(a * b) * a = b` for all
`a, b ∈ S`. Prove that `a * (b * a) = b` for all `a, b ∈ S`.

Honesty label: **REAL.** This is a complete, kernel-checked proof with zero
`sorry`. `#print axioms putnam2001A1` reports that it does **not depend on any
axioms** (not even `propext`). The file is Mathlib-free and compiles against
`leanprover/lean4:v4.18.0` core.

See `Showcase/Putnam/P01.md` for the human-readable writeup.
-/
namespace Showcase.Putnam

/-- Putnam 2001 A1: from `(a * b) * a = b` for all `a b`, deduce `a * (b * a) = b`. -/
theorem putnam2001A1 {S : Type _} (op : S → S → S)
    (H : ∀ a b, op (op a b) a = b) (a b : S) :
    op a (op b a) = b := by
  -- Instantiate the hypothesis at `(b * a)` and `b`:
  --   ((b * a) * b) * (b * a) = b
  have key := H (op b a) b
  -- The hypothesis at `b`, `a` collapses the inner factor: `(b * a) * b = a`.
  have hc : op (op b a) b = a := H b a
  rw [hc] at key
  exact key

-- Honesty proof: emitted into the build log.
#print axioms putnam2001A1

end Showcase.Putnam
