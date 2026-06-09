/-
# Putnam 2019 A1 — DEMO (statement formalized, proof deferred)

Problem. Determine all nonnegative integers `n` that can be written as
`A³ + B³ + C³ − 3ABC` for some nonnegative integers `A, B, C`.
Answer (the statement we formalize): exactly the `n` with `n % 9 ∉ {3, 6}`.

Honesty label: **DEMO.** The *statement* below typechecks against core Lean,
but the proof is `sorry`. `#print axioms putnam2019A1_iff` would therefore report
`sorryAx`. This file is intentionally NOT labeled REAL: per honesty doctrine v11
we never call a `sorry`-bearing result kernel-checked.

Why DEMO: the forward direction needs the identity
`A³+B³+C³−3ABC = (A+B+C)(A²+B²+C²−AB−BC−CA)` and a residue analysis mod 9; the
reverse needs explicit constructions. That is real Mathlib work, staged here as
a faithful statement scaffold rather than a fake "REAL" claim.

See `Showcase/Putnam/P03.md` for the human-readable writeup.
-/
namespace Showcase.Putnam

/-- The cyclic form `A³ + B³ + C³ − 3ABC`, over `ℤ` to keep subtraction total. -/
def cyclicForm (A B C : Int) : Int := A ^ 3 + B ^ 3 + C ^ 3 - 3 * A * B * C

/-- Putnam 2019 A1 (DEMO): `n` is representable iff `n % 9 ∉ {3, 6}`.
    Proof deferred (`sorry`) — this declaration is DEMO, not REAL. -/
theorem putnam2019A1_iff (n : Int) (hn : 0 ≤ n) :
    (∃ A B C : Int, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ C ∧ cyclicForm A B C = n)
      ↔ (n % 9 ≠ 3 ∧ n % 9 ≠ 6) := by
  sorry

end Showcase.Putnam
