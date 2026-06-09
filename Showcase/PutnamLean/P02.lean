/-
# Classic / Putnam-style number theory — REAL (kernel-checked)

Problem. For every natural number `n`, `6 ∣ n³ − n`.
We state the equivalent, subtraction-free congruence used in the formalization:
`n ^ 3 % 6 = n % 6`  (i.e. `n³ ≡ n (mod 6)`).

Honesty label: **REAL.** Complete, kernel-checked, zero `sorry`.
`#print axioms cube_mod_six` reports only `[propext]`, an in-policy Lean-core
axiom. Mathlib-free; the residue check is closed by `decide` over `Fin 6`.

Honest attribution: this is the classic `n³ ≡ n (mod 6)` fact — a standard
Putnam-style number-theory warm-up — not a specific Putnam-year problem. It is
included to show a genuine, axiom-clean `decide`-backed REAL proof alongside the
algebraic P01.

See `Showcase/Putnam/P02.md` for the human-readable writeup.
-/
namespace Showcase.Putnam

/-- `n³ ≡ n (mod 6)` for every `n : ℕ`, hence `6 ∣ n³ − n`. -/
theorem cube_mod_six (n : Nat) : n ^ 3 % 6 = n % 6 := by
  -- Rewrite `n ^ 3` as `n * n * n` (core `pow` unfolding).
  have e : n ^ 3 = n * n * n := by
    simp [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  -- The whole claim is decidable once everything is reduced modulo 6:
  -- check it for each residue class `r ∈ Fin 6`.
  have key : ∀ r : Fin 6, ((r.val * r.val % 6) * r.val) % 6 = r.val := by decide
  rw [e, Nat.mul_mod, Nat.mul_mod n n 6]
  have h := key ⟨n % 6, Nat.mod_lt _ (by decide)⟩
  simpa using h

-- Honesty proof: emitted into the build log (shows `propext` only).
#print axioms cube_mod_six

end Showcase.Putnam
