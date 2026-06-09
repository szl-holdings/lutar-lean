import Mathlib

namespace Lutar.Putnam.Sampler

/-!
# Sampler Problem 4 (Number theory / infinitude in a progression)

**Problem (PDF):** Prove there are infinitely many primes `p` with `p ≡ 3 (mod 4)`.

**Math (Euclid-style):** If only finitely many such primes existed, form
`N = 4·(product of them) - 1 ≡ 3 (mod 4)`. `N` is odd and `> 1`, so it has an odd prime
factor; not all its prime factors can be `≡ 1 (mod 4)` (their product would be `≡ 1`), so
some prime factor is `≡ 3 (mod 4)`, and it is not in the finite list — contradiction.

**Status: CLOSED — KERNEL-VERIFIED (no `sorry`).** Discharged from Mathlib's Dirichlet
machinery: `Nat.setOf_prime_and_eq_mod_infinite` gives infinitude of primes in the residue
class `a` modulo `q` whenever `a` is a unit of `ZMod q`; here `q = 4`, `a = 3` (a unit since
`3 · 3 = 1` in `ZMod 4`). A short `ZMod.natCast_eq_natCast_iff'` bridge identifies the
congruence `(p : ZMod 4) = 3` with `p % 4 = 3`. No new declared axiom token.
-/

theorem p04 : {p : ℕ | p.Prime ∧ p % 4 = 3}.Infinite := by
  have hu : IsUnit (3 : ZMod 4) := isUnit_of_mul_eq_one 3 3 (by decide)
  have h := Nat.setOf_prime_and_eq_mod_infinite (q := 4) (a := (3 : ZMod 4)) hu
  have hset :
      {p : ℕ | p.Prime ∧ (p : ZMod 4) = 3} = {p : ℕ | p.Prime ∧ p % 4 = 3} := by
    ext p
    simp only [Set.mem_setOf_eq, and_congr_right_iff]
    intro _
    have h3 : (3 : ZMod 4) = ((3 : ℕ) : ZMod 4) := by norm_cast
    rw [h3, ZMod.natCast_eq_natCast_iff']
    constructor <;> intro hh <;> omega
  rwa [hset] at h

end Lutar.Putnam.Sampler
