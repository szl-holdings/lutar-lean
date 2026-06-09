import Mathlib

namespace Lutar.Putnam.Sampler

/-!
# Sampler Problem 4 (Number theory / infinitude in a progression)

**Problem (PDF):** Prove there are infinitely many primes `p` with `p ≡ 3 (mod 4)`.

**Math (Euclid-style):** If only finitely many such primes existed, form
`N = 4·(product of them) - 1 ≡ 3 (mod 4)`. `N` is odd and `> 1`, so it has an odd prime
factor; not all its prime factors can be `≡ 1 (mod 4)` (their product would be `≡ 1`), so
some prime factor is `≡ 3 (mod 4)`, and it is not in the finite list — contradiction.

**Status: HONEST OPEN ATTEMPT.** This is a genuine theorem (special case of Dirichlet),
but a clean, kernel-checked Lean proof — either via Mathlib's Dirichlet machinery or a
self-contained Euclid argument over `ZMod 4` — is not yet closed here. The residual below is
an explicitly-labeled `sorry`, NOT a hidden one. It is counted as OPEN, not proven.
-/

theorem p04 : {p : ℕ | p.Prime ∧ p % 4 = 3}.Infinite := by
  sorry -- sorry_sampler_p04: infinitude of primes ≡ 3 (mod 4) — open attempt (honest residual)

end Lutar.Putnam.Sampler
