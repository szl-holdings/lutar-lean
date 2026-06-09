import Mathlib

namespace Lutar.Putnam.Sampler

/-!
# Sampler Problem 9 (Algebra / no polynomial with a forbidden functional equation)

**Problem (PDF):** Prove there is no real polynomial `p` with `p(0) = 0`, `p(1) = 1`, and
`p(x)² = p(x²)` for all real `x`.

**Math sketch:** From `p(x)² = p(x²)` and degree considerations, the leading coefficient must
be `1` and `p(x) = xⁿ` for the multiplicative relation to hold on all reals; but `p(0) = 0`
forces `n ≥ 1` while `p(x)² = p(x²)` with `p(0)=0, p(1)=1` together pin `p(x) = xⁿ`, and then
no such monomial simultaneously satisfies all the imposed point/identity constraints of the
problem — contradiction.

**Status: HONEST OPEN ATTEMPT.** A clean kernel-checked Lean proof (degree/leading-coefficient
argument over `Polynomial ℝ`, or an infinitely-many-roots argument) is not yet closed here.
The residual below is an explicitly-labeled `sorry`, NOT a hidden one. Counted as OPEN.
-/

theorem p09 :
    ¬ ∃ p : Polynomial ℝ,
      Polynomial.eval 0 p = 0 ∧ Polynomial.eval 1 p = 1 ∧
        ∀ x : ℝ, (Polynomial.eval x p) ^ 2 = Polynomial.eval (x ^ 2) p := by
  sorry -- sorry_sampler_p09: no polynomial with p(0)=0,p(1)=1,p(x)²=p(x²) — open attempt

end Lutar.Putnam.Sampler
