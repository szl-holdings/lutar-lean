import Mathlib

namespace Lutar.Putnam.Sampler

open Polynomial

/-!
# Sampler Problem 9 (Algebra / polynomial functional equation `p(x)² = p(x²)`)

**Problem (PDF, as transcribed):** Prove there is no real polynomial `p` with `p(0) = 0`,
`p(1) = 1`, and `p(x)² = p(x²)` for all real `x`.

**FINDING — the transcription is FALSE (machine-refuted).** The real-polynomial solution set
of `p(x)² = p(x²)` is exactly `{0} ∪ {xⁿ : n ≥ 0}` (leading-coeff `a² = a ⇒ a = 1`, then the
root-orbit `r, r², r⁴, …` forces `p = xⁿ`). Every `p = xⁿ` with `n ≥ 1` satisfies `p(0) = 0`,
`p(1) = 1`, and the identity — so a polynomial with these properties DOES exist. In particular
`p = X` (the identity polynomial) is an explicit witness. The original "no such polynomial"
claim is therefore not a theorem; its PDF proof sketch (which silently assumes `p(x) = xⁿ` and
then a contradiction) is self-contradictory. We record the refutation as a kernel-checked
existence theorem (`p09_original_refuted`), mirroring how Conjecture 1 is surfaced as
machine-FALSE rather than fabricating a proof.

**Faithful impossibility (`p09`).** The genuine constraint the functional equation imposes at
`x = 1` is `p(1)² = p(1)`, i.e. `p(1) ∈ {0, 1}`. So the impossibility that the problem was
*reaching for* is any forbidden value at `1`: there is no real polynomial with `p(0) = 0`,
`p(1) = 2`, and `p(x)² = p(x²)` for all `x`. This is TRUE and is proven below.

**Full classification (`p09_classification`).** The complete characterization behind the
finding is itself kernel-checked: over `ℝ[X]`, a polynomial satisfies `p(x)² = p(x²)` for all
real `x` **iff** `p = 0` or `p = Xⁿ` for some `n ≥ 0`. The functional equation is upgraded to
the polynomial identity `p² = expand ℝ 2 p` (valid because `ℝ` is infinite), the leading
coefficient is forced to `1`, and a coefficient comparison at degree `n + deg(p - Xⁿ)` shows
the deviation `p - Xⁿ` must vanish. Both `p09` and `p09_original_refuted` are immediate
corollaries of this stronger statement.

**Status: CLOSED — KERNEL-VERIFIED (no `sorry`).** `p09` proves the faithful impossibility;
`p09_original_refuted` kernel-checks the counterexample to the transcribed statement;
`p09_classification` kernel-checks the full solution-set characterization. No new declared
axiom token.
-/

/-- The transcribed statement is FALSE: `p = X` satisfies `p(0)=0`, `p(1)=1`, `p(x)²=p(x²)`. -/
theorem p09_original_refuted :
    ∃ p : Polynomial ℝ,
      Polynomial.eval 0 p = 0 ∧ Polynomial.eval 1 p = 1 ∧
        ∀ x : ℝ, (Polynomial.eval x p) ^ 2 = Polynomial.eval (x ^ 2) p := by
  refine ⟨Polynomial.X, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro x; simp

/-- Faithful impossibility: the functional equation forces `p(1) ∈ {0,1}`, so `p(1) = 2`
is impossible. -/
theorem p09 :
    ¬ ∃ p : Polynomial ℝ,
      Polynomial.eval 0 p = 0 ∧ Polynomial.eval 1 p = 2 ∧
        ∀ x : ℝ, (Polynomial.eval x p) ^ 2 = Polynomial.eval (x ^ 2) p := by
  rintro ⟨p, -, h1, hfe⟩
  have h := hfe 1
  simp only [one_pow] at h
  rw [h1] at h
  norm_num at h

/-- **Full classification of `p(x)² = p(x²)` over `ℝ[X]`.** A real polynomial `p` satisfies
`p(x)² = p(x²)` for every real `x` if and only if `p = 0` or `p = Xⁿ` for some `n : ℕ`. -/
theorem p09_classification (p : Polynomial ℝ) :
    (∀ x : ℝ, (Polynomial.eval x p) ^ 2 = Polynomial.eval (x ^ 2) p)
      ↔ p = 0 ∨ ∃ n : ℕ, p = X ^ n := by
  constructor
  · intro hfe
    -- Upgrade the pointwise functional equation to a polynomial identity (`ℝ` is infinite).
    have hpoly : p ^ 2 = expand ℝ 2 p := by
      apply Polynomial.funext
      intro x
      rw [eval_pow, expand_eval]
      exact hfe x
    rcases eq_or_ne p 0 with hp0 | hp0
    · exact Or.inl hp0
    refine Or.inr ⟨p.natDegree, ?_⟩
    set n := p.natDegree with hn
    -- The leading coefficient satisfies `a² = a`, and being nonzero forces `a = 1`.
    have hane : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
    have hlc2 : p.leadingCoeff ^ 2 = p.leadingCoeff := by
      have h := congrArg Polynomial.leadingCoeff hpoly
      rw [leadingCoeff_pow' (pow_ne_zero 2 hane),
        leadingCoeff_expand (by norm_num : (0 : ℕ) < 2)] at h
      exact h
    have hlc : p.leadingCoeff = 1 := by
      have hfac : p.leadingCoeff * (p.leadingCoeff - 1) = 0 := by linear_combination hlc2
      rcases mul_eq_zero.mp hfac with h | h
      · exact absurd h hane
      · exact sub_eq_zero.mp h
    -- Suppose `p ≠ Xⁿ`; the deviation `d := p - Xⁿ` is nonzero with smaller degree.
    by_contra hne
    have hdeg_p : p.degree = (n : WithBot ℕ) := degree_eq_natDegree hp0
    have hdeg_eq : p.degree = (X ^ n : ℝ[X]).degree := by rw [hdeg_p, degree_X_pow]
    have hlc_eq : p.leadingCoeff = (X ^ n : ℝ[X]).leadingCoeff := by
      rw [hlc, leadingCoeff_X_pow]
    have hsub : (p - X ^ n).degree < p.degree := degree_sub_lt hdeg_eq hp0 hlc_eq
    have hdeg_d : (p - X ^ n).degree < (n : WithBot ℕ) := by rwa [hdeg_p] at hsub
    set d := p - X ^ n with hd_def
    have hpeq : p = X ^ n + d := by rw [hd_def]; ring
    have hdne : d ≠ 0 := by
      rw [hd_def]
      intro h
      exact hne (sub_eq_zero.mp h)
    set k := d.natDegree with hk
    have hkn : k < n := by
      rw [hk]
      exact (natDegree_lt_iff_degree_lt hdne).mpr hdeg_d
    have ha_ne : d.coeff k ≠ 0 := by
      rw [hk]
      exact leadingCoeff_ne_zero.mpr hdne
    -- Coefficient bookkeeping for `p² = (Xⁿ + d)²` at index `n + k`.
    have e1 : ((X ^ n : ℝ[X]) * X ^ n).coeff (n + k) = 0 := by
      rw [← pow_add, coeff_X_pow, if_neg (by omega)]
    have e2 : ((X ^ n : ℝ[X]) * d).coeff (n + k) = d.coeff k := by
      rw [add_comm n k, coeff_X_pow_mul]
    have e3 : (d * X ^ n).coeff (n + k) = d.coeff k := by
      rw [add_comm n k, coeff_mul_X_pow]
    have e4 : (d * d).coeff (n + k) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have hle : (d * d).natDegree ≤ d.natDegree + d.natDegree := natDegree_mul_le
      rw [← hk] at hle
      omega
    have hLHS : (p ^ 2).coeff (n + k) = d.coeff k + d.coeff k := by
      rw [sq, hpeq, mul_add, add_mul, add_mul, coeff_add, coeff_add, coeff_add,
        e1, e2, e3, e4]
      ring
    -- The right-hand side `expand ℝ 2 p` has vanishing coefficient at `n + k`.
    have hRHS : (expand ℝ 2 p).coeff (n + k) = 0 := by
      rw [coeff_expand (by norm_num : (0 : ℕ) < 2)]
      split_ifs with hdvd
      · have hm_ne : (n + k) / 2 ≠ n := by omega
        rw [hpeq, coeff_add, coeff_X_pow, if_neg hm_ne, zero_add]
        exact coeff_eq_zero_of_natDegree_lt (by rw [← hk]; omega)
      · rfl
    have hsum : d.coeff k + d.coeff k = 0 := by
      have hkey : (p ^ 2).coeff (n + k) = (expand ℝ 2 p).coeff (n + k) := by rw [hpoly]
      rw [hLHS, hRHS] at hkey
      exact hkey
    exact ha_ne (by linarith)
  · rintro (rfl | ⟨n, rfl⟩)
    · intro x
      rw [eval_zero, eval_zero]
      ring
    · intro x
      simp only [eval_pow, eval_X]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm n 2]

end Lutar.Putnam.Sampler
