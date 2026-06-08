/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Round 13 — CUT-2 / CF-11: axiom-free CONDITIONAL Λ-uniqueness under slice-multiplicativity

This file ships the **maximal honest closure that is also turnkey in Lean today** for the
Λ-uniqueness program: every supporting lemma is already proved in
`Round13/CauchyND_Closure.lean` and `Round13/Lambda_Uniqueness.lean`.

## What is PROVEN here (no open obligations / no admit / NO new `axiom` token)

* **`lambda_unique_of_separable`** — the CUT-2 theorem. Any A1–A5 aggregator `Φ` whose
  per-axis slices `fᵢ` are multiplicative (`fᵢ(s·t) = fᵢ(s)·fᵢ(t)`, `fᵢ(1)=1`), monotone,
  and which *separates* (`Φ x = ∏ᵢ fᵢ(xᵢ)`) **equals `Λ k`**.

  This is strictly MORE ATOMIC / WEAKER than the existing `Factors Φ αs` premise (which
  presupposes the exponential shape `Φ x = ∏ xᵢ^αᵢ`): here we assume only that each slice is
  multiplicative, and we *derive* the exponents and the product form, via the already-proved
  `multiplicative_monotone_isPow_pos`.

## Proof assembly (every step has a named in-tree lemma)
1. Per axis `i`: `multiplicative_monotone_isPow_pos (hmul i) (hmono i) (hone i)` ⇒ a power-law
   exponent `αᵢ` with `fᵢ t = t^αᵢ` for `t ≠ 0`. (PROVED in-tree.)
2. The boundary `t = 0` is closed here. Each `fᵢ(0)` is idempotent (`fᵢ(0)=fᵢ(0)²`) hence `0`
   or `1`. If `fᵢ(0)=1` the slice is constant `1`, forcing the matching exponent `αᵢ=0`, and
   `(0:ℝ≥0)^0 = 1 = fᵢ 0`. If `fᵢ(0)=0`, A5 symmetry (lifted through `hsep`) forces all
   exponents equal so `αᵢ ≠ 0`, giving `(0:ℝ≥0)^(αᵢ) = 0 = fᵢ 0`. Either way the boundary
   factor matches, upgrading the positive-only power law to `Factors Φ αs`.
3. `lambda_unique_of_factors hk Φ hL αs hfac` ⇒ `Φ = Λ k`. (PROVED in-tree; internally re-pins
   every `αᵢ = 1/k` via `exponents_equal_inv_k_of_symm`.)

## Honesty / scope
- CUT-2 is a theorem **CONDITIONAL on `{A1, A2, A3, A5, slice-multiplicativity}`**, discharged
  through Mathlib + in-tree lemmas, with **NO new `axiom` token** (unlike any A6-bisymmetry
  variant). The UNCONDITIONAL statement `lambda_unique` remains **FALSE** under A1–A5
  (`maxAgg`, `min` are counterexamples — see `Lambda_Uniqueness.maxAgg_ne_Lambda`).
- Λ therefore stays **Conjecture 1 unconditionally**. F23 now carries a proven, axiom-free
  conditional core. Locked-proven set is unchanged.

## References
- Aczél, J. (1966). *Lectures on Functional Equations.* Academic Press. §5.1.
- Hardy, G.H., Littlewood, J.E., Pólya, G. (1934). *Inequalities.* §2.18.
- Maksa, Gy. (2000). On the bisymmetry/separability representation of means.

Signed-off-by: SZL CTO <cto@szl-holdings.com>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/
import Lutar.Axioms
import Lutar.Invariant
import Lutar.Round13.CauchyND_Closure
import Lutar.Round13.Lambda_Uniqueness
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Lutar.Round13

open NNReal Real BigOperators

/-! ## CUT-2 / CF-11 — slice-multiplicativity ⇒ Λ (axiom-free conditional uniqueness) -/

/-- A multiplicative slice value at `0` is idempotent, hence `0` or `1`. -/
private lemma slice_zero_idem {g : NNReal → NNReal}
    (hg : ∀ s t, g (s * t) = g s * g t) : g 0 = 0 ∨ g 0 = 1 := by
  have h : g 0 = g 0 * g 0 := by simpa using hg 0 0
  rcases eq_or_ne (g 0) 0 with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (mul_right_cancel₀ h0 (by rw [one_mul]; exact h.symm))

/-- If a multiplicative slice has `g 0 = 1`, it is constant `1` on all of `ℝ≥0`. -/
private lemma slice_const_one_of_zero_one {g : NNReal → NNReal}
    (hg : ∀ s t, g (s * t) = g s * g t) (h0 : g 0 = 1) : ∀ t, g t = 1 := by
  intro t
  have : g 0 = g 0 * g t := by simpa using hg 0 t
  rw [h0, one_mul] at this
  exact this.symm

/-- `2 ^ (r : ℝ) = 1` (in ℝ≥0) forces `r = 0`, via the in-tree `rpow_left_inj_one_lt`. -/
private lemma rpow_two_eq_one_iff {r : ℝ} (h : (2 : NNReal) ^ r = 1) : r = 0 := by
  have h2 : (1 : NNReal) < 2 := one_lt_two
  have : (2 : NNReal) ^ r = (2 : NNReal) ^ (0 : ℝ) := by rw [NNReal.rpow_zero]; exact h
  exact rpow_left_inj_one_lt h2 this

/-- **CUT-2 / CF-11 — `lambda_unique_of_separable`.**

    Any A1–A5 aggregator `Φ` whose per-axis slices `fᵢ` are multiplicative, monotone, with
    `fᵢ(1)=1`, and which separates as `Φ x = ∏ᵢ fᵢ(xᵢ)`, equals the Lutar invariant `Λ k`.

    Strictly weaker hypothesis than the `Factors` premise: we *derive* the exponential shape
    from slice-multiplicativity (`multiplicative_monotone_isPow_pos`) rather than assuming it.
    NO new axiom; the unconditional uniqueness statement remains FALSE. -/
theorem lambda_unique_of_separable {k : ℕ} (hk : 0 < k)
    (Φ : Aggregator k) (hL : LutarAxioms Φ)
    (f : Fin k → (NNReal → NNReal))
    (hsep  : ∀ x, Φ x = ∏ i, f i (x i))
    (hmul  : ∀ i s t, f i (s * t) = f i s * f i t)
    (hone  : ∀ i, f i 1 = 1)
    (hmono : ∀ i, Monotone (f i)) :
    Φ = Λ k := by
  classical
  -- Step 1: per-axis power law on the positives.
  have hpow : ∀ i, ∃ α : NNReal, ∀ t : NNReal, t ≠ 0 → f i t = t ^ (α : ℝ) :=
    fun i => multiplicative_monotone_isPow_pos (hmul i) (hmono i) (hone i)
  choose αs hαs using hpow
  -- evaluation of the power law at base `4` and `2`.
  have htwo : ∀ i, f i 2 = (2 : NNReal) ^ (αs i : ℝ) := fun i => hαs i 2 (by norm_num)
  have hfour : ∀ i, f i 4 = (4 : NNReal) ^ (αs i : ℝ) := fun i => hαs i 4 (by norm_num)
  -- A "two-hot" evaluation helper: a product whose entries are all `1` except at two indices.
  have two_hot :
      ∀ (i j : Fin k) (_ : i ≠ j) (a b : NNReal),
        (∏ l, (fun l => if l = i then a else if l = j then b else (1 : NNReal)) l)
          = a * b := by
    intro i j hij a b
    have hmem : i ∈ (Finset.univ.erase j) := Finset.mem_erase.2 ⟨hij, Finset.mem_univ i⟩
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
        ← Finset.mul_prod_erase _ _ hmem]
    have hrest : (∏ l ∈ (Finset.univ.erase j).erase i,
        (fun l => if l = i then a else if l = j then b else (1 : NNReal)) l) = 1 := by
      apply Finset.prod_eq_one
      intro l hl
      have hli : l ≠ i := (Finset.mem_erase.1 hl).1
      have hlj : l ≠ j := (Finset.mem_erase.1 (Finset.mem_erase.1 hl).2).1
      simp [hli, hlj]
    -- the j-factor and i-factor:
    have hjf : (if j = i then a else if j = j then b else (1 : NNReal)) = b := by
      simp [hij.symm]
    have hif : (if i = i then a else if i = j then b else (1 : NNReal)) = a := by simp
    rw [hjf, hif, hrest]
    ring
  -- Step 2: all exponents are equal, via A5 symmetry lifted through `hsep`.
  have hαeq : ∀ i j : Fin k, αs i = αs j := by
    intro i j
    rcases eq_or_ne i j with hij | hij
    · rw [hij]
    -- test vector: 4 at i, 2 at j, 1 elsewhere.
    set x : Axes k := fun l => if l = i then (4 : NNReal) else if l = j then 2 else 1 with hx
    set σ : Equiv.Perm (Fin k) := Equiv.swap i j with hσ
    have hA5 := hL.A5 x σ
    rw [hsep, hsep] at hA5
    -- LHS product (swapped input): (x∘σ) i = x j = 2, (x∘σ) j = x i = 4, rest 1.
    have hxcomp : ∀ l, (x ∘ σ) l
        = (fun l => if l = i then (2 : NNReal) else if l = j then 4 else 1) l := by
      intro l
      simp only [Function.comp, hσ, hx]
      rcases eq_or_ne l i with hli | hli
      · subst hli
        rw [Equiv.swap_apply_left]
        simp [hij, hij.symm]
      · rcases eq_or_ne l j with hlj | hlj
        · subst hlj
          rw [Equiv.swap_apply_right]
          simp [hij, hij.symm]
        · rw [Equiv.swap_apply_of_ne_of_ne hli hlj]
          simp [hli, hlj]
    have hxself : ∀ l, x l
        = (fun l => if l = i then (4 : NNReal) else if l = j then 2 else 1) l := by
      intro l; simp [hx]
    -- rewrite both products into the slice values, then to powers of the base.
    have hLHS : (∏ l, f l ((x ∘ σ) l)) = f i 2 * f j 4 := by
      rw [Finset.prod_congr rfl (fun l _ => by rw [hxcomp l])]
      -- now product of `f l (if l=i then 2 else if l=j then 4 else 1)`
      have : (∏ l, f l (if l = i then (2:NNReal) else if l = j then 4 else 1))
          = ∏ l, (fun l => if l = i then f i 2 else if l = j then f j 4 else (1:NNReal)) l := by
        apply Finset.prod_congr rfl
        intro l _
        rcases eq_or_ne l i with hli | hli
        · subst hli; simp
        · rcases eq_or_ne l j with hlj | hlj
          · subst hlj; simp [hli]
          · simp [hli, hlj, hone l]
      rw [this, two_hot i j hij (f i 2) (f j 4)]
    have hRHS : (∏ l, f l (x l)) = f i 4 * f j 2 := by
      rw [Finset.prod_congr rfl (fun l _ => by rw [hxself l])]
      have : (∏ l, f l (if l = i then (4:NNReal) else if l = j then 2 else 1))
          = ∏ l, (fun l => if l = i then f i 4 else if l = j then f j 2 else (1:NNReal)) l := by
        apply Finset.prod_congr rfl
        intro l _
        rcases eq_or_ne l i with hli | hli
        · subst hli; simp
        · rcases eq_or_ne l j with hlj | hlj
          · subst hlj; simp [hli]
          · simp [hli, hlj, hone l]
      rw [this, two_hot i j hij (f i 4) (f j 2)]
    rw [hLHS, hRHS] at hA5
    -- f i 2 * f j 4 = f i 4 * f j 2, expand to powers of 2.
    rw [htwo i, hfour j, hfour i, htwo j] at hA5
    -- (2^αᵢ)(4^αⱼ) = (4^αᵢ)(2^αⱼ);  4 = 2^2.
    have h4 : (4 : NNReal) = (2 : NNReal) ^ (2 : ℝ) := by
      rw [show (4:NNReal) = (2:NNReal)^(2:ℕ) by norm_num, ← NNReal.rpow_natCast]; norm_num
    rw [h4] at hA5
    -- collapse exponents: 2^(αᵢ + 2αⱼ) = 2^(2αᵢ + αⱼ)
    rw [← NNReal.rpow_mul, ← NNReal.rpow_mul, ← NNReal.rpow_add (by norm_num),
        ← NNReal.rpow_add (by norm_num)] at hA5
    have hbase : ((αs i : ℝ) + (2:ℝ) * (αs j : ℝ)) = ((2:ℝ) * (αs i : ℝ) + (αs j : ℝ)) :=
      rpow_left_inj_one_lt (one_lt_two) hA5
    -- αᵢ + 2αⱼ = 2αᵢ + αⱼ ⇒ αᵢ = αⱼ (as reals, then NNReal).
    have hreal : (αs i : ℝ) = (αs j : ℝ) := by linarith [hbase]
    exact NNReal.coe_injective hreal
  -- Step 3: each `f i 0` equals `(0)^(αs i)`; via the dichotomy + exponent equality.
  have hf0 : ∀ i, f i 0 = (0 : NNReal) ^ (αs i : ℝ) := by
    intro i
    rcases slice_zero_idem (hmul i) with h0 | h1
    · -- f i 0 = 0; need αᵢ ≠ 0 so that 0^αᵢ = 0.
      rw [h0]
      -- αᵢ ≠ 0: otherwise the slice is constant 1 on positives, but exponent-equality with a
      -- positive axis (if any) would make every exponent 0, contradicting ∑ αₗ = 1 via A3.
      have hαne : (αs i : ℝ) ≠ 0 := by
        intro hzero
        -- if αᵢ = 0 then by hαeq all αₗ = 0; but ∏ f l 2 = 2 (A3) forces ∑ αₗ = 1.
        have hdiag2 : (∏ l, f l (2:NNReal)) = 2 := by
          have := (hsep (fun _ => (2:NNReal))).symm
          rw [hL.A3.A3_normalize 2] at this; simpa using this
        -- ∏ f l 2 = ∏ 2^αₗ = 2^(∑αₗ); each αₗ = αᵢ = 0 ⇒ = 2^0 = 1 ≠ 2.
        have hall0 : ∀ l, (αs l : ℝ) = 0 := by
          intro l; have := hαeq l i; rw [this]; exact hzero
        have hprodone : (∏ l, f l (2:NNReal)) = 1 := by
          rw [Finset.prod_congr rfl (fun l _ => htwo l)]
          apply Finset.prod_eq_one
          intro l _; rw [hall0 l, NNReal.rpow_zero]
        rw [hprodone] at hdiag2
        exact (by norm_num : (1:NNReal) ≠ 2) hdiag2
      rw [NNReal.zero_rpow hαne]
    · -- f i 0 = 1; the slice is constant 1, forcing αᵢ = 0 so 0^0 = 1.
      have hc1 := slice_const_one_of_zero_one (hmul i) h1
      have hα0 : (αs i : ℝ) = 0 := rpow_two_eq_one_iff (by rw [← htwo i]; exact hc1 2)
      rw [h1, hα0, NNReal.rpow_zero]
  -- Step 4: assemble `Factors Φ αs` and discharge via the in-tree terminal theorem.
  have hfac : Factors Φ αs := by
    intro x
    rw [hsep x]
    apply Finset.prod_congr rfl
    intro i _
    rcases eq_or_ne (x i) 0 with hxi | hxi
    · rw [hxi]; exact hf0 i
    · exact hαs i (x i) hxi
  exact lambda_unique_of_factors hk Φ hL αs hfac

end Lutar.Round13
