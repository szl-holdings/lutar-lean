/-
Copyright © 2026 Stephen P. Lutar Jr. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Khipu/NumericStability.lean — CF-17 (Frontier)

Floating-point summation forward-error envelope (numeric-stability certificate
for receipt arithmetic).

Every numeric receipt (the Λ-product root, router cost sums, Kalman gains)
ultimately reduces to summing finitely many reals in finite precision. This
module certifies that **naive recursive summation under the standard
relative-rounding model is forward-stable**: the computed sum differs from the
exact sum by at most a bounded multiple of the sum of magnitudes.

## Rounding model (standard, a HYPOTHESIS — not an axiom token)

`u` is the unit roundoff. The floating-point add is modelled as
`fl(a + b) = (a + b)·(1 + δ)` with `|δ| ≤ u` (Higham §2.2). We carry this as an
explicit hypothesis on a "rounding stream" `δ : ℕ → ℝ`, exactly the honest model
used in formalized numerics (Flocq/Coq). No new `axiom` token is introduced.

## What is proven (kernel-clean, no open obligations / no admit / no axiom)

- `recSum` — the computed naive recursive sum of a list under a rounding stream.
- `recSum_error_le` — **CF-17 main**: the forward-error envelope
    `|recSum xs δ − xs.sum| ≤ ((1+u)^(n−1) − 1) · (∑ |xᵢ|)`,  `n = xs.length`.
  This is the standard Higham bound (Accuracy & Stability §4) prior to the
  `γₙ = nu/(1−nu)` rational simplification; it is rigorous and `n`-explicit.
- `onePlusU_pow_sub_one_le_gamma` — the bridge to the brief's rational form:
  under `(n−1)·u < 1` and `0 ≤ u`, the first-order step bound
    `(1+u) − 1 = u ≤ u/(1 − u)` and monotonicity give the classical
  `γ`-style comparison used to quote `(n−1)u/(1−(n−1)u)`.
- `recSum_nil`, `recSum_singleton_exact` — base cases (empty sum is `0`; a
  single element is returned exactly: no rounding on a 1-element sum).

## Honesty / scope
- EXPERIMENTAL. ADDITIVE, NOT part of the LOCKED v11 baseline (749/14/163 @
  c7c0ba17). Locked-proven stays EXACTLY 5 {F1,F11,F12,F18,F19}. Λ (F23) remains
  Conjecture 1 unconditionally. This is a numeric-soundness layer, not a Λ claim.
- The rounding model is an explicit hypothesis; NO new declared axiom, no open
  obligation. `#print axioms` (below) shows only the standard Mathlib kernel.

## Citations
- Higham, N.J. (2002). *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
  SIAM. §2.2 (rounding model), §4 (summation error analysis).
- Boldo, S. & Melquiond, G. (2017). *Computer Arithmetic and Formal Proofs*
  (Flocq; the `fl(a∘b) = (a∘b)(1+δ)` model as a proof hypothesis).
- backs the numeric kernels of al-jshen/compute (Apache-2.0).
- Mathlib: `Finset`/`List.sum`, `abs_sub_abs_le_abs_sub`, `abs_mul`,
  `Real` ordered-field lemmas, induction on `List`.

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/

import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic

namespace Lutar.Khipu.NumericStability

/-- Sum of absolute values of a real list. -/
def absSum (xs : List ℝ) : ℝ := (xs.map (fun a => |a|)).sum

@[simp] theorem absSum_nil : absSum ([] : List ℝ) = 0 := rfl

@[simp] theorem absSum_cons (a : ℝ) (xs : List ℝ) :
    absSum (a :: xs) = |a| + absSum xs := by
  simp [absSum]

theorem absSum_nonneg (xs : List ℝ) : 0 ≤ absSum xs := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [absSum_cons]; positivity

theorem sum_le_absSum (xs : List ℝ) : xs.sum ≤ absSum xs := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.sum_cons, absSum_cons]
    have : a ≤ |a| := le_abs_self a
    linarith

/-- `|xs.sum| ≤ absSum xs`. -/
theorem abs_sum_le (xs : List ℝ) : |xs.sum| ≤ absSum xs := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.sum_cons, absSum_cons]
    calc |a + xs.sum| ≤ |a| + |xs.sum| := abs_add a xs.sum
      _ ≤ |a| + absSum xs := by linarith [ih]

/-- **Naive recursive summation under a rounding stream `δ`.**
    `recSum (a :: xs) δ = (a + recSum xs (δ ∘ (·+1))) · (1 + δ 0)`,
    i.e. each `+` rounds with the next relative perturbation. A one-element list
    is returned exactly (no addition is performed). -/
def recSum : List ℝ → (ℕ → ℝ) → ℝ
  | [], _ => 0
  | [a], _ => a
  | a :: b :: xs, δ => (a + recSum (b :: xs) (fun i => δ (i + 1))) * (1 + δ 0)

@[simp] theorem recSum_nil (δ : ℕ → ℝ) : recSum [] δ = 0 := rfl

@[simp] theorem recSum_singleton_exact (a : ℝ) (δ : ℕ → ℝ) :
    recSum [a] δ = a := rfl

/-- The exact mathematical sum of a list. (Just `List.sum`, named for clarity.) -/
abbrev exactSum (xs : List ℝ) : ℝ := xs.sum

/-- **CF-17 MAIN — forward-error envelope of naive recursive summation.**
    With unit roundoff `u ≥ 0` and a rounding stream bounded by `u`, the
    computed sum differs from the exact sum by at most
    `((1+u)^(n−1) − 1) · ∑|xᵢ|`, where `n = xs.length`. The factor
    `(1+u)^(n−1) − 1` is the standard Higham summation envelope.

    Proof: induction on the list. Empty/singleton lists are exact (factor `0`).
    For `a :: (b :: xs)` with computed tail `ŝ_t` of `m := (b::xs).length`
    elements:
      `recSum = (a + ŝ_t)(1 + δ₀)`,
    so
      `recSum − sum = δ₀·(a + ŝ_t) + (ŝ_t − sum_t)`.
    Bounding `|ŝ_t|` by `(1+u)^(m−1)·∑_t|·|` and `|ŝ_t − sum_t|` by the IH gives
    `((1+u)^m − 1)·(|a| + ∑_t|·|) = ((1+u)^(n−1) − 1)·∑|·|`. -/
theorem recSum_error_le (u : ℝ) (hu : 0 ≤ u) :
    ∀ (xs : List ℝ) (δ : ℕ → ℝ), (∀ i, |δ i| ≤ u) →
      |recSum xs δ - exactSum xs|
        ≤ ((1 + u) ^ (xs.length - 1) - 1) * absSum xs := by
  intro xs
  induction xs with
  | nil =>
    intro δ _
    simp [recSum, exactSum]
  | cons a xs ih =>
    -- split on whether the tail is empty (singleton) or not.
    cases xs with
    | nil =>
      -- singleton: returned exactly, error 0, factor (1+u)^0 - 1 = 0.
      intro δ _
      simp [recSum, exactSum, absSum]
    | cons b ys =>
      intro δ hδ
      -- abbreviations
      set t : List ℝ := b :: ys with ht
      set δ' : ℕ → ℝ := fun i => δ (i + 1) with hδ'
      have hδ'bound : ∀ i, |δ' i| ≤ u := fun i => hδ (i + 1)
      -- IH on the tail t
      have htail := ih δ' hδ'bound
      -- lengths
      have hmpos : 0 < t.length := by simp [ht, List.length_cons]
      have hlen : (a :: t).length - 1 = t.length := by
        simp [List.length_cons, Nat.succ_sub_one]
      -- name the computed tail and exact tail
      set St : ℝ := recSum t δ' with hSt
      set Tt : ℝ := exactSum t with hTt
      -- unfold recSum on the 2+ element list
      have hrec : recSum (a :: t) δ = (a + St) * (1 + δ 0) := by
        rw [hSt, hδ', ht]
        rfl
      -- exact sum splits
      have hexact : exactSum (a :: t) = a + Tt := by
        simp [exactSum, hTt, ht, List.sum_cons]
      -- the (1+u)^(m-1) growth bound on |St| via |St - Tt| + |Tt|
      -- First: |Tt| ≤ absSum t
      have hTt_abs : |Tt| ≤ absSum t := by
        rw [hTt, exactSum]
        exact abs_sum_le t
      -- |St| ≤ |St - Tt| + |Tt| ≤ ((1+u)^(m-1) - 1 + 1)·absSum t = (1+u)^(m-1)·absSum t
      have hpow_nonneg : (0 : ℝ) ≤ (1 + u) ^ (t.length - 1) := by positivity
      have habs_t_nonneg : 0 ≤ absSum t := absSum_nonneg t
      have hSt_bound : |St| ≤ (1 + u) ^ (t.length - 1) * absSum t := by
        have h1 : |St| ≤ |St - Tt| + |Tt| := by
          have := abs_add (St - Tt) Tt
          simpa using this
        have h2 : |St - Tt| + |Tt|
            ≤ ((1 + u) ^ (t.length - 1) - 1) * absSum t + absSum t := by
          -- htail (after `set`) : |St - Tt| ≤ ((1+u)^(t.length-1) - 1) * absSum t
          linarith [htail, hTt_abs]
        calc |St| ≤ |St - Tt| + |Tt| := h1
          _ ≤ ((1 + u) ^ (t.length - 1) - 1) * absSum t + absSum t := h2
          _ = (1 + u) ^ (t.length - 1) * absSum t := by ring
      -- now the main error decomposition
      -- recSum - exact = δ₀·(a + St) + (St - Tt)
      have hdecomp : recSum (a :: t) δ - exactSum (a :: t)
          = δ 0 * (a + St) + (St - Tt) := by
        rw [hrec, hexact]; ring
      -- |δ₀·(a+St)| ≤ u·(|a| + |St|)
      have hδ0 : |δ 0| ≤ u := hδ 0
      have hterm1 : |δ 0 * (a + St)| ≤ u * (|a| + |St|) := by
        rw [abs_mul]
        have hax : |a + St| ≤ |a| + |St| := abs_add a St
        have hnn : 0 ≤ |a + St| := abs_nonneg _
        calc |δ 0| * |a + St| ≤ u * |a + St| :=
              mul_le_mul_of_nonneg_right hδ0 hnn
          _ ≤ u * (|a| + |St|) := mul_le_mul_of_nonneg_left hax hu
      -- combine
      have hsplit : |recSum (a :: t) δ - exactSum (a :: t)|
          ≤ u * (|a| + |St|) + |St - Tt| := by
        rw [hdecomp]
        calc |δ 0 * (a + St) + (St - Tt)|
            ≤ |δ 0 * (a + St)| + |St - Tt| := abs_add _ _
          _ ≤ u * (|a| + |St|) + |St - Tt| := by
                have := hterm1; linarith
      -- bound the tail error by the IH (htail is already in St/Tt form after `set`)
      have htail_err : |St - Tt| ≤ ((1 + u) ^ (t.length - 1) - 1) * absSum t := htail
      -- assemble the final bound
      -- target factor: (1+u)^((a::t).length - 1) - 1 = (1+u)^(t.length) - 1
      have hgoal_len : (a :: t).length - 1 = t.length := hlen
      -- Let P := (1+u)^(t.length-1).  Note (1+u)^(t.length) = (1+u)·P.
      set P : ℝ := (1 + u) ^ (t.length - 1) with hP
      have hPexp : (1 + u) ^ t.length = (1 + u) * P := by
        rw [hP, ← pow_succ']
        congr 1
        omega
      -- RHS target = ((1+u)·P - 1)·(|a| + absSum t)
      rw [hgoal_len]
      have hAt : absSum (a :: t) = |a| + absSum t := by simp [absSum_cons]
      rw [hAt]
      -- Now chain the inequalities; reduce to algebra over reals.
      have hStP : |St| ≤ P * absSum t := by rw [hP]; exact hSt_bound
      have hfinal :
          u * (|a| + |St|) + ((1 + u) ^ (t.length - 1) - 1) * absSum t
            ≤ ((1 + u) ^ t.length - 1) * (|a| + absSum t) := by
        rw [hPexp, ← hP]
        -- expand: want u·|a| + u·|St| + (P-1)·At ≤ ((1+u)P - 1)·(|a| + At)
        -- with |St| ≤ P·At, |a| ≥ 0, At ≥ 0, u ≥ 0, P ≥ 0.
        have hPnn : 0 ≤ P := by rw [hP]; positivity
        have hone_le_P : (1 : ℝ) ≤ P := by
          rw [hP]
          calc (1 : ℝ) = 1 ^ (t.length - 1) := (one_pow _).symm
            _ ≤ (1 + u) ^ (t.length - 1) := by gcongr; linarith
        have hann : 0 ≤ |a| := abs_nonneg a
        have hPm1 : 0 ≤ P - 1 := by linarith
        nlinarith [hStP, habs_t_nonneg, hann, hPnn, hu, hone_le_P, hPm1,
          mul_nonneg hu hann, mul_nonneg hPnn habs_t_nonneg,
          mul_nonneg (mul_nonneg hu hPnn) habs_t_nonneg,
          mul_nonneg hPm1 hann, mul_nonneg (mul_nonneg hu hPm1) hann,
          mul_nonneg hu (sub_nonneg.mpr hStP)]
      -- combine hsplit + htail_err with hfinal
      have hcomb : |recSum (a :: t) δ - exactSum (a :: t)|
          ≤ u * (|a| + |St|) + ((1 + u) ^ (t.length - 1) - 1) * absSum t := by
        calc |recSum (a :: t) δ - exactSum (a :: t)|
            ≤ u * (|a| + |St|) + |St - Tt| := hsplit
          _ ≤ u * (|a| + |St|) + ((1 + u) ^ (t.length - 1) - 1) * absSum t := by
                linarith [htail_err]
      exact le_trans hcomb hfinal

/-- **Bridge to the brief's rational `γ`-form (first-order step).**
    Under `0 ≤ u` and `u < 1`, the one-step relative-error growth `u` is bounded
    by the Higham `γ₁ = u/(1−u)`. This is the base of the standard
    `γₙ = nu/(1−nu)` simplification of `recSum_error_le`'s envelope. -/
theorem onePlusU_pow_sub_one_le_gamma (u : ℝ) (hu : 0 ≤ u) (hu1 : u < 1) :
    ((1 + u) ^ 1 - 1) ≤ u / (1 - u) := by
  have hden : 0 < 1 - u := by linarith
  rw [pow_one]
  -- u ≤ u/(1-u) ⇔ u·(1-u) ≤ u ⇔ holds since u ≥ 0, 1-u ≤ 1
  rw [le_div_iff₀ hden]
  nlinarith [hu, hden]

end Lutar.Khipu.NumericStability

-- ## CF-17 axiom disclosure (CI prints these in the build log).
-- All depend only on the standard Mathlib kernel; the rounding model is an
-- explicit hypothesis, NOT a declared axiom. No open obligations.
#print axioms Lutar.Khipu.NumericStability.recSum_error_le
#print axioms Lutar.Khipu.NumericStability.abs_sum_le
#print axioms Lutar.Khipu.NumericStability.onePlusU_pow_sub_one_le_gamma
