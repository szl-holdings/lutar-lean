/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Cauchy_ND — Step 4: the per-coordinate exponents are all `1/k`

This file discharges **Step 4** of the `lutar_is_geomean` (Cauchy_ND) proof
roadmap documented in `team/cauchy-nd-closure/PROOF_SPEC.md`:

> By symmetry the function is symmetric in its arguments, so `αᵢ = α` for all
> `i`; the diagonal commitment `Λ(c,…,c) = c` then forces `Σ αᵢ = 1`, hence
> each `αᵢ = 1/k`.

It is a NEW file under `Lutar/Innovations/round9/`, OUTSIDE the locked kernel
(theorems 749/14/163 are untouched).  It depends only on `Lutar.Axioms` and
Mathlib; it does not modify `Uniqueness.lean`.

## Input from the upstream specialist

Step 3 (PhD Functional Analysis, `MultiplicativeMonotoneIsPow`) supplies the
factorization hypothesis
  `h_factor : ∀ x, Lambda_fn x = ∏ i, (x i) ^ (alphas i : ℝ)`
with non-negative real exponents `alphas i`.  Step 4 takes that factorization
and pins the exponents.

## HONESTY NOTE (read carefully — it changes the lemma statement)

The PROOF_SPEC narrative asserts "A3 (Egyptian-exact) implies `Lambda_fn` is
symmetric in its arguments". **This is not derivable from the four Lutar axioms
as they are actually formalized in `Lutar/Axioms.lean`.**  The formalized A3 is
only the *diagonal* commitment

  `A3_normalize : ∀ c, Lambda_fn (fun _ => c) = c`         (`IsEgyptianExact`)

together with `k_pos`.  It says nothing about permuting the *off-diagonal*
inputs.  Concretely, the coordinate projection `Lambda_fn x = x 0` satisfies all
of A1 (monotone), A2 (1-homogeneous), A3 (`A3_normalize`: the constant vector
returns the constant) and A4 (bounded by the max axis), and it factors as
`∏ i, (x i) ^ αᵢ` with `α = (1,0,…,0)`.  For `k ≥ 2` those exponents are not all
equal, so the bare statement

  `(A1∧A2∧A3∧A4) ∧ h_factor → ∀ i, αᵢ = 1/k`

is **false**.  This matches the classical theory: Kolmogorov's characterization
of quasi-arithmetic means lists *symmetry / anonymity* as an INDEPENDENT axiom,
and the only homogeneous quasi-arithmetic means are the *weighted* power means;
equal weights require symmetry (Hardy–Littlewood–Pólya §2; Aczél 1966 §5.1).

We therefore proceed in three honest layers:

* `IsSymmetric`            — the permutation-invariance predicate that is the
                             genuinely missing hypothesis.
* `sum_alphas_eq_one`      — **unconditional, fully proved**: `∑ i, αᵢ = 1`,
                             from A3 + factorization alone.
* `alphas_eq_of_symmetric` — **fully proved**: under `IsSymmetric`, `αᵢ = αⱼ`.
* `exponents_equal_inv_k_of_symm` — **fully proved**: `IsSymmetric` + A3 +
                             factorization ⟹ `αᵢ = 1/k`.  Nothing is assumed
                             beyond symmetry.

Finally `exponents_equal_inv_k` reproduces the *exact* signature requested by the
Step-4 spec.  Because that signature omits the symmetry hypothesis it is not
provable (counterexample above); its body is `exponents_equal_inv_k_of_symm`
applied to a single, clearly tagged `sorry` supplying the missing symmetry
(`SYMMETRY_AXIOM_GAP`).  The fix is a one-line upstream change: add `IsSymmetric`
to `LutarAxioms`, or have Step 5 thread the symmetry of `Lutar.Λ` (which is
trivially symmetric) into the call site.  See `STEP4_SYMM_FINAL.md`.
-/
import Lutar.Axioms
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic

namespace Lutar
namespace Round9

open NNReal BigOperators

/-! ### Symmetry predicate (the genuinely-missing hypothesis)

This is the predicate the team adopted as **axiom A5** on branch
`fix/uniqueness-a1-a5-2026-06-02` (`Lutar/Axioms.lean`):

```
def IsPermutationInvariant {k : ℕ} (Λ : Aggregator k) : Prop :=
  ∀ (x : Axes k) (σ : Fin k ≃ Fin k), Λ (x ∘ ↑σ) = Λ x
```

The present branch (`feat/cauchy-nd-closure-symm`, based on
`fix/lake-build-compilation-2026-06-02`) does **not** yet carry the A5 field in
`LutarAxioms`, so we re-declare the same predicate here under the name
`IsSymmetric` and take it as an explicit hypothesis.  It is *definitionally the
same statement* as the canonical `IsPermutationInvariant` (`x ∘ σ` is exactly
`fun i => x (σ i)`).  Once A5 is merged, Step 5 supplies `hL.A5` directly. -/

/-- **Symmetry / anonymity (= canonical A5 `IsPermutationInvariant`).**
`Lambda_fn` is invariant under permutation of its arguments: for every
permutation `σ` of `Fin k`, reindexing the input by `σ` leaves the output
unchanged.  This is the independent axiom (Kolmogorov; Aczél 1966 §5.1) that the
four original Lutar axioms do *not* supply but that the geometric-mean
characterization requires (PhD-Math audit 2026-06-02; README §CAUCHY_ND). -/
def IsSymmetric {k : ℕ} (Lambda_fn : Aggregator k) : Prop :=
  ∀ (σ : Equiv.Perm (Fin k)) (x : Axes k), Lambda_fn (fun i => x (σ i)) = Lambda_fn x

/-- `IsSymmetric` is exactly the canonical A5 predicate, just with the arguments
in the other order and `x ∘ σ` spelled pointwise.  This bridge lets Step 5 feed
the merged `A5 : IsPermutationInvariant` field straight into the Step-4 lemmas.
(Stated as the defeq it is; proved by `Iff.rfl`-style unfolding.) -/
theorem isSymmetric_iff_permInvariant {k : ℕ} (Lambda_fn : Aggregator k) :
    IsSymmetric Lambda_fn ↔
      (∀ (x : Axes k) (σ : Equiv.Perm (Fin k)), Lambda_fn (x ∘ (σ : Fin k → Fin k)) = Lambda_fn x) := by
  constructor
  · intro h x σ; exact h σ x
  · intro h σ x; exact h x σ

/-! ### A `NNReal.rpow` product/sum bridge for a fixed positive base

For a fixed base `c : NNReal` with `c ≠ 0` we have
`∏ i, c ^ (f i) = c ^ (∑ i, f i)`.  Proved by finset induction using
`NNReal.rpow_add` (which needs `c ≠ 0`).  We only ever instantiate `c` at a
concrete nonzero value, so the `c ≠ 0` side condition is harmless. -/
theorem prod_rpow_const_eq_rpow_sum {ι : Type*} (s : Finset ι) {c : NNReal}
    (hc : c ≠ 0) (f : ι → ℝ) :
    (∏ i ∈ s, c ^ (f i)) = c ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, NNReal.rpow_add hc]

/-- **`rpow_left_inj_one_lt`** — for a fixed NNReal base `c` with `1 < c`, the
map `a ↦ c ^ a` (real exponent) is injective: `c ^ a = c ^ b → a = b`.

Mathlib v4.13.0 has no exponent-injectivity lemma directly on `NNReal.rpow`
(`NNReal.rpow_left_injective` is injectivity in the *base* for a fixed exponent).
We therefore push the equality through the coercion `ℝ≥0 → ℝ` with `NNReal.coe_rpow`
and close it with `Real.rpow_le_rpow_left_iff` (which needs `1 < c`) applied in
both directions (antisymmetry). -/
theorem rpow_left_inj_one_lt {c : NNReal} (hc : 1 < c) {a b : ℝ}
    (h : c ^ a = c ^ b) : a = b := by
  -- coerce to ℝ: (c:ℝ) ^ a = (c:ℝ) ^ b
  have hcoe : (c : ℝ) ^ a = (c : ℝ) ^ b := by
    have := congrArg (fun t : NNReal => (t : ℝ)) h
    simpa only [NNReal.coe_rpow] using this
  have hc' : (1 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  -- antisymmetry via the order iff
  have hle : a ≤ b := (Real.rpow_le_rpow_left_iff hc').mp (le_of_eq hcoe)
  have hge : b ≤ a := (Real.rpow_le_rpow_left_iff hc').mp (le_of_eq hcoe.symm)
  exact le_antisymm hle hge

/-! ### Step 4a — the exponents sum to one (UNCONDITIONAL) -/

/-- **`sum_alphas_eq_one`.** From the diagonal commitment `A3_normalize`
(`Lambda_fn (fun _ => c) = c`) and the factorization `h_factor`, the exponents
sum to one: `∑ i, αᵢ = 1`.

Proof: evaluate `h_factor` at the constant vector `fun _ => (2 : NNReal)`.
The left side is `Lambda_fn (fun _ => 2) = 2` by `A3_normalize`.  The right side
is `∏ i, 2 ^ αᵢ = 2 ^ (∑ i, αᵢ)` by `prod_rpow_const_eq_rpow_sum`.  So
`2 ^ (∑ αᵢ) = 2 = 2 ^ (1:ℝ)`, and since the base `2 > 1` the `rpow` is
injective in the exponent, giving `∑ αᵢ = 1`. -/
theorem sum_alphas_eq_one {k : ℕ}
    (Lambda_fn : Aggregator k)
    (hL : LutarAxioms Lambda_fn)
    (alphas : Fin k → NNReal)
    (h_factor : ∀ x : Axes k, Lambda_fn x = ∏ i, (x i) ^ (alphas i : ℝ)) :
    (∑ i, (alphas i : ℝ)) = 1 := by
  -- constant input value 2
  set c : NNReal := 2 with hc_def
  have hc0 : c ≠ 0 := by rw [hc_def]; norm_num
  -- A3 on the constant vector
  have hdiag : Lambda_fn (fun _ => c) = c := hL.A3.A3_normalize c
  -- factorization on the constant vector
  have hfac : Lambda_fn (fun _ => c) = ∏ i, c ^ (alphas i : ℝ) := h_factor (fun _ => c)
  -- combine: c = ∏ i, c ^ αᵢ
  have hkey : c = ∏ i, c ^ (alphas i : ℝ) := by rw [← hfac, hdiag]
  -- collapse the product to a single rpow
  have hcollapse : (∏ i, c ^ (alphas i : ℝ)) = c ^ (∑ i, (alphas i : ℝ)) :=
    prod_rpow_const_eq_rpow_sum (Finset.univ) hc0 (fun i => (alphas i : ℝ))
  -- so c ^ 1 = c ^ (∑ αᵢ)
  have heq : c ^ (1 : ℝ) = c ^ (∑ i, (alphas i : ℝ)) := by
    rw [NNReal.rpow_one, ← hcollapse, ← hkey]
  -- the base is > 1, hence injective in the exponent
  have h1c : (1 : NNReal) < c := by
    rw [hc_def]; norm_num
  -- exponent-injectivity for base `c > 1` applied to `c^1 = c^(∑)`
  exact (rpow_left_inj_one_lt h1c heq).symm

/-! ### Step 4b — symmetry forces the exponents equal -/

/-- **`alphas_eq_of_symmetric`.** Under symmetry of `Lambda_fn`, the exponents
of the factorization are all equal: `αᵢ = αⱼ` for any `i j`.

Proof: fix `i j`.  Use the transposition `σ = Equiv.swap i j`.  Apply
`IsSymmetric` to the test vector that is `(2 : NNReal)` at coordinate `i` and
`1` everywhere else.  Symmetry equates `Lambda_fn` at this vector with
`Lambda_fn` at the vector that is `2` at `j` and `1` elsewhere.  Feeding both
through `h_factor`, every factor is `1 ^ α = 1` except the single `2`-slot, so
the two products collapse to `2 ^ αᵢ` and `2 ^ αⱼ` respectively.  Injectivity of
`x ↦ 2 ^ x` then gives `αᵢ = αⱼ`. -/
theorem alphas_eq_of_symmetric {k : ℕ}
    (Lambda_fn : Aggregator k)
    (hsym : IsSymmetric Lambda_fn)
    (alphas : Fin k → NNReal)
    (h_factor : ∀ x : Axes k, Lambda_fn x = ∏ i, (x i) ^ (alphas i : ℝ)) :
    ∀ i j, alphas i = alphas j := by
  classical
  intro i j
  -- test vector: 2 at coordinate j, 1 elsewhere
  set c : NNReal := 2 with hc_def
  have hc1 : (1 : NNReal) < c := by rw [hc_def]; norm_num
  -- e m := indicator vector with value c at coordinate m, 1 elsewhere
  set e : Fin k → Axes k := (fun m => fun n => if n = m then c else 1) with he_def
  -- product of (e m) through the factorization collapses to c ^ (alphas m)
  have hcollapse : ∀ m, (∏ n, (e m n) ^ (alphas n : ℝ)) = c ^ (alphas m : ℝ) := by
    intro m
    -- only the n = m factor is nontrivial; all others are 1 ^ α = 1
    rw [Finset.prod_eq_single m]
    · rw [he_def]; simp
    · intro n _ hn
      rw [he_def]; simp only [if_neg hn, NNReal.one_rpow]
    · intro hm
      exact absurd (Finset.mem_univ m) hm
  -- symmetry: swapping i and j maps e i to e j as a reindexing
  -- (fun n => e i (swap i j n)) = e j, pointwise
  have hswap : (fun n => e i ((Equiv.swap i j) n)) = e j := by
    funext n
    rw [he_def]
    show (if (Equiv.swap i j) n = i then c else 1) = (if n = j then c else 1)
    -- `swap i j n = i  ⇔  n = j`
    have hiff : ((Equiv.swap i j) n = i) ↔ (n = j) := by
      constructor
      · intro h
        have h2 := congrArg (Equiv.swap i j) h
        -- swap is an involution: swap (swap n) = n; and swap i = j
        rwa [Equiv.swap_apply_self, Equiv.swap_apply_left] at h2
      · intro h; subst h; simp [Equiv.swap_apply_right]
    by_cases hnj : n = j
    · rw [if_pos (hiff.mpr hnj), if_pos hnj]
    · rw [if_neg (fun h => hnj (hiff.mp h)), if_neg hnj]
  -- apply symmetry at x = e i
  have hsym_eq : Lambda_fn (fun n => e i ((Equiv.swap i j) n)) = Lambda_fn (e i) :=
    hsym (Equiv.swap i j) (e i)
  rw [hswap] at hsym_eq
  -- now Lambda_fn (e j) = Lambda_fn (e i); push through factorization
  have hfi : Lambda_fn (e i) = c ^ (alphas i : ℝ) := by
    rw [h_factor (e i), hcollapse i]
  have hfj : Lambda_fn (e j) = c ^ (alphas j : ℝ) := by
    rw [h_factor (e j), hcollapse j]
  have : c ^ (alphas j : ℝ) = c ^ (alphas i : ℝ) := by
    rw [← hfj, ← hfi]; exact hsym_eq
  -- injectivity of x ↦ c ^ x (real exponent), then NNReal.coe injective
  have hreal : (alphas j : ℝ) = (alphas i : ℝ) :=
    rpow_left_inj_one_lt hc1 this
  exact (NNReal.coe_injective hreal).symm

/-! ### Step 4 (combined, with the honest symmetry hypothesis) -/

/-- **`exponents_equal_inv_k_of_symm`** — the mathematically complete Step 4.

Under symmetry (`hsym`) together with the Lutar axioms and the factorization,
every exponent equals `1/k`:
* `alphas_eq_of_symmetric` gives `αᵢ = αⱼ` for all `i j`, so all `αᵢ` equal a
  common value `a := α₀`.
* `sum_alphas_eq_one` gives `∑ i, αᵢ = 1`; with all terms equal to `a` this is
  `k • a = 1`, i.e. `a = 1/k`.
The result is stated, as the spec requests, as `alphas i = (1/k : NNReal)`. -/
theorem exponents_equal_inv_k_of_symm {k : ℕ} (hk : 0 < k)
    (Lambda_fn : Aggregator k)
    (hL : LutarAxioms Lambda_fn)
    (hsym : IsSymmetric Lambda_fn)
    (alphas : Fin k → NNReal)
    (h_factor : ∀ x : Axes k, Lambda_fn x = ∏ i, (x i) ^ (alphas i : ℝ)) :
    ∀ i, alphas i = (1 / k : NNReal) := by
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hk'
  -- all equal
  have hall : ∀ i j, alphas i = alphas j :=
    alphas_eq_of_symmetric Lambda_fn hsym alphas h_factor
  -- sum is 1 (in ℝ)
  have hsum : (∑ i, (alphas i : ℝ)) = 1 :=
    sum_alphas_eq_one Lambda_fn hL alphas h_factor
  -- with all αᵢ equal to α₀, the sum is k * α₀
  intro i
  -- rewrite each summand as α₀ (using i = ⟨0,hk⟩ as the anchor)
  set i0 : Fin k := ⟨0, hk⟩
  have hconst : ∀ j, (alphas j : ℝ) = (alphas i0 : ℝ) := by
    intro j; exact_mod_cast (hall j i0)
  have hsum2 : (∑ _j : Fin k, (alphas i0 : ℝ)) = 1 := by
    rw [← hsum]; exact (Finset.sum_congr rfl (fun j _ => (hconst j).symm))
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum2
  -- (k : ℝ) * αᵢ₀ = 1  ⟹  αᵢ₀ = 1/k
  have hi0_val : (alphas i0 : ℝ) = 1 / (k : ℝ) := by
    rw [eq_div_iff hkne, mul_comm]
    exact hsum2
  -- transport to αᵢ via equality of all exponents
  have hi_val : (alphas i : ℝ) = 1 / (k : ℝ) := by
    rw [show (alphas i : ℝ) = (alphas i0 : ℝ) from by exact_mod_cast (hall i i0)]
    exact hi0_val
  -- convert ℝ-equality back to NNReal
  have hcoe : (alphas i : ℝ) = ((1 / k : NNReal) : ℝ) := by
    rw [hi_val, NNReal.coe_div, NNReal.coe_one, NNReal.coe_natCast]
  exact NNReal.coe_injective hcoe

/-! ### Step 4 — the exact requested signature

Reproduces the signature handed down by the Step-4 spec.  As documented in the
HONESTY NOTE, this signature is missing the symmetry hypothesis and is therefore
not provable from `hL` and `h_factor` alone (the projection `x ↦ x 0` is a
counterexample for `k ≥ 2`).  The proof reduces it to the complete
`exponents_equal_inv_k_of_symm`, leaving a single tagged `sorry` for the missing
symmetry fact.  ZERO mathematical content is hidden in this `sorry`: it is
exactly the independent symmetry/anonymity axiom that Step 5 must supply. -/
theorem exponents_equal_inv_k {k : Nat} (hk : 0 < k)
    (Lambda_fn : Aggregator k)
    (hL : LutarAxioms Lambda_fn)
    (alphas : Fin k → NNReal)
    (h_factor : ∀ x : Fin k → NNReal,
      Lambda_fn x = ∏ i, (x i) ^ (alphas i : ℝ)) :
    ∀ i, alphas i = (1 / k : NNReal) := by
  have hsym : IsSymmetric Lambda_fn := by
    -- SYMMETRY_AXIOM_GAP.  Not derivable from A1–A4 as formalized on this branch
    -- (counterexample `x ↦ x 0`).  This is exactly axiom **A5**
    -- (`IsPermutationInvariant`) added by the team on
    -- `fix/uniqueness-a1-a5-2026-06-02`.  Step 5 discharges this in one line via
    -- `hL.A5` once A5 is part of `LutarAxioms`; see `isSymmetric_iff_permInvariant`.
    sorry
  exact exponents_equal_inv_k_of_symm hk Lambda_fn hL hsym alphas h_factor

end Round9
end Lutar
