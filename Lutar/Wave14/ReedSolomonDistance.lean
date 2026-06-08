/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 14 — CF-19: Reed–Solomon MDS distance lower bound (clean, axiom-free)

The in-tree `Lutar/CodingTheory/ReedSolomonSingleton.lean` proves the polynomial-uniqueness
core `poly_uniqueness_at_k_points` (sorry-free) but leaves the *minimum-distance* statements
`reedSolomonIsMDS` / `singletonBound_upper` as honest `sorry`s (they need the heavy
linear-algebra Singleton counting / Vandermonde rank machinery).

This file closes the **honest, cleanly-provable HALF** that the uniqueness core directly buys:
the **MDS lower bound on the agreement/distance side**.

  *Two distinct polynomials of degree `< k` over a field agree on at most `k − 1` of any set
   of `n` distinct evaluation points; equivalently, their evaluation vectors differ in at least
   `n − k + 1` positions.*

This is exactly the classical Reed–Solomon distance lower bound
(Reed–Solomon 1960; Singleton 1964; cf. Kun 2015; arXiv:2411.14779 — "any nonzero `f` of degree
`≤ k−1` has at most `k−1` zeros in the evaluation set"). It is the achievability half of the
Singleton bound for RS codes, and is the part that follows *purely* from the
"fewer-than-`k` roots ⇒ zero polynomial" fact already available in Mathlib.

## What is PROVEN here (no sorry / NO new axiom)
* `roots_lt_card_of_degree_lt` — over a field, the agreement set of two distinct polynomials of
  degree `< k` among `n` distinct points has cardinality `< k` (hence `≤ k − 1`).
* `rs_distance_lower_bound` — the Hamming distance (number of differing coordinates) of the two
  evaluation vectors is at least `n − k + 1`.

## Honesty / scope
- EXPERIMENTAL companion (`Lutar/Wave14/`). Does NOT edit the baseline RS file; its `sorry`s
  (the Singleton *upper* bound and the full MDS equality, which need Vandermonde-rank linear
  algebra) stay honestly tracked. This file proves only the achievability/lower-distance half
  that the polynomial-root core cleanly delivers.
- Locked-proven set unchanged. NO new axiom; NO sorry.

## References
- Reed, I.S. & Solomon, G. (1960), JSIAM 8(2):300–304. DOI:10.1137/0108018
- Singleton, R.C. (1964), IEEE Trans. IT 10(2):116–118. DOI:10.1109/TIT.1964.1053661
- Kun, J. (2015), "The Codes of Solomon, Reed, and Muller."
- "New families of non-Reed-Solomon MDS codes", arXiv:2411.14779.

Signed-off-by: SZL CTO <cto@szl-holdings.com>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Data.Finset.Card

namespace Lutar.Wave14

open Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Agreement-set cardinality bound.** If `p ≠ q` are polynomials over a field with
    `p.natDegree < k` and `q.natDegree < k`, then among any finite set `pts` of points the
    subset on which `p` and `q` agree has cardinality strictly less than `k`.

    Proof: `p - q` is a nonzero polynomial of `natDegree < k`; a nonzero polynomial over a
    field has at most `natDegree` roots in any finset, so its root-subset of `pts` has
    cardinality `≤ (p-q).natDegree < k`. -/
theorem agreement_card_lt_of_degree_lt
    {k : ℕ} (pts : Finset F) (p q : Polynomial F)
    (hpdeg : p.natDegree < k) (hqdeg : q.natDegree < k) (hpq : p ≠ q) :
    (pts.filter (fun x => p.eval x = q.eval x)).card < k := by
  have hd0 : p - q ≠ 0 := sub_ne_zero.mpr hpq
  -- natDegree (p - q) < k
  have hdeg : (p - q).natDegree < k :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le p q) (Nat.max_lt.mpr ⟨hpdeg, hqdeg⟩)
  -- the agreement set is exactly the set of roots of (p - q) within pts
  have hset : pts.filter (fun x => p.eval x = q.eval x)
      = pts.filter (fun x => (p - q).IsRoot x) := by
    apply Finset.filter_congr
    intro x _
    simp [Polynomial.IsRoot, Polynomial.eval_sub, sub_eq_zero]
  rw [hset]
  -- the roots of a nonzero degree-`<k` polynomial inside `pts` number `≤ natDegree < k`
  have hcard : (pts.filter (fun x => (p - q).IsRoot x)).card ≤ (p - q).roots.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hd0]
    exact hx.2
  have hroots_le : (p - q).roots.toFinset.card ≤ (p - q).natDegree := by
    refine le_trans (Multiset.toFinset_card_le _) ?_
    exact le_trans (Polynomial.card_roots' (p - q)) (le_refl _)
  exact lt_of_le_of_lt (le_trans hcard hroots_le) hdeg

/-- Pure-arithmetic core: from `k ≤ n`, `A + D = n`, `A < k`, conclude `n - k + 1 ≤ D`. -/
private lemma rs_arith {n k A D : ℕ} (hkn : k ≤ n) (hpart : A + D = n) (hA : A < k) :
    n - k + 1 ≤ D := by omega

/-- **Reed–Solomon MDS distance lower bound (clean).** Let `pts : Fin n → F` be `n` distinct
    evaluation points and let `p ≠ q` be message polynomials of degree `< k`. Then the two
    codewords `(p.eval (pts i))ᵢ` and `(q.eval (pts i))ᵢ` differ in at least `n − k + 1`
    coordinates — the achievability half of the Singleton bound for RS codes.

    (Stated as: the number of AGREEING coordinates is `≤ k − 1`, equivalently the number of
    DIFFERING coordinates is `≥ n − (k − 1) = n − k + 1`.) -/
theorem rs_distance_lower_bound
    {n k : ℕ} (_hk : 1 ≤ k) (hkn : k ≤ n)
    (pts : Fin n → F) (hpts : Function.Injective pts)
    (p q : Polynomial F)
    (hpdeg : p.natDegree < k) (hqdeg : q.natDegree < k) (hpq : p ≠ q) :
    n - k + 1 ≤
      (Finset.univ.filter (fun i : Fin n => p.eval (pts i) ≠ q.eval (pts i))).card := by
  classical
  -- agree and disagree partition Fin n.
  have hpart :
      (Finset.univ.filter (fun i : Fin n => p.eval (pts i) = q.eval (pts i))).card
        + (Finset.univ.filter (fun i : Fin n => p.eval (pts i) ≠ q.eval (pts i))).card = n := by
    rw [Finset.filter_card_add_filter_neg_card_eq_card]
    simp
  -- bound on the agreeing indices: they inject into the agreeing POINTS.
  have hagree_lt :
      (Finset.univ.filter (fun i : Fin n => p.eval (pts i) = q.eval (pts i))).card < k := by
    have himg :
        (Finset.univ.filter (fun i : Fin n => p.eval (pts i) = q.eval (pts i))).image pts
          ⊆ (Finset.univ.image pts).filter (fun x => p.eval x = q.eval x) := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hi.2⟩
    have hcard_eq :
        ((Finset.univ.filter (fun i : Fin n => p.eval (pts i) = q.eval (pts i))).image pts).card
          = (Finset.univ.filter (fun i : Fin n => p.eval (pts i) = q.eval (pts i))).card :=
      Finset.card_image_of_injective _ hpts
    have hsub_lt : ((Finset.univ.image pts).filter (fun x => p.eval x = q.eval x)).card < k :=
      agreement_card_lt_of_degree_lt (Finset.univ.image pts) p q hpdeg hqdeg hpq
    calc (Finset.univ.filter (fun i : Fin n => p.eval (pts i) = q.eval (pts i))).card
        = ((Finset.univ.filter (fun i : Fin n => p.eval (pts i) = q.eval (pts i))).image pts).card :=
          hcard_eq.symm
      _ ≤ ((Finset.univ.image pts).filter (fun x => p.eval x = q.eval x)).card :=
            Finset.card_le_card himg
      _ < k := hsub_lt
  -- combine: disagree.card = n − agree.card ≥ n − (k−1) = n − k + 1.
  -- Use an abstract Nat lemma fed exactly the three facts (so omega never has to recognize
  -- the Finset.card atoms; they are passed as plain Nat values).
  exact rs_arith hkn hpart hagree_lt

end Lutar.Wave14
