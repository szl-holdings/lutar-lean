/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 19 — CUT-1 density: sub-lemma B reduction (uncountable accumulation points)

## Mission (BKS 2208.07083 Lemma 6, bullet 2)
> "The closure of `f(D)` has uncountably many two-sided accumulation points."

This is the genuinely-deep half of the BKS density argument. We do NOT fake it. Instead we close
the **structural reduction** kernel-clean: the statement "uncountably many" is reduced to "contains
a nonempty **perfect** subset", and we PROVE that *a nonempty perfect subset of `ℝ` is
uncountable* (via Mathlib's Cantor-injection `Perfect.exists_nat_bool_injection`, since `ℝ` is a
complete metric space and the Cantor space `ℕ → Bool` has cardinality continuum).

So sub-lemma B is reduced to its honest residual core:
> **(B-residual)** the closure of the dyadic image contains a nonempty perfect set of two-sided
> accumulation points.

That residual is the part requiring the BKS self-similar / bisymmetric generator structure
(Aczél–Dhombres pp. 287–290), which is multi-week and is documented — NOT axiomatised, NOT
`sorry`-ed. Everything in THIS file (the "perfect ⇒ uncountable" engine and the point-level
two-sided/accumulation bridges) is fully kernel-clean.

NO `sorry`, NO new axiom. `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.

## Sources
* Burai, Kiss, Szokol (2022), arXiv:2208.07083 — Lemma 6, bullet 2 + footnote 2 (two-sided
  accumulation point).
* Mathlib `Perfect.exists_nat_bool_injection` (perfect nonempty set in complete metric space admits
  a continuous injection from Cantor space).
* G. Kiss (2026), *On noncontinuous bisymmetric strictly monotone operations* — the honest boundary:
  dropping reflexivity/symmetry permits noncontinuous `F`, so these hypotheses are essential.
-/
import Lutar.Wave19.Density
import Mathlib.Topology.MetricSpace.Perfect
import Mathlib.SetTheory.Cardinal.Continuum

open Set Function Cardinal

namespace Lutar.Wave19

/-- The Cantor space `ℕ → Bool` is uncountable (cardinality continuum `𝔠 > ℵ₀`). -/
theorem natBool_not_countable : ¬ Countable (ℕ → Bool) := by
  rw [← Cardinal.mk_le_aleph0_iff]
  have h : #(ℕ → Bool) = 𝔠 := by rw [mk_arrow]; simp [mk_bool, mk_nat, power_def]
  rw [h]
  exact not_le.2 aleph0_lt_continuum

/-- **Sub-lemma B engine (kernel-clean): a nonempty perfect set of reals is uncountable.**
Via Mathlib's `Perfect.exists_nat_bool_injection`: a nonempty perfect set in the complete metric
space `ℝ` admits an injection from the uncountable Cantor space `ℕ → Bool`, hence is uncountable.
This is the precise quantitative content behind BKS bullet 2 — "uncountably many". -/
theorem perfect_nonempty_not_countable {C : Set ℝ} (hC : Perfect C) (hne : C.Nonempty) :
    ¬ C.Countable := by
  obtain ⟨f, hrange, _, hinj⟩ := hC.exists_nat_bool_injection hne
  intro hcount
  have hrc : (range f).Countable := hcount.mono hrange
  have hrc' : Countable (range f) := hrc.to_subtype
  have hcd : Countable (ℕ → Bool) :=
    (Function.Injective.countable (f := Set.rangeFactorization f)
      (fun a b hab => hinj (congrArg Subtype.val hab)))
  exact natBool_not_countable hcd

/-- **Sub-lemma B reduction.** If the two-sided accumulation set `accSet` of `H` *contains* a
nonempty perfect set `C` (the honest residual `(B-residual)`), then `accSet` is uncountable — the
form consumed by `dyadic_image_dense` / `dyadic_image_dense_of_sep`.

This makes BKS bullet 2 entirely a matter of exhibiting the perfect subset; the "uncountably many"
conclusion is then automatic and kernel-clean. -/
theorem accSet_not_countable_of_perfect_subset {accSet C : Set ℝ}
    (hsub : C ⊆ accSet) (hC : Perfect C) (hne : C.Nonempty) : ¬ accSet.Countable :=
  fun hcount => perfect_nonempty_not_countable hC hne (hcount.mono hsub)

/-- A two-sided accumulation point (BKS footnote 2) is an `AccPt` of `H` in Mathlib's sense
(cluster point with respect to the principal filter): every neighbourhood meets `H` away from the
point. Bridges `IsTwoSidedAccPt` to Mathlib's perfect/accumulation API. -/
theorem accPt_of_isTwoSidedAccPt {H : Set ℝ} {α : ℝ} (h : IsTwoSidedAccPt H α) :
    AccPt α (Filter.principal H) := by
  rw [accPt_iff_nhds]
  intro U hU
  rw [Metric.mem_nhds_iff] at hU
  obtain ⟨ε, hε, hball⟩ := hU
  obtain ⟨⟨x, hx⟩, _⟩ := h ε hε
  refine ⟨x, ⟨hball ?_, hx.2⟩, ?_⟩
  · -- x ∈ ]α-ε, α[ ⊆ ball α ε
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩
  · -- x < α so x ≠ α
    exact ne_of_lt hx.1.2

end Lutar.Wave19
