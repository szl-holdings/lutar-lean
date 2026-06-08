/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 20 — PRIMITIVE B: two-sided accumulation + perfect ⇒ uncountable bridge

## Mission (the "uncountably many accumulation points" fact, standalone & honest)
This file supplies — as **independent, general primitives** — the bridge that BKS
(arXiv:2208.07083) Lemma 6, bullet 2 needs:

> "the closure of `f(D)` has uncountably many two-sided accumulation points."

The genuinely hard, BKS-self-similar-structure content is the existence of a nonempty **perfect**
subset.  We do **NOT** fake it.  Instead we prove the entire *generic bridge* kernel-clean and
reduce B to a **single, clearly stated residual**:

* **Engine** (proved here): a nonempty **perfect** subset of `ℝ` is **uncountable**
  (Cantor injection `Perfect.exists_nat_bool_injection`; `ℕ → Bool` has cardinality `𝔠 > ℵ₀`).
* **Perfect bridge** (proved here): `IsClosed C` + "**no isolated points**"
  (`∀ x ∈ C, AccPt x (𝓟 C)`, i.e. `Preperfect C`) ⇒ `Perfect C` ⇒ (if nonempty) uncountable.
  This is exactly the brief's requested bridge
  *"closure has no isolated points ⇒ perfect ⇒ uncountable"*.
* **Two-sided accumulation** (defined + bridged here): `IsTwoSidedAccPt H α` (every left- and
  right- neighbourhood of `α` meets `H`) implies the Mathlib `AccPt α (𝓟 H)`.  Hence a set all of
  whose points are two-sided accumulation points of itself, if closed and nonempty, is perfect and
  uncountable.
* **Residual** (NOT proved here; NOT axiomatised; NOT `sorry`-ed): the BKS-specific
  `(B-residual)` — *the closure of the dyadic generator image contains a nonempty perfect set of
  two-sided accumulation points* — which requires the recursive midpoint / densely-self-similar
  structure (Aczél–Dhombres pp. 287–290).  Once `(B-residual)` is supplied, bullet 2 ("uncountably
  many") is immediate from `twoSidedPerfect_uncountable` below.

Everything in THIS file is fully kernel-clean.  It imports only core Mathlib — NO Wave18/Wave19
dependency.

NO `sorry`, NO new axiom. `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.

## Sources
* Burai, Kiss, Szokol (2022), arXiv:2208.07083 — https://arxiv.org/abs/2208.07083 — Lemma 6,
  bullet 2 + footnote 2 (definition of two-sided accumulation point).
* Mathlib `Perfect`, `Preperfect`, `Perfect.exists_nat_bool_injection`, `accPt_iff_nhds`.
* G. Kiss (2026), *On noncontinuous bisymmetric strictly monotone operations* — the honest
  boundary: dropping reflexivity/symmetry permits noncontinuous `F`, so these hypotheses are
  essential (the residual cannot be obtained without them).
-/
import Mathlib.Topology.MetricSpace.Perfect
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Topology.Instances.Real.Lemmas

open Set Function Cardinal

namespace Lutar.Wave20

/-! ## Part 1 — the quantitative engine: perfect nonempty ⇒ uncountable -/

/-- The Cantor space `ℕ → Bool` is uncountable (cardinality continuum `𝔠 > ℵ₀`). -/
theorem natBool_not_countable : ¬ Countable (ℕ → Bool) := by
  rw [← Cardinal.mk_le_aleph0_iff]
  have h : #(ℕ → Bool) = 𝔠 := by rw [mk_arrow]; simp [mk_bool, mk_nat, power_def]
  rw [h]
  exact not_le.2 aleph0_lt_continuum

/-- **Primitive B engine: a nonempty perfect set of reals is uncountable.**
Via Mathlib's `Perfect.exists_nat_bool_injection`: a nonempty perfect set in the complete metric
space `ℝ` admits an injection from the uncountable Cantor space `ℕ → Bool`, hence is uncountable.
This is the precise quantitative content behind BKS bullet 2 — "uncountably many". -/
theorem perfect_nonempty_not_countable {C : Set ℝ} (hC : Perfect C) (hne : C.Nonempty) :
    ¬ C.Countable := by
  obtain ⟨f, hrange, _, hinj⟩ := hC.exists_nat_bool_injection hne
  intro hcount
  have hrc : (range f).Countable := hcount.mono hrange
  have : Countable (range f) := hrc.to_subtype
  have hcd : Countable (ℕ → Bool) :=
    Function.Injective.countable (f := Set.rangeFactorization f)
      (fun a b hab => hinj (congrArg Subtype.val hab))
  exact natBool_not_countable hcd

/-! ## Part 2 — the perfect bridge: closed + no isolated points ⇒ perfect ⇒ uncountable -/

/-- **Perfect bridge.** A set that is `IsClosed` and has **no isolated points**
(`∀ x ∈ C, AccPt x (𝓟 C)`, i.e. `Preperfect C`) is `Perfect`. This is just the `Perfect`
constructor, packaged as the brief's named bridge. -/
theorem perfect_of_isClosed_no_isolated {C : Set ℝ} (hClosed : IsClosed C)
    (hAcc : ∀ x ∈ C, AccPt x (Filter.principal C)) : Perfect C :=
  ⟨hClosed, hAcc⟩

/-- **The full bridge (brief's `no isolated points ⇒ perfect ⇒ uncountable`).** A nonempty closed
set of reals with no isolated points is uncountable. -/
theorem uncountable_of_isClosed_no_isolated {C : Set ℝ} (hne : C.Nonempty)
    (hClosed : IsClosed C) (hAcc : ∀ x ∈ C, AccPt x (Filter.principal C)) : ¬ C.Countable :=
  perfect_nonempty_not_countable (perfect_of_isClosed_no_isolated hClosed hAcc) hne

/-- **Reduction form for a superset.** If a set `S` *contains* a nonempty perfect set `C` (the
honest residual `(B-residual)`), then `S` is uncountable.  This is the precise shape consumed by
the BKS density argument: take `S` = the set of two-sided accumulation points. -/
theorem not_countable_of_perfect_subset {S C : Set ℝ}
    (hsub : C ⊆ S) (hC : Perfect C) (hne : C.Nonempty) : ¬ S.Countable :=
  fun hcount => perfect_nonempty_not_countable hC hne (hcount.mono hsub)

/-! ## Part 3 — two-sided accumulation points (BKS footnote 2) -/

/-- **Two-sided accumulation point** (BKS arXiv:2208.07083, footnote 2): `α` is a two-sided
accumulation point of `H ⊆ ℝ` if every punctured left- and right- neighbourhood of `α` meets `H`:
for all `ε > 0`, both `]α-ε, α[ ∩ H` and `]α, α+ε[ ∩ H` are nonempty. -/
def IsTwoSidedAccPt (H : Set ℝ) (α : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), (Ioo (α - ε) α ∩ H).Nonempty ∧ (Ioo α (α + ε) ∩ H).Nonempty

/-- **Two-sided ⇒ Mathlib accumulation point.** A two-sided accumulation point of `H` (BKS sense)
is an `AccPt` of `H` in Mathlib's sense (cluster point of the principal filter): every
neighbourhood meets `H` away from the point.  Bridges `IsTwoSidedAccPt` into the `Perfect`/`AccPt`
API so the engine and bridge above apply. -/
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

/-- **Capstone bridge for BKS bullet 2.** If `C ⊆ ℝ` is nonempty, closed, and **every** point of
`C` is a *two-sided* accumulation point of `C`, then `C` is perfect and hence **uncountable**.

This is the directly-usable form: once `(B-residual)` exhibits such a `C` inside the set of
two-sided accumulation points of the dyadic image's closure, "uncountably many two-sided
accumulation points" follows immediately (`not_countable_of_perfect_subset`). -/
theorem twoSidedPerfect_uncountable {C : Set ℝ} (hne : C.Nonempty) (hClosed : IsClosed C)
    (hTwoSided : ∀ x ∈ C, IsTwoSidedAccPt C x) : ¬ C.Countable :=
  uncountable_of_isClosed_no_isolated hne hClosed
    (fun x hx => accPt_of_isTwoSidedAccPt (hTwoSided x hx))

/-- **The residual, assembled.** Given the honest residual `(B-residual)` — a nonempty perfect set
`C` of two-sided accumulation points contained in the set `S` of all two-sided accumulation points
of `H` — the conclusion of BKS bullet 2 ("`S` is uncountable") is immediate.  This lemma is the
single named entry point that the BKS-specific generator argument must feed. -/
theorem uncountable_twoSidedAccSet_of_perfect_subset {H S C : Set ℝ}
    (_hSdef : ∀ x ∈ S, IsTwoSidedAccPt H x)
    (hsub : C ⊆ S) (hC : Perfect C) (hne : C.Nonempty) : ¬ S.Countable :=
  not_countable_of_perfect_subset hsub hC hne

end Lutar.Wave20
