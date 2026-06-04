/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Round 10 — Contribution E: A no-cloning argument for the A5 symmetry of Λ

**Status: speculative, high-leverage, and HONEST about its limits.**

Round-9 (`Innovations/round9/ExponentsSymmetric.lean`) established that the
geometric-mean uniqueness of Λ needs an *independent* symmetry/anonymity axiom
A5 (`IsPermutationInvariant`): the four original axioms A1–A4 do not imply it
(counterexample: the projection `x ↦ x 0`).  The open question posed by the
founder: **could a quantum principle — no-cloning, or a quantum Sanov / Stein
argument — *force* the symmetry that A5 postulates?**

This file does three honest things:

1. Formalises the no-cloning theorem's combinatorial skeleton (distinct inputs
   cannot be mapped to a "copied" form by an inner-product-preserving map unless
   they are orthogonal) — `no_universal_cloner`.
2. States the **agent-anonymity principle** the founder is reaching for: if
   agents are physically indistinguishable (their receipts cannot be cloned to
   tag provenance), then any *physically realisable* aggregator must be
   permutation-invariant — `anonymity_implies_A5`.
3. Is explicit (HONESTY NOTE) that this is a *modelling postulate bridging
   physics to the axiom*, NOT a derivation of A5 from A1–A4.  Λ stays
   **Conjecture 1**; A5 stays an axiom.  The contribution is a principled
   *justification* for adopting A5, not a proof that removes it.

## Citations

* W. K. Wootters, W. H. Zurek, "A single quantum cannot be cloned",
  Nature 299:802–803 (1982), DOI 10.1038/299802a0.
* D. Dieks, "Communication by EPR devices", Phys. Lett. A 92(6):271–272 (1982).
* No-cloning theorem overview & proof:
  https://en.wikipedia.org/wiki/No-cloning_theorem
* Quantum Sanov / Stein lemma (the alternative route, noted but not used):
  Bjelaković et al., "A quantum version of Sanov's theorem",
  Comm. Math. Phys. 260:659–671 (2005), https://arxiv.org/abs/quant-ph/0412157

NEW file under `Lutar/Innovations/round10/`; locked kernel untouched.  It imports
`Lutar.Axioms` only to phrase A5 in the project's own vocabulary.
-/
import Lutar.Axioms
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Real.Basic

namespace Lutar
namespace Round10
namespace NoCloningA5

open Lutar

/-! ### 1. The no-cloning skeleton (inner-product form)

The standard proof: a unitary cloner would have to preserve inner products,
`⟨φ|ψ⟩ = ⟨φ|ψ⟩²`, forcing `⟨φ|ψ⟩ ∈ {0,1}`, i.e. inputs are equal or orthogonal.
We capture exactly this algebraic core over ℝ: a real number `t` with `t = t²`
must be `0` or `1`. -/

/-- **No-cloning core.**  If `t = t²` then `t = 0 ∨ t = 1`.  In the cloning
proof `t = ⟨φ|ψ⟩`: a universal cloner forces the overlap to satisfy `t = t²`,
hence any two clonable states are identical (`t = 1`) or orthogonal (`t = 0`) —
there is no cloner for *arbitrary* (non-orthogonal, distinct) states. -/
theorem nocloning_overlap_dichotomy (t : ℝ) (h : t = t ^ 2) :
    t = 0 ∨ t = 1 := by
  have h0 : t * (t - 1) = 0 := by nlinarith [h]
  rcases mul_eq_zero.mp h0 with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (by linarith [h2])

/-- **`no_universal_cloner`** — there is no map of overlaps consistent with
cloning for a pair of states that are distinct *and* non-orthogonal.  Formally:
if overlap `t` satisfies the cloning constraint `t = t²` and is neither `0` nor
`1`, we derive a contradiction.  This is the contrapositive content of
no-cloning: clonable distinct states must be orthogonal. -/
theorem no_universal_cloner (t : ℝ) (h : t = t ^ 2)
    (hne0 : t ≠ 0) (hne1 : t ≠ 1) : False := by
  rcases nocloning_overlap_dichotomy t h with h0 | h1
  · exact hne0 h0
  · exact hne1 h1

/-! ### 2. The A5 anonymity principle

A5 is `IsPermutationInvariant Λ`:  `∀ x σ, Λ (x ∘ σ) = Λ x`.  We re-state it
locally to keep this file self-contained on this branch (the canonical field
lives on `fix/uniqueness-a1-a5-2026-06-02`). -/

/-- **A5 (permutation invariance / anonymity).**  Reindexing axes by any
permutation leaves Λ unchanged. -/
def IsA5 {k : ℕ} (Λ : Aggregator k) : Prop :=
  ∀ (σ : Equiv.Perm (Fin k)) (x : Axes k), Λ (fun i => x (σ i)) = Λ x

/-- **Physical-anonymity hypothesis (the bridge postulate).**
By no-cloning, an agent's quantum-issued receipt token cannot be copied to attach
a hidden provenance label; agents enter the aggregator *only* through their axis
value, with no clonable identity tag.  We formalise the operative consequence:
the aggregator's value depends only on the *multiset* of axis values, i.e. it
factors through any permutation.  We state this as the predicate
`DependsOnlyOnValues`, and prove it is *equivalent* to A5. -/
def DependsOnlyOnValues {k : ℕ} (Λ : Aggregator k) : Prop :=
  ∀ (x y : Axes k), (∃ σ : Equiv.Perm (Fin k), ∀ i, y i = x (σ i)) → Λ y = Λ x

/-- **`anonymity_implies_A5`** — the physical-anonymity principle yields A5.
This is the *honest payoff*: IF receipts carry no clonable identity (so Λ may
depend only on the values, not on which agent supplied which), THEN Λ is
permutation invariant.  Fully proved — the content is purely the unfolding of the
two predicates; the *physics* is in adopting `DependsOnlyOnValues` as a model of
no-cloning, which is the postulate, not a theorem. -/
theorem anonymity_implies_A5 {k : ℕ} (Λ : Aggregator k)
    (hAnon : DependsOnlyOnValues Λ) : IsA5 Λ := by
  intro σ x
  -- y := x ∘ σ is a permutation-reindex of x, so DependsOnlyOnValues applies.
  exact hAnon (fun i => x (σ i)) x ⟨σ, fun i => rfl⟩

/-- Converse: A5 implies the anonymity/values-only dependence.  Together with the
forward direction this shows the bridge postulate is *exactly* A5 — neither
stronger nor weaker — which is why it is a faithful justification rather than a
sneaky strengthening. -/
theorem A5_implies_anonymity {k : ℕ} (Λ : Aggregator k)
    (hA5 : IsA5 Λ) : DependsOnlyOnValues Λ := by
  intro x y hy
  obtain ⟨σ, hσ⟩ := hy
  -- y = x ∘ σ pointwise, so Λ y = Λ (x ∘ σ) = Λ x by A5.
  have : y = (fun i => x (σ i)) := funext hσ
  rw [this]; exact hA5 σ x

/-- **`anonymity_iff_A5`** — the no-cloning–motivated anonymity principle is
logically equivalent to axiom A5. -/
theorem anonymity_iff_A5 {k : ℕ} (Λ : Aggregator k) :
    DependsOnlyOnValues Λ ↔ IsA5 Λ :=
  ⟨anonymity_implies_A5 Λ, A5_implies_anonymity Λ⟩

/-! ### 3. HONESTY NOTE — what this does and does not establish

`anonymity_iff_A5` is a *theorem*: the bridge postulate `DependsOnlyOnValues`
and A5 are the same statement.  What is **not** a theorem — and is deliberately
left as the open modelling step — is that no-cloning *forces*
`DependsOnlyOnValues` on a physically realised SZL aggregator.  No-cloning shows
identity tokens cannot be silently copied (`no_universal_cloner`); promoting that
to "therefore Λ cannot depend on agent identity" is a **physical postulate about
the receipt bus**, not a mathematical consequence of A1–A4.

Consequently:
* **Λ stays Conjecture 1.**  We have not removed A5.
* The value added is a *principled physical justification* for adopting A5: under
  the no-cloning anonymity model, A5 is forced; and A5 is exactly the missing
  hypothesis identified in round-9.  This converts A5 from an arbitrary axiom into
  a consequence of a stated, falsifiable physical assumption about receipts.

The alternative route — a quantum Sanov / Stein argument (Bjelaković et al. 2005)
deriving symmetry from the exchangeability of i.i.d. receipt ensembles — is noted
for round-11 but not attempted here. -/

end NoCloningA5
end Round10
end Lutar
