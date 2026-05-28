/-
# Audit-Reidemeister Conjecture (v15 → v16)

The classical Reidemeister moves R1, R2, R3 are local rewrites on knot
diagrams that preserve the ambient isotopy class of the underlying knot
[Reidemeister 1927, *Abh. Math. Sem. Univ. Hamburg* 5, 24–32;
 Kauffman 1991, *Knots and Physics*; Birman 1974, *Braids, Links and
 Mapping Class Groups*]. A function on knot diagrams is a *knot invariant*
exactly when it is invariant under R1, R2, R3 (modulo a framing factor for
unframed invariants under R1).

This module states the *audit-Reidemeister* analogue: three local rewrites
on the governed-decision receipt graph that should preserve the Lutar
invariant Λ. They are:

  R1 — single-axis repack: rewriting a single axis check into an equivalent
       form (no information change) leaves Λ unchanged.
  R2 — independent commute: swapping the order of two gate evaluations on
       disjoint axis subsets leaves Λ unchanged.
  R3 — receipt-chain associativity: re-parenthesising a chain
       ((a∘b)∘c) ↔ (a∘(b∘c)) leaves Λ unchanged.

All three are tagged as `axiom` (see Status note below). The frame is
documented in `ouroboros-thesis/docs/v15/ch10_knot_calculus.md` §10.2.
Target v16 closure.

Geometric reading: Λ is a *knot invariant* of the receipt-chain braid in
B_n, where n is the number of concurrent actors. Khipu hierarchy supplies
the chord-diagram skeleton [Bar-Natan 1995, *Topology* 34, 423–472;
Vassiliev 1990, *Adv. Sov. Math.* 1, 23–69; Kontsevich 1993].

Status: ALL THREE STATEMENTS ARE TAGGED AS `axiom`, not `theorem`. They are
not proved in this module. Using `axiom` rather than `theorem ... := sorry`
is the doctrinally honest spelling: Lean's `#print axioms` machinery will
flag any downstream theorem that depends on R1/R2/R3, so callers cannot
mistake conjectural facts for proven ones (B2 issue lutar-lean#32 fix).

Each axiom is intended to become a `theorem` once the Reidemeister-move
equivalence on the receipt-rewriting calculus is fully formalized.
Target: v17.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Lutar.Invariant
import Lutar.Axioms

namespace Lutar.Knot

open Lutar

/-- A *receipt-graph rewrite* is an endofunction on axis vectors that should
    preserve the audit-equivalence class. We do not fix a particular small
    set of allowed rewrites — instead, R1, R2, R3 below are the three
    canonical generators. -/
def AxisRewrite (k : ℕ) := Axes k → Axes k

/-- **R1 — Single-axis repack.** A repack rewrite acts on a single axis `i`
    by replacing `x_i` with `f(x_i)` for some bijection `f : NNReal → NNReal`
    that preserves the Λ-axis interpretation (typically a unit-preserving
    rescaling like `x ↦ x` or `x ↦ x^p · x^(1-p)`). The conjecture is that
    such repacks leave Λ fixed iff `f` is the identity on the i-th coordinate
    in the geometric mean sense. -/
def isR1Rewrite {k : ℕ} (i : Fin k) (f : NNReal → NNReal) (r : AxisRewrite k) : Prop :=
  ∀ x : Axes k, (r x) i = f (x i) ∧ ∀ j : Fin k, j ≠ i → (r x) j = x j

/-- **R2 — Independent commute.** Two rewrites act on disjoint axis subsets
    `S` and `T`. Their composition commutes; Λ is unchanged.
    Stated using the fact that Λ is a symmetric function of its k arguments
    (the geometric mean is invariant under permutation). -/
def isR2Commute {k : ℕ} (r₁ r₂ : AxisRewrite k) : Prop :=
  ∀ x : Axes k, r₁ (r₂ x) = r₂ (r₁ x)

/-- **R3 — Receipt-chain associativity.** Composition of three rewrites is
    associative: `(r₁ ∘ r₂) ∘ r₃ = r₁ ∘ (r₂ ∘ r₃)`. This is `Function.comp_assoc`
    in Mathlib; included here as a Reidemeister-style local rewrite. -/
def isR3Associative {k : ℕ} (r₁ r₂ r₃ : AxisRewrite k) : Prop :=
  (r₁ ∘ r₂) ∘ r₃ = r₁ ∘ (r₂ ∘ r₃)

/-- **Conjecture R1 (audit-Reidemeister).**
    For any single-axis repack `r` that preserves the geometric-mean factor
    at position `i` (i.e. `f x = x`), Λ is invariant under `r`.

    Status: Conjecture. Proof route: from `Λ_def` and the definition of
    geometric mean, expand the product, substitute `f = id`, and conclude
    by `rfl`. The general statement (any `f` such that `f` is the identity
    on the i-th factor in the multiplicative sense) is open.

    Target: v16. Tagged as `axiom` per B2 issue lutar-lean#32. -/
axiom Λ_invariant_under_R1
    {k : ℕ} (hk : 0 < k) (i : Fin k) (r : AxisRewrite k)
    (h_r1 : isR1Rewrite i id r) :
    ∀ x : Axes k, Λ k (r x) = Λ k x

/-- **Conjecture R2 (audit-Reidemeister).**
    For any two rewrites `r₁`, `r₂` that commute (act on disjoint axis subsets),
    Λ is invariant under both `r₁ ∘ r₂` and `r₂ ∘ r₁` *equally*.

    Status: Conjecture. Proof route: from `isR2Commute` plus the symmetry of
    the geometric mean under permutation.

    Target: v16. Tagged as `axiom` per B2 issue lutar-lean#32. -/
axiom Λ_invariant_under_R2
    {k : ℕ} (hk : 0 < k) (r₁ r₂ : AxisRewrite k)
    (h_r2 : isR2Commute r₁ r₂)
    (h_inv_r₁ : ∀ x, Λ k (r₁ x) = Λ k x)
    (h_inv_r₂ : ∀ x, Λ k (r₂ x) = Λ k x) :
    ∀ x : Axes k, Λ k (r₁ (r₂ x)) = Λ k x

/-- **Conjecture R3 (audit-Reidemeister).**
    For any three rewrites `r₁`, `r₂`, `r₃`, associativity of composition
    implies Λ-invariance under `r₁ ∘ r₂ ∘ r₃` does not depend on parenthesisation.

    Status: Conjecture. Proof route: `Function.comp_assoc` is a `theorem` in
    Mathlib; the remaining content is that Λ-invariance is closed under
    composition of invariant rewrites.

    Target: v16. Tagged as `axiom` per B2 issue lutar-lean#32. -/
axiom Λ_invariant_under_R3
    {k : ℕ} (hk : 0 < k) (r₁ r₂ r₃ : AxisRewrite k)
    (h_r3 : isR3Associative r₁ r₂ r₃)
    (h_inv_r₁ : ∀ x, Λ k (r₁ x) = Λ k x)
    (h_inv_r₂ : ∀ x, Λ k (r₂ x) = Λ k x)
    (h_inv_r₃ : ∀ x, Λ k (r₃ x) = Λ k x) :
    ∀ x : Axes k, Λ k (((r₁ ∘ r₂) ∘ r₃) x) = Λ k x

end Lutar.Knot
