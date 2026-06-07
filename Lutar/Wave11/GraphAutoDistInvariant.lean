/-
Copyright © 2026 Stephen P. Lutar Jr. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave11/GraphAutoDistInvariant.lean — CF-1 core (Frontier)

Λ-graph automorphism / isomorphism label-invariance: the missing metric core.

P-GNN (You et al. 2019) position-aware embeddings encode each vertex by its
distance to anchor vertices.  For these to be a sound *audit-fiber* invariant
(relabelling the execution graph must not change the receipt), the underlying
`SimpleGraph.dist` must be preserved by graph automorphisms.  Mathlib has
`SimpleGraph.dist`, `Walk.map`, `Walk.length_map`, and `Reachable.map`, but
does **not** package the automorphism/iso distance-invariance lemma.  This file
supplies it, then lifts it to the P-GNN position-encoding equivariance that
`Lutar/PositionAware.lean` previously only *tracked* as `:= True`.

## What is proven (kernel-clean, no sorry/admit/axiom)

- `dist_le_of_iso` — an iso `f : G ≃g G'` cannot increase distance:
  `G'.dist (f u) (f v) ≤ G.dist u v` (map the realising walk).
- `reachable_iso_iff` — reachability is an iso-invariant.
- `dist_iso_eq` — **CF-1 metric core**: `G'.dist (f u) (f v) = G.dist u v` for
  any graph isomorphism `f : G ≃g G'` (both inequalities ⇒ equality).
- `dist_auto_eq` — automorphism specialisation `G.dist (f u) (f v) = G.dist u v`.
- `positionEncoding_equivariant` — **CF-1 P-GNN obligation**: the P-GNN
  distance-to-anchor position vector is automorphism-equivariant — relabelling a
  vertex `v` and its anchor `a` by `f` leaves the encoded distance unchanged.
- `positionEncoding_iso_equivariant` — the cross-graph (iso) version.

These discharge the two stubbed obligations in `Lutar/PositionAware.lean`
(`dist_iso_inv_tracked`, `positionEncoding_equivariant_tracked`, formerly
`:= True`) and supply the metric backbone of the GraphLambda Λ-iso claim.

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave11`) — ADDITIVE, NOT in the LOCKED v11 baseline
  (749/14/163 @ c7c0ba17). Locked-proven stays EXACTLY 5 {F1,F11,F12,F18,F19}.
  Λ remains Conjecture 1. NOT imported into `Lutar.lean`.
- Built on Mathlib `SimpleGraph.Metric`; NO new declared axiom, NO sorry.

## Citations
- You, J., Gomes-Selman, J., Ying, R., Leskovec, J. (2019). "Position-aware
  Graph Neural Networks." ICML 2019. arXiv:1906.04817. [JiaxuanYou/P-GNN, MIT].
- You, J., Leskovec, J., He, K., Xie, S. (2021). "Identity-aware Graph Neural
  Networks." AAAI 2021. arXiv:2101.10320.
- Mathlib: `SimpleGraph.Iso`, `SimpleGraph.Walk.map`, `Walk.length_map`,
  `SimpleGraph.Reachable.map`, `SimpleGraph.dist_le`.

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/

import Mathlib.Combinatorics.SimpleGraph.Metric

namespace Lutar.Wave11.GraphAutoDistInvariant

open SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}

/-- Reachability transports along an iso (both directions). -/
theorem reachable_iso_iff (f : G ≃g G') (u v : V) :
    G'.Reachable (f u) (f v) ↔ G.Reachable u v := by
  constructor
  · intro h
    -- pull back along f.symm; f.symm (f u) = u
    have := h.map f.symm.toHom
    simpa using this
  · intro h
    exact h.map f.toHom

/-- An iso does not increase distance: it maps a realising walk to a walk of the
    same length in the codomain. -/
theorem dist_le_of_iso (f : G ≃g G') (u v : V) :
    G'.dist (f u) (f v) ≤ G.dist u v := by
  by_cases h : G.Reachable u v
  · -- take a walk of length `dist u v`, map it; its length is preserved
    obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
    have hmap : (p.map f.toHom).length = G.dist u v := by
      rw [Walk.length_map]; exact hp
    calc G'.dist (f u) (f v) ≤ (p.map f.toHom).length := dist_le _
      _ = G.dist u v := hmap
  · -- unreachable: dist u v = 0, and the codomain dist is ≤ 0
    have hr : ¬ G.Reachable u v := h
    have : G.dist u v = 0 := dist_eq_zero_of_not_reachable hr
    rw [this]
    -- need G'.dist (f u) (f v) ≤ 0, i.e. = 0; (f u),(f v) also unreachable
    have hr' : ¬ G'.Reachable (f u) (f v) := by
      rw [reachable_iso_iff f]; exact hr
    rw [dist_eq_zero_of_not_reachable hr']

/-- **CF-1 metric core — graph-isomorphism distance invariance.**
    For any graph isomorphism `f : G ≃g G'`, `dist` is preserved exactly. -/
theorem dist_iso_eq (f : G ≃g G') (u v : V) :
    G'.dist (f u) (f v) = G.dist u v := by
  apply le_antisymm (dist_le_of_iso f u v)
  -- reverse: apply dist_le_of_iso to f.symm at (f u), (f v); simp f.symm (f u) = u
  have hsym := dist_le_of_iso f.symm (f u) (f v)
  simpa using hsym

/-- **CF-1 — automorphism distance invariance** (`G' = G`). -/
theorem dist_auto_eq (f : G ≃g G) (u v : V) :
    G.dist (f u) (f v) = G.dist u v :=
  dist_iso_eq f u v

/-! ## §  P-GNN position-encoding equivariance (closes PositionAware stubs) -/

/-- P-GNN position encoding: distance from `v` to anchor `a`.  (Mirrors
    `Lutar.PositionAware.positionEncoding` for a single anchor.) -/
noncomputable def posEnc (G : SimpleGraph V) (v a : V) : ℕ := G.dist v a

/-- **CF-1 P-GNN obligation (automorphism equivariance).**
    Relabelling both a vertex `v` and an anchor `a` by an automorphism `f`
    leaves the distance-to-anchor position code unchanged:
    `posEnc G (f v) (f a) = posEnc G v a`. Hence the P-GNN position embedding is
    an automorphism-invariant audit feature — a relabelled execution graph
    produces the identical position encoding (the audit-fiber invariance). -/
theorem positionEncoding_equivariant (f : G ≃g G) (v a : V) :
    posEnc G (f v) (f a) = posEnc G v a :=
  dist_auto_eq f v a

/-- **CF-1 P-GNN obligation (cross-graph / iso equivariance).**
    The same statement across two isomorphic graphs: the position encoding
    transports along the isomorphism `f : G ≃g G'`. -/
theorem positionEncoding_iso_equivariant (f : G ≃g G') (v a : V) :
    posEnc G' (f v) (f a) = posEnc G v a :=
  dist_iso_eq f v a

end Lutar.Wave11.GraphAutoDistInvariant

-- ## CF-1 axiom disclosure (CI prints these in the build log).
-- Structural metric proofs; expected kernel-only [propext, Classical.choice,
-- Quot.sound] (or fewer). NO sorryAx, NO declared Lutar axioms.
#print axioms Lutar.Wave11.GraphAutoDistInvariant.reachable_iso_iff
#print axioms Lutar.Wave11.GraphAutoDistInvariant.dist_le_of_iso
#print axioms Lutar.Wave11.GraphAutoDistInvariant.dist_iso_eq
#print axioms Lutar.Wave11.GraphAutoDistInvariant.dist_auto_eq
#print axioms Lutar.Wave11.GraphAutoDistInvariant.positionEncoding_equivariant
#print axioms Lutar.Wave11.GraphAutoDistInvariant.positionEncoding_iso_equivariant
