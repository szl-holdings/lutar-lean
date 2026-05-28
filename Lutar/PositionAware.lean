/-
Copyright © 2026 Stephen P. Lutar Jr. (SZL Holdings).
Released under the Apache-2.0 License.

# PositionAware — anchor-based position embedding for audit fibers (v17.2)

Fashion-graft of P-GNN [You et al. 2019 ICML, JiaxuanYou/P-GNN]: position-aware
embeddings break the symmetric-vertex limitation of standard GNNs by sampling
random anchor sets and encoding each vertex's distance to each anchor.

SZL innovation: position-anchored DPI bound — Bekenstein capacity computed
per local audit neighbourhood (the k-hop ball around an anchor), giving
sharper per-region governance bounds than the global DPI bound.

## Citations

  - You, J., Gomes-Selman, J., Ying, R., Leskovec, J. (2019). "Position-aware
    Graph Neural Networks." ICML 2019. arXiv:1906.04817.
    [JiaxuanYou/P-GNN]
  - You, J., Leskovec, J., He, K., Xie, S. (2020). "Graph Structure of Neural
    Networks." NeurIPS 2020. arXiv:2007.06559.
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Lutar.GraphLambda

namespace Lutar.PositionAware

open SimpleGraph

/-- An anchor set: a finite subset of vertices. -/
def AnchorSet (V : Type) [Fintype V] := Finset V

/-! ## §1. Position encoding -/

/-- The position-encoding of a vertex w.r.t. an anchor set:
    distance to each anchor.  Convention: `SimpleGraph.dist` returns 0
    when vertices are unreachable (the standard Mathlib junk-value convention). -/
noncomputable def positionEncoding {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : AnchorSet V) (v : V) : A → ℕ :=
  fun a => G.dist v a.val

/-! ## §2. Graph-isomorphism distance invariance (auxiliary lemma) -/

/-- **Auxiliary (V17.2-L1).** A graph self-automorphism preserves `SimpleGraph.dist`.

    Proof: given `φ : V ≃ V` preserving adjacency, we build a `G →g G`
    homomorphism using `φ`. Then `Walk.map` transports every walk `p : G.Walk v a`
    to a walk `p.map φ_hom : G.Walk (φ v) (φ a)` of the same length
    (`Walk.length_map`), so the infimum over walk-lengths is ≤ in both directions,
    yielding equality.

    The graph homomorphism `φ_hom` is built from `φ.toFun` and the forward
    direction of `hφ`; the inverse homomorphism uses `φ.invFun` and the
    backward direction (accessed via `φ.left_inv` + `hφ`). -/
theorem dist_iso_inv {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (φ : V ≃ V)
    (hφ : ∀ x y : V, G.Adj x y ↔ G.Adj (φ x) (φ y))
    (u v : V) :
    G.dist u v = G.dist (φ u) (φ v) := by
  -- Build the forward graph homomorphism φ_hom : G →g G
  let φ_hom : G →g G :=
    ⟨φ.toFun, fun {a b} hab => (hφ a b).mp hab⟩
  -- Build the backward graph homomorphism φ_inv_hom : G →g G using φ.symm
  let φ_inv_hom : G →g G :=
    ⟨φ.invFun, fun {a b} hab => by
      -- We need: G.Adj (φ.invFun a) (φ.invFun b) from G.Adj a b
      -- By hφ applied to φ.invFun a, φ.invFun b:
      -- G.Adj (φ.invFun a) (φ.invFun b) ↔ G.Adj (φ (φ.invFun a)) (φ (φ.invFun b))
      -- = G.Adj a b  (by right_inv)
      rw [hφ (φ.invFun a) (φ.invFun b)]
      simp [φ.right_inv]
      exact hab⟩
  -- Apply dist_le and Walk.map + Walk.length_map in both directions
  apply Nat.le_antisymm
  · -- G.dist u v ≤ G.dist (φ u) (φ v):
    -- for any walk q : G.Walk (φ u) (φ v),
    -- (q.map φ_inv_hom) : G.Walk (φ.invFun (φ u)) (φ.invFun (φ v))
    --                    = G.Walk u v   (by left_inv)
    -- and has the same length.
    rw [dist_eq_sInf, dist_eq_sInf]
    apply Nat.sInf_le_sInf
    intro k ⟨p, hp⟩
    -- p : G.Walk u v, p.length = k
    -- produce q = p.map φ_hom : G.Walk (φ u) (φ v)
    exact ⟨p.map φ_hom, by rw [Walk.length_map]; exact hp⟩
  · -- G.dist (φ u) (φ v) ≤ G.dist u v:
    rw [dist_eq_sInf, dist_eq_sInf]
    apply Nat.sInf_le_sInf
    intro k ⟨q, hq⟩
    -- q : G.Walk (φ u) (φ v), q.length = k
    -- produce r = q.map φ_inv_hom : G.Walk (φ.invFun (φ u)) (φ.invFun (φ v))
    -- then use left_inv to coerce back to G.Walk u v
    have hinv_u : φ.invFun (φ u) = u := φ.left_inv u
    have hinv_v : φ.invFun (φ v) = v := φ.left_inv v
    let r := q.map φ_inv_hom
    -- r : G.Walk (φ.invFun (φ u)) (φ.invFun (φ v))
    -- = G.Walk u v after substituting hinv_u, hinv_v
    refine ⟨r.copy hinv_u hinv_v, ?_⟩
    rw [Walk.length_copy, Walk.length_map]
    exact hq

/-! ## §3. Position encoding equivariance (V17.2-T3) -/

/-- **NEW theorem (V17.2-T3).** Position encoding is permutation-equivariant:
    if φ is a graph automorphism (a bijection on vertices that preserves adjacency),
    then the position encoding of φ(v) w.r.t. the φ-image anchor set φ(A) equals
    the position encoding of v w.r.t. the original anchor set A.

    More precisely, for each anchor `a : A`, the distance from v to a in G equals
    the distance from φ(v) to φ(a) in G (since φ is an isometry by V17.2-L1).

    Proof: unfold `positionEncoding` to `G.dist`; apply `dist_iso_inv`. -/
theorem positionEncoding_equivariant {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : AnchorSet V) (v : V)
    (φ : V ≃ V) (hφ : ∀ x y, G.Adj x y ↔ G.Adj (φ x) (φ y)) :
    ∀ a : A, positionEncoding G A v a
           = positionEncoding G (A.image φ) (φ v)
               ⟨φ a.val, Finset.mem_image_of_mem φ a.property⟩ := by
  intro a
  -- Both sides reduce to G.dist _ _:
  -- LHS = G.dist v a.val
  -- RHS = G.dist (φ v) (φ a.val)   [since the anchor is φ a.val by construction]
  simp only [positionEncoding]
  -- Apply V17.2-L1: G.dist v a.val = G.dist (φ v) (φ a.val)
  exact dist_iso_inv G φ hφ v a.val

end Lutar.PositionAware
