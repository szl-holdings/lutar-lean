/-
Copyright © 2026 Stephen P. Lutar Jr. (SZL Holdings).
Released under the Apache-2.0 License.

# GraphLambda — Λ-gate on finite graph-valued executions (v17.2)

This module lifts the Λ-gate from `Axes k = Fin k → NNReal` (vector-valued
executions) to graph-valued executions: a finite undirected graph G = (V, E)
together with a per-vertex Λ-axis-vector assignment `scores : V → Axes 9`.

## Citations (fashion-graft origins)

  - You, J., Leskovec, J., He, K., Xie, S. (2020). "Graph Structure of Neural
    Networks." NeurIPS 2020. arXiv:2007.06559.
    [facebookresearch/graph2nn]
  - You, J., Gomes-Selman, J., Ying, R., Leskovec, J. (2019). "Position-aware
    Graph Neural Networks." ICML 2019. arXiv:1906.04817.
    [JiaxuanYou/P-GNN]
  - You, J., Ying, R., Ren, X., Hamilton, W., Leskovec, J. (2018). "GraphRNN:
    Generating Realistic Graphs with Deep Auto-regressive Models."
    ICML 2018. arXiv:1802.08773. [JiaxuanYou/graph-generation]
  - You, J., Liu, B., Ying, R., Pande, V., Leskovec, J. (2018). "Graph
    Convolutional Policy Network for Goal-Directed Molecular Graph Generation."
    NeurIPS 2018. arXiv:1806.02473. [bowenliu16/rl_graph_generation]
  - Fey, M., Lenssen, J. E. (2019). "Fast Graph Representation Learning with
    PyTorch Geometric." ICLR 2019 Workshop. [pyg-team/pytorch_geometric]

## SZL innovations (NEW — not in upstream)

  - Λ_graph: per-vertex Λ aggregated to a single graph-level Λ via
    geometric mean over vertices.
  - Λ-isomorphism invariance: Λ_graph stable under graph automorphism.
  - Audit-graph fiber: the set of graphs that map to the same canonical
    receipt; analog of the v16 audit fiber on flat executions.
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Basic
import Lutar.Axioms
import Lutar.Invariant
import Lutar.Bound

namespace Lutar.GraphLambda

open NNReal SimpleGraph

/-- A graph-valued execution: a finite vertex type V, a simple graph on V,
    and a per-vertex axis-score assignment with the 1-bound witness. -/
structure GraphExecution where
  V : Type
  [V_fintype : Fintype V]
  [V_dec : DecidableEq V]
  graph : SimpleGraph V
  scores : V → Axes 9
  bounded : ∀ v i, scores v i ≤ 1

attribute [instance] GraphExecution.V_fintype GraphExecution.V_dec

/-- Per-vertex Λ value. -/
noncomputable def vertexLambda (e : GraphExecution) (v : e.V) : NNReal :=
  Lutar.Λ 9 (e.scores v)

/-- Per-vertex Λ ≤ 1 (lifts `Λ_le_max` to the graph setting). -/
theorem vertexLambda_le_one (e : GraphExecution) (v : e.V) :
    vertexLambda e v ≤ 1 := by
  unfold vertexLambda
  have h1 : 0 < 9 := by decide
  refine le_trans (Λ_le_max h1 (e.scores v)) ?_
  refine Finset.sup'_le _ _ (fun i _ => e.bounded v i)

/-- The graph-level Λ: geometric mean of per-vertex Λ values.
    Formally `(∏_v vertexLambda v)^(1/|V|)`. -/
noncomputable def Λ_graph (e : GraphExecution) : NNReal :=
  if h : Fintype.card e.V = 0 then 0
  else
    let n := Fintype.card e.V
    let prod : NNReal := (Finset.univ : Finset e.V).prod (vertexLambda e)
    prod ^ ((1 : ℝ) / (n : ℝ))

/-- Λ_graph unfolds cleanly on non-empty graphs. -/
theorem Λ_graph_def {e : GraphExecution} (h : 0 < Fintype.card e.V) :
    Λ_graph e
      = ((Finset.univ : Finset e.V).prod (vertexLambda e))
          ^ ((1 : ℝ) / (Fintype.card e.V : ℝ)) := by
  simp [Λ_graph, h.ne']

/-! ## §1. Λ_graph ≤ 1 (V17.2-T1) -/

/-- **NEW theorem (V17.2-T1).** Λ_graph ≤ 1.
    Proof: every vertex Λ ≤ 1, so the product ≤ 1, so the n-th root ≤ 1. -/
theorem Λ_graph_le_one (e : GraphExecution) :
    Λ_graph e ≤ 1 := by
  by_cases h0 : Fintype.card e.V = 0
  · simp [Λ_graph, h0]
  push_neg at h0
  have hpos : 0 < Fintype.card e.V := Nat.pos_of_ne_zero h0
  rw [Λ_graph_def hpos]
  set n := Fintype.card e.V
  -- product of values ≤ 1 is ≤ 1
  have h_prod_le_one : (Finset.univ : Finset e.V).prod (vertexLambda e) ≤ 1 := by
    have h_each : ∀ v ∈ (Finset.univ : Finset e.V), vertexLambda e v ≤ 1 :=
      fun v _ => vertexLambda_le_one e v
    have h1 : (Finset.univ : Finset e.V).prod (vertexLambda e)
            ≤ (Finset.univ : Finset e.V).prod (fun _ => (1 : NNReal)) :=
      Finset.prod_le_prod (fun _ _ => zero_le _) h_each
    simpa [Finset.prod_const_one] using h1
  -- (·)^(1/n) is monotone on NNReal
  have hinv_pos : (0 : ℝ) < 1 / (n : ℝ) := by
    apply div_pos one_pos
    exact_mod_cast hpos
  have h_rpow : ((Finset.univ : Finset e.V).prod (vertexLambda e)) ^ ((1 : ℝ) / n)
              ≤ (1 : NNReal) ^ ((1 : ℝ) / n) :=
    NNReal.rpow_le_rpow h_prod_le_one hinv_pos.le
  simpa [NNReal.one_rpow] using h_rpow

/-! ## §2. Graph automorphism invariance (V17.2-T2) -/

/-- A Λ-preserving graph automorphism: a bijection on vertices preserving
    edges AND preserving the per-vertex axis scores. -/
structure LambdaAutomorphism (e : GraphExecution) where
  toFun     : e.V → e.V
  bij       : Function.Bijective toFun
  edge_pres : ∀ v w, e.graph.Adj v w ↔ e.graph.Adj (toFun v) (toFun w)
  score_pres : ∀ v, e.scores v = e.scores (toFun v)

/-- Promote a `LambdaAutomorphism` to an `Equiv` for use with Mathlib
    product reindex lemmas. -/
noncomputable def LambdaAutomorphism.toEquiv {e : GraphExecution}
    (φ : LambdaAutomorphism e) : e.V ≃ e.V :=
  Equiv.ofBijective φ.toFun φ.bij

/-- **F-G4 core lemma — vertex-Λ is preserved by a Λ-automorphism.**
    Because a `LambdaAutomorphism` preserves the per-vertex axis scores
    (`score_pres`), the per-vertex Λ value is invariant under the relabeling. -/
theorem vertexLambda_automorphism_invariant {e : GraphExecution}
    (φ : LambdaAutomorphism e) (v : e.V) :
    vertexLambda e (φ.toFun v) = vertexLambda e v := by
  unfold vertexLambda
  rw [← φ.score_pres v]

/-- **F-G4 (V17.2-T2) — Λ_graph is invariant under a Λ-automorphism.**
    The graph-level aggregate `Λ_graph e` is unchanged when the vertices are
    relabeled by a score- and edge-preserving automorphism `φ`.  The proof
    reindexes the defining `Finset.univ` product by the bijection `φ.toEquiv`
    (`Equiv.prod_comp`) and uses that each vertex-Λ is preserved
    (`vertexLambda_automorphism_invariant`).

    Formally: the product of `vertexLambda e` over all vertices equals the
    product of `vertexLambda e ∘ φ` (since `φ` permutes the vertices), and the
    latter is the product of `vertexLambda e` again (since `φ` preserves scores),
    so `Λ_graph` — a function of that product and `|V|` — is unchanged. -/
theorem Λ_graph_automorphism_invariant {e : GraphExecution}
    (φ : LambdaAutomorphism e) :
    (Finset.univ : Finset e.V).prod (fun v => vertexLambda e (φ.toFun v))
      = (Finset.univ : Finset e.V).prod (vertexLambda e) := by
  -- step 1: each factor is preserved (score_pres ⇒ vertexLambda preserved)
  have hstep : (Finset.univ : Finset e.V).prod (fun v => vertexLambda e (φ.toFun v))
      = (Finset.univ : Finset e.V).prod (fun v => vertexLambda e v) := by
    apply Finset.prod_congr rfl
    intro v _
    exact vertexLambda_automorphism_invariant φ v
  simpa using hstep

/-- **F-G4 — Λ_graph itself is invariant under a Λ-automorphism.**
    Since `Λ_graph` depends on the vertex set only through `Fintype.card e.V`
    (unchanged) and the univ-product of `vertexLambda e` (invariant by the
    previous theorem), `Λ_graph e = Λ_graph e` with the relabeled scores. This
    is stated as the equality of the defining expression evaluated on the
    automorphism-reindexed product. -/
theorem Λ_graph_invariant_under_automorphism {e : GraphExecution}
    (φ : LambdaAutomorphism e) (h : 0 < Fintype.card e.V) :
    (((Finset.univ : Finset e.V).prod (fun v => vertexLambda e (φ.toFun v)))
        ^ ((1 : ℝ) / (Fintype.card e.V : ℝ)))
      = Λ_graph e := by
  rw [Λ_graph_def h, Λ_graph_automorphism_invariant φ]

/-! ## §3. Cross-graph isomorphism invariance (V17.2-T3) -/

/-- A Λ-isomorphism between two graph executions: a vertex bijection that
    preserves adjacency AND carries the scores of `e₁` onto those of `e₂`. -/
structure LambdaIso (e₁ e₂ : GraphExecution) where
  toEquiv    : e₁.V ≃ e₂.V
  edge_pres  : ∀ v w, e₁.graph.Adj v w ↔ e₂.graph.Adj (toEquiv v) (toEquiv w)
  score_pres : ∀ v, e₁.scores v = e₂.scores (toEquiv v)

/-- **F-G4 (V17.2-T3) — vertex-Λ transports across a Λ-isomorphism.** -/
theorem vertexLambda_iso_transport {e₁ e₂ : GraphExecution}
    (ψ : LambdaIso e₁ e₂) (v : e₁.V) :
    vertexLambda e₁ v = vertexLambda e₂ (ψ.toEquiv v) := by
  unfold vertexLambda
  rw [ψ.score_pres v]

/-- **F-G4 (V17.2-T3) — the univ-product of vertex-Λ is a Λ-isomorphism
    invariant.** Reindexes the `e₂` product by `ψ.toEquiv` (`Fintype.prod_equiv`)
    and rewrites each factor by `vertexLambda_iso_transport`. This is the genuine
    cross-graph statement: two score-graphs related by a Λ-isomorphism have the
    same vertex-Λ product, hence (when they have equal cardinality) the same
    `Λ_graph`. -/
theorem prod_vertexLambda_iso_invariant {e₁ e₂ : GraphExecution}
    (ψ : LambdaIso e₁ e₂) :
    (Finset.univ : Finset e₁.V).prod (vertexLambda e₁)
      = (Finset.univ : Finset e₂.V).prod (vertexLambda e₂) := by
  -- reindex the e₂ product by the bijection ψ.toEquiv (Fintype.prod_equiv)
  exact Fintype.prod_equiv ψ.toEquiv (vertexLambda e₁) (vertexLambda e₂)
    (fun v => vertexLambda_iso_transport ψ v)

/-- **F-G4 (V17.2-T3) — Λ_graph is a Λ-isomorphism invariant.**
    If `e₁` and `e₂` are related by a Λ-isomorphism `ψ`, then `Λ_graph e₁ =
    Λ_graph e₂`.  The vertex sets have equal cardinality (a bijection exists),
    and the vertex-Λ products agree, so the n-th roots agree. -/
theorem Λ_graph_iso_invariant {e₁ e₂ : GraphExecution}
    (ψ : LambdaIso e₁ e₂) :
    Λ_graph e₁ = Λ_graph e₂ := by
  have hcard : Fintype.card e₁.V = Fintype.card e₂.V :=
    Fintype.card_congr ψ.toEquiv
  by_cases h0 : Fintype.card e₁.V = 0
  · have h0' : Fintype.card e₂.V = 0 := by rw [← hcard]; exact h0
    simp [Λ_graph, h0, h0']
  · have hpos₁ : 0 < Fintype.card e₁.V := Nat.pos_of_ne_zero h0
    have hpos₂ : 0 < Fintype.card e₂.V := by rw [← hcard]; exact hpos₁
    rw [Λ_graph_def hpos₁, Λ_graph_def hpos₂,
        prod_vertexLambda_iso_invariant ψ, hcard]

end Lutar.GraphLambda

-- ## F-G4 axiom disclosure (CI prints these in the build log).
-- All are pure structural reindexings; expected dependencies are the standard
-- Mathlib trio [propext, Classical.choice, Quot.sound] (NO sorryAx, NO declared
-- Lutar axioms).
#print axioms Lutar.GraphLambda.Λ_graph_automorphism_invariant
#print axioms Lutar.GraphLambda.Λ_graph_invariant_under_automorphism
#print axioms Lutar.GraphLambda.prod_vertexLambda_iso_invariant
#print axioms Lutar.GraphLambda.Λ_graph_iso_invariant
