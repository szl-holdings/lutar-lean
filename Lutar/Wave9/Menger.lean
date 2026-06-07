/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave9/Menger.lean — GT-1: Menger-style cut/path duality (cut side)

The route-redundancy ⇄ failure-containment bridge for a tactical mesh, stated
over Mathlib's `SimpleGraph` and `Walk`. We machine-check the two HALVES of
Menger's theorem that hold WITHOUT the hard min-max construction (which Mathlib
does not yet provide), i.e. the parts that are genuinely closable:

  * **Cut ⟹ disconnection** (`cut_blocks_reachable`): if a vertex set `X` meets the
    support of EVERY `u`–`v` walk, then deleting `X` destroys all `u`–`v` walks —
    a cut isolates the fault domain. (Here `u, v ∉ X`.)
  * **Disjoint routes ⟹ cut lower bound** (`disjoint_paths_le_cut`, the EASY
    direction of Menger): if there are `k` walks whose supports are pairwise
    disjoint, and `X` is a cut hitting every one of them, then `k ≤ |X|`.
    Concretely we build an injection `Fin k ↪ X`, so route redundancy `k` forces
    any containing cut to spend at least `k` vertices.

The HARD direction (a cut of size `< k` ⟹ `< k` disjoint paths, i.e. the full
max-flow/min-cut equality) is the documented ROADMAP; Mathlib has no Menger
theorem, so we do not fabricate it.

## What is proven
- `cut_blocks_reachable` — `X` meets every `u`–`v` walk support ⟹ no walk avoids
  `X`; equivalently the `X`-deleted graph has no `u`–`v` walk.
- `disjoint_paths_le_cut` — `k` support-disjoint walks + a hitting cut `X` ⟹
  `k ≤ X.card` (route redundancy lower-bounds cut size).

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave9`) — NOT in the LOCKED v11 baseline. Locked-proven
  stays exactly 5 {F1,F11,F12,F18,F19}. Λ untouched (Conjecture 1).
- Known-theorem formalization (Menger 1927; the two non-min-max halves). Backed
  by Mathlib `SimpleGraph.Walk`.
- NO new declared axiom, NO sorry in any theorem body.
- Scope: this is the path-vs-cut duality CORE, not full min-max Menger and not an
  efficient algorithm; per the GT-1 risk note the general directed/weighted and
  the tight min-max equality remain ROADMAP.

## Citations
- Menger, "Zur allgemeinen Kurventheorie", Fund. Math. 10 (1927).
- Menger's theorem (background): https://en.wikipedia.org/wiki/Menger%27s_theorem
- "A coarse Menger's Theorem for planar and bounded genus graphs",
  arXiv:2605.11112: https://arxiv.org/abs/2605.11112
- Mathlib SimpleGraph connectivity:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Connectivity/Subgraph.html

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Finite

open SimpleGraph

namespace Lutar.Wave9.Menger

variable {V : Type*} {G : SimpleGraph V}

/-- A vertex set `X` is a `u`–`v` **cut** if it meets the support of every
`u`–`v` walk. (Route ⇒ some vertex of the route lies in `X`.) -/
def IsCut (G : SimpleGraph V) (u v : V) (X : Set V) : Prop :=
  ∀ p : G.Walk u v, ∃ x ∈ X, x ∈ p.support

/-- **GT-1 (cut ⟹ disconnection).** If `X` is a `u`–`v` cut, then there is NO
`u`–`v` walk whose support avoids `X`: deleting the cut isolates the endpoints.
Contrapositive of `IsCut`. -/
theorem cut_blocks_reachable {u v : V} {X : Set V}
    (hcut : IsCut G u v X) :
    ¬ ∃ p : G.Walk u v, ∀ x ∈ p.support, x ∉ X := by
  rintro ⟨p, hp⟩
  obtain ⟨x, hxX, hxp⟩ := hcut p
  exact hp x hxp hxX

/-- **GT-1 (easy Menger inequality: disjoint routes ⟹ cut lower bound).**
Given `k` walks `route i : G.Walk u v` whose SUPPORTS are pairwise disjoint, and
a finite cut `X` that hits every one of them, we have `k ≤ X.card`. The cut must
spend a distinct vertex on each disjoint route.

Proof: each route `i` is hit by a chosen cut vertex `f i ∈ X` lying on
`route i`. Disjoint supports make `i ↦ f i` injective into `X`, so
`Fintype.card (Fin k) = k ≤ X.card`. -/
theorem disjoint_paths_le_cut [DecidableEq V] {u v : V} {k : ℕ}
    (route : Fin k → G.Walk u v)
    (hdisj : ∀ i j, i ≠ j →
      ∀ x, x ∈ (route i).support → x ∉ (route j).support)
    {X : Finset V}
    (hhit : ∀ i, ∃ x ∈ X, x ∈ (route i).support) :
    k ≤ X.card := by
  classical
  -- pick a hitting cut vertex on each route
  choose f hfX hfsupp using hhit
  -- the chooser is injective: distinct routes share no support vertex
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    -- f i = f j lies on both route i and route j, contradicting disjointness
    have hi : f i ∈ (route i).support := hfsupp i
    have hj : f j ∈ (route j).support := hfsupp j
    rw [hij] at hi
    exact hdisj i j hne (f j) hi hj
  -- an injection Fin k ↪ X gives k ≤ |X|
  have : Fintype.card (Fin k) ≤ X.card := by
    have hmap : ∀ i, f i ∈ X := hfX
    calc Fintype.card (Fin k)
        ≤ Fintype.card X :=
          Fintype.card_le_of_injective (fun i => ⟨f i, hmap i⟩)
            (fun i j h => hinj (by simpa using h))
      _ = X.card := Fintype.card_coe X
  simpa using this

#print axioms cut_blocks_reachable
#print axioms disjoint_paths_le_cut

end Lutar.Wave9.Menger
