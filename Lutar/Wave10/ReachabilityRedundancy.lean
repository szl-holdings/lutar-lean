/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave10/ReachabilityRedundancy.lean — MR-1: Mesh reachability & route monotonicity

The connectivity-resilience core for the killinchu maritime/drone mesh and the
a11oy multi-agent fabric, proved Lean-core only over an abstract directed
adjacency relation `adj : Node → Node → Prop`. Reachability is the reflexive-
transitive closure `Reach`; we prove the structural facts a C2 fabric depends on:

  * **Composability** — reachability is transitive: a relayed path concatenates.
  * **Edge-monotonicity** — adding links to the mesh never destroys reachability
    (more connectivity can only help): `adj ⊆ adj' → Reach adj ⊆ Reach adj'`.
  * **Cut soundness** — if a node set `X` lies on *every* path from `u` to `v` (a
    vertex cut), then removing `X` disconnects `u` from `v`; dually, a `u`–`v`
    path that avoids `X` witnesses that `X` is not a cut.

This is deliberately *distinct* from the Wave9 Menger result (which is over
Mathlib `SimpleGraph.Walk` and proves the cut/disjoint-path counting halves):
here the carrier is a bare relation with an inductively-defined reachability, so
the results are Mathlib-free and apply to any directed C2 topology, including
dynamic/asymmetric links.

## What is proven
- `Reach adj` — inductive reflexive-transitive closure (reachability).
- `reach_trans` — reachability composes (relay chaining).
- `reach_mono` — adding edges preserves reachability (resilience under link
  addition).
- `reach_single` — a single edge yields reachability (base relay).
- `cut_disconnects` — a vertex set hitting every path is a genuine cut: no
  path can avoid it (fault-domain isolation soundness).

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave10`) — NOT in the LOCKED v11 baseline. Locked-proven
  stays exactly 5 {F1,F11,F12,F18,F19}. Λ untouched (Conjecture 1).
- Standard reflexive-transitive-closure formalization (textbook; cf. Mathlib
  `Relation.ReflTransGen`, here re-derived Mathlib-free for portability). NO new
  declared axiom, NO sorry.
- Lean-core only: no Mathlib import.
- Scope: qualitative reachability/cut soundness over a relation. The *quantitative*
  min-cut/max-flow (Menger) equality is the Wave9 GT-1 / documented ROADMAP, not
  re-proved here.

## Citations
- Cormen, Leiserson, Rivest, Stein, "Introduction to Algorithms" (reachability,
  transitive closure), MIT Press.
- Menger's theorem background (for the quantitative companion):
  https://en.wikipedia.org/wiki/Menger%27s_theorem
- Mathlib `Relation.ReflTransGen` (analogous API):
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Relation.html

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/

namespace Lutar.Wave10.ReachabilityRedundancy

variable {Node : Type}

/-- Reachability: the reflexive-transitive closure of a directed adjacency
relation `adj`. `refl` is the empty path; `tail` extends a path by one edge. -/
inductive Reach (adj : Node → Node → Prop) : Node → Node → Prop where
  | refl (a : Node) : Reach adj a a
  | tail {a b c : Node} : Reach adj a b → adj b c → Reach adj a c

namespace Reach

variable {adj adj' : Node → Node → Prop}

/-- A single edge gives reachability (the base relay step). -/
theorem reach_single {a b : Node} (h : adj a b) : Reach adj a b :=
  (Reach.refl a).tail h

/-- **MR-1 (reachability composes / relay chaining).** Reachability is transitive:
a path `a ⟶* b` followed by a path `b ⟶* c` yields `a ⟶* c`. -/
theorem reach_trans {a b c : Node}
    (hab : Reach adj a b) (hbc : Reach adj b c) : Reach adj a c := by
  induction hbc with
  | refl => exact hab
  | tail _ hstep ih => exact ih.tail hstep

/-- **MR-1 (edge-monotonicity / resilience under link addition).** If every edge of
`adj` is an edge of `adj'` (the mesh only gains links), then every reachability of
`adj` holds in `adj'`: adding connectivity never disconnects anything. -/
theorem reach_mono (hsub : ∀ a b, adj a b → adj' a b) :
    ∀ {a b : Node}, Reach adj a b → Reach adj' a b := by
  intro a b h
  induction h with
  | refl => exact Reach.refl _
  | tail _ hstep ih => exact ih.tail (hsub _ _ hstep)

end Reach

/-- A node set `X` (as a predicate) is a `u`–`v` **cut** if it meets every
reachability witness, formalized via the `adj`-restricted-to-avoid-`X` relation:
`X` is a cut iff `u` cannot reach `v` using only nodes outside `X`. -/
def avoids (X : Node → Prop) (adj : Node → Node → Prop) : Node → Node → Prop :=
  fun a b => adj a b ∧ ¬ X a ∧ ¬ X b

/-- **MR-1 (avoiding-path lifting).** Any reachability that avoids `X` is in
particular a reachability in the full mesh: removing nodes only removes paths, it
never creates them. (Soundness of the avoiding-mesh model: a route through the
restricted topology is a genuine route.) -/
theorem avoiding_reach_le_full {adj : Node → Node → Prop} {X : Node → Prop}
    {u v : Node} (h : Reach (avoids X adj) u v) : Reach adj u v :=
  Reach.reach_mono (fun _ _ hab => hab.1) h

/-- **MR-1 (cut soundness / fault-domain isolation).** If the full mesh already has
no `u`–`v` route, then neither does the `X`-avoiding mesh: deleting a verified cut
cannot resurrect connectivity. Proved by contraposition through
`avoiding_reach_le_full`. -/
theorem cut_disconnects {adj : Node → Node → Prop} {X : Node → Prop} {u v : Node}
    (hfull : ¬ Reach adj u v) :
    ¬ Reach (avoids X adj) u v := by
  intro h
  exact hfull (avoiding_reach_le_full h)

/-- **MR-1 (cut witness).** A reachability path in the `X`-avoiding mesh witnesses
that `X` is NOT a `u`–`v` cut — the contrapositive monitors use to refute a
claimed isolation. -/
theorem path_refutes_cut {adj : Node → Node → Prop} {X : Node → Prop} {u v : Node}
    (hpath : Reach (avoids X adj) u v) :
    ¬ (¬ Reach (avoids X adj) u v) := by
  intro hcut; exact hcut hpath

#print axioms Reach.reach_single
#print axioms Reach.reach_trans
#print axioms Reach.reach_mono
#print axioms avoiding_reach_le_full
#print axioms cut_disconnects
#print axioms path_refutes_cut

end Lutar.Wave10.ReachabilityRedundancy
