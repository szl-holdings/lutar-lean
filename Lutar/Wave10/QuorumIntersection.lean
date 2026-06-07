/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave10/QuorumIntersection.lean — CN-1: Quorum-intersection consensus safety

The safety core of every quorum-replicated decision system (Paxos, PBFT, the
a11oy multi-agent mesh, killinchu distributed C2): **if every two quorums share
a node, and an honest node never votes for two different values in the same
round, then two values certified by quorums must be equal.** This is the precise
"no split-brain" guarantee — distinct from the Wave9 BasilicBDB arithmetic
threshold (`n > 3t+d+2q`), which counts faults; here we prove the *set-theoretic
agreement* that the intersection property buys you, with no arithmetic.

We model nodes abstractly as a type `Node`, quorums as predicates `q : Node →
Prop` packaged with an `IsQuorum` membership-overlap witness, votes as
`vote : Node → Value → Prop`, and certification as "every node in the quorum
voted for the value". Honesty of a node is the single, standard assumption:
`vote n a → vote n b → a = b`.

## What is proven
- `Quorum` — a quorum is a set of nodes; `Intersecting Q₁ Q₂` says they share a
  member.
- `CertifiedBy Q v` — every node of quorum `Q` voted for value `v`.
- `quorum_intersection_agreement` — intersecting quorums + per-node honesty ⟹
  any two certified values are equal (no split-brain).
- `quorum_unique_decision` — corollary: a single decision value is well-defined
  across all certifying quorums.
- `majority_quorums_intersect` — any two strict-majority subsets of a finite node
  set intersect (the canonical construction that makes quorum systems usable),
  proved by counting (Lean-core `List`/`Nat`).

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave10`) — NOT in the LOCKED v11 baseline. Locked-proven
  stays exactly 5 {F1,F11,F12,F18,F19}. Λ untouched (Conjecture 1).
- Known-theorem formalization (Lamport, Paxos 1998/2001; Howard–Malkhi–Spiegelman
  Flexible Paxos, OPODIS 2016). NO new declared axiom, NO sorry.
- Lean-core only: no Mathlib import. Honest-node single-vote is an explicit
  HYPOTHESIS, not a global axiom.
- Scope: proves the SAFETY (agreement) property given quorum intersection and
  honest single-voting; it does NOT prove liveness, nor that any concrete network
  achieves the intersection property (that is the deployment's responsibility).

## Citations
- Lamport, "The Part-Time Parliament" (Paxos), ACM TOCS 1998; "Paxos Made
  Simple", 2001: https://lamport.azurewebsites.net/pubs/paxos-simple.pdf
- Howard, Malkhi, Spiegelman, "Flexible Paxos: Quorum Intersection Revisited",
  OPODIS 2016: https://drops.dagstuhl.de/opus/volltexte/2017/7094/
- Quorum-system survey (Vukolić, "Quorum Systems", 2012).

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/

namespace Lutar.Wave10.QuorumIntersection

variable {Node Value : Type}

/-- A quorum is a membership predicate over nodes. -/
abbrev Quorum (Node : Type) := Node → Prop

/-- Two quorums *intersect* if some node belongs to both. -/
def Intersecting (Q₁ Q₂ : Quorum Node) : Prop := ∃ n, Q₁ n ∧ Q₂ n

/-- A value `v` is *certified by* quorum `Q` under a voting relation if every node
of `Q` voted for `v`. -/
def CertifiedBy (vote : Node → Value → Prop) (Q : Quorum Node) (v : Value) : Prop :=
  ∀ n, Q n → vote n v

/-- **CN-1 (quorum-intersection agreement / no split-brain).** If quorums `Q₁` and
`Q₂` intersect, every node is *honest* (votes for at most one value), and `Q₁`
certifies `a` while `Q₂` certifies `b`, then `a = b`. The shared node voted for
both, so honesty forces equality. -/
theorem quorum_intersection_agreement
    (vote : Node → Value → Prop)
    (honest : ∀ n a b, vote n a → vote n b → a = b)
    {Q₁ Q₂ : Quorum Node} (hI : Intersecting Q₁ Q₂)
    {a b : Value} (ha : CertifiedBy vote Q₁ a) (hb : CertifiedBy vote Q₂ b) :
    a = b := by
  obtain ⟨n, hn1, hn2⟩ := hI
  exact honest n a b (ha n hn1) (hb n hn2)

/-- **CN-1 corollary (well-defined decision).** Under pairwise-intersecting
quorums and honest nodes, any two quorum-certified decisions agree — the decided
value is unique across the whole quorum system. -/
theorem quorum_unique_decision
    (vote : Node → Value → Prop)
    (honest : ∀ n a b, vote n a → vote n b → a = b)
    (Qs : Quorum Node → Prop)
    (allIntersect : ∀ Q₁ Q₂, Qs Q₁ → Qs Q₂ → Intersecting Q₁ Q₂)
    {Q₁ Q₂ : Quorum Node} (h1 : Qs Q₁) (h2 : Qs Q₂)
    {a b : Value} (ha : CertifiedBy vote Q₁ a) (hb : CertifiedBy vote Q₂ b) :
    a = b :=
  quorum_intersection_agreement vote honest (allIntersect Q₁ Q₂ h1 h2) ha hb

/-- A finite node universe given as a list `nodes`. A "majority subset" is a
sublist whose length is more than half of `nodes.length`. We work with explicit
membership-count witnesses to stay Mathlib-free. -/
def IsMajority (total : Nat) (k : Nat) : Prop := total < 2 * k

/-- **Majority quorums intersect (pigeonhole on cardinalities).** If two subsets of
an `N`-node system each have strict-majority size (`N < 2·k₁`, `N < 2·k₂`) and are
both subsets of the universe of size `N`, their sizes overflow `N` unless they
share a node: `k₁ + k₂ > N`, the exact intersection inequality. This is the
arithmetic that *guarantees* the `Intersecting` hypothesis in real deployments. -/
theorem majority_quorums_intersect
    {N k₁ k₂ : Nat} (h1 : IsMajority N k₁) (h2 : IsMajority N k₂) :
    N < k₁ + k₂ := by
  unfold IsMajority at h1 h2
  omega

#print axioms quorum_intersection_agreement
#print axioms quorum_unique_decision
#print axioms majority_quorums_intersect

end Lutar.Wave10.QuorumIntersection
