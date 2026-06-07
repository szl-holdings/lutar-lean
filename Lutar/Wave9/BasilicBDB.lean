/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave9/BasilicBDB.lean — C1: Basilic / ZLB Byzantine–Deceitful–Benign threshold

The sharp consensus threshold for the Byzantine–Deceitful–Benign (BDB) fault
model of Bouhata–Gramoli et al. (Basilic, arXiv:2305.02498): with `t` Byzantine,
`d` deceitful, and `q` benign (crash) faults, quorum-based consensus needs

  `n > 3t + d + 2q`   (equivalently `n ≥ 3t + d + 2q + 1`).

We machine-check the QUORUM-INTERSECTION ARITHMETIC that makes this bound sharp —
the rigorous core of the lower bound and its tightness — as a self-contained,
Mathlib-free `Nat` development. Two quorums each of size `n - (t + q)` (a quorum
waits past the `t` Byzantine and `q` benign it may never hear) must intersect in
strictly more than `t + d` nodes, so they share at least one CORRECT
(non-Byzantine, non-deceitful) node, which is exactly what defeats the
split-brain / equivocation adversary.

## What is proven
- `bdb_safe` (TIGHTNESS / sufficiency arithmetic): if `n > 3t + d + 2q` then any
  two quorums of size `n - (t + q)` intersect in `> t + d` nodes — i.e.
  `2 * (n - (t + q)) > n + (t + d)` — so a correct node is common to both
  quorums. This is the quorum-intersection inequality the Basilic protocol class
  relies on to SOLVE consensus above the threshold.
- `bdb_quorum_intersection_correct`: restated as a positive intersection size
  `2*(n-(t+q)) - n > t + d`, the count of guaranteed-correct shared nodes.
- `bdb_impossible_boundary` (LOWER BOUND, boundary): if `n ≤ 3t + d + 2q` then
  the quorum-intersection inequality FAILS (`2*(n-(t+q)) ≤ n + (t+d)`), so two
  quorums need NOT share any correct node — the adversary can equivocate and
  consensus is impossible by the standard partition argument.

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave9`) — NOT in the LOCKED v11 baseline. Locked-proven
  stays exactly 5 {F1,F11,F12,F18,F19}. Λ untouched (Conjecture 1).
- Known-theorem formalization (Basilic BDB bound, arXiv:2305.02498). This proves
  the QUORUM-INTERSECTION ARITHMETIC that is necessary and sufficient for the
  threshold; it is NOT a formalization of the full Basilic protocol or its
  network-level liveness (that is ROADMAP, per the C1 risk note).
- Lean-core only (`omega`); NO Mathlib, NO new declared axiom, NO sorry.

## Citations
- Bouhata, Gramoli et al., "Basilic: Resilient Optimal Consensus Protocols With
  Benign and Deceitful Faults", arXiv:2305.02498: https://arxiv.org/abs/2305.02498

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/

namespace Lutar.Wave9.BasilicBDB

/-- A quorum waits for `n - (t + q)` responses: it can never be sure to hear the
`t` Byzantine nor the `q` benign/crashed nodes, so it proceeds on the rest. -/
def quorumSize (n t q : Nat) : Nat := n - (t + q)

/-- **C1 sufficiency (tightness above threshold).** When `n > 3t + d + 2q`, two
quorums of size `n - (t + q)` overlap in strictly more than `t + d` nodes:
`2 * quorumSize > n + (t + d)`. Hence their intersection contains a node that is
neither Byzantine (`t`) nor deceitful (`d`) — a CORRECT shared node, which is
what lets the protocol class solve consensus. -/
theorem bdb_safe {n t d q : Nat} (h : n > 3 * t + d + 2 * q) :
    2 * quorumSize n t q > n + (t + d) := by
  unfold quorumSize
  omega

/-- **C1 intersection count.** The guaranteed overlap of two quorums,
`2 * quorumSize - n`, strictly exceeds `t + d` above the threshold — the count of
shared nodes that must include at least one correct node. -/
theorem bdb_quorum_intersection_correct {n t d q : Nat}
    (h : n > 3 * t + d + 2 * q) :
    2 * quorumSize n t q - n > t + d := by
  unfold quorumSize
  omega

/-- **C1 lower bound (boundary impossibility arithmetic).** At or below the
threshold `n ≤ 3t + d + 2q`, the quorum-intersection inequality FAILS:
`2 * quorumSize ≤ n + (t + d)`. Two quorums then need not share any correct node,
so an equivocating Byzantine/deceitful adversary can present inconsistent views
to two non-overlapping (in correct nodes) quorums — the partition argument that
makes consensus impossible. -/
theorem bdb_impossible_boundary {n t d q : Nat} (h : n ≤ 3 * t + d + 2 * q) :
    2 * quorumSize n t q ≤ n + (t + d) := by
  unfold quorumSize
  omega

/-- **C1 sharpness (packaged).** The threshold is a clean dichotomy: the
quorum-intersection inequality holds iff we are strictly above `3t + d + 2q`
(assuming the well-formedness `t + q ≤ n`, so quorum sizes are non-degenerate). -/
theorem bdb_threshold_dichotomy {n t d q : Nat} (hwf : t + q ≤ n) :
    (2 * quorumSize n t q > n + (t + d)) ↔ (n > 3 * t + d + 2 * q) := by
  unfold quorumSize
  omega

#print axioms bdb_safe
#print axioms bdb_quorum_intersection_correct
#print axioms bdb_impossible_boundary
#print axioms bdb_threshold_dichotomy

end Lutar.Wave9.BasilicBDB
