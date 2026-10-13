<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SZL Holdings — Formula-Graph Self-Repair Convergence · refuted statement and open obligations -->

# Self-Repair Convergence — SR-1 refuted as stated

> **Status, 2026-10-10.** The written SR-1 claim is **false as stated**. The counterexample below is an exact rational check of that written synchronous update. It is not a test of a deployed repair endpoint, not a Lean proof, and not evidence of service recovery or biological healing.
>
> This note does **not** establish that any Python repair function implements the equation. Endpoint correspondence remains **UNKNOWN** until a pinned source, numeric representation, and refinement check exist.
>
> **Doctrine:** v11 — locked-proven stays exactly 8 `{F1,F4,F7,F11,F12,F18,F19,F22}`. This correction adds nothing to that count. Λ-Aggregator Uniqueness remains Conjecture 1.

## The written update

Over an undirected graph \(G=(V,E)\) with a designated permanently-down (lesioned) node \(d\), each non-lesioned node carries a health value \(s_i \in [0,1]\), updated synchronously by neighbor-averaging toward its live neighbors:

\[
s_i^{(t+1)} \;=\; \mathrm{clip}_{[0,1]}\!\Big(s_i^{(t)} + \rho\big(\bar{s}_{\mathcal N_i}^{(t)} - s_i^{(t)}\big)\Big),
\qquad s_d^{(t)} = 0 \ \forall t,
\]

where \(\rho \in (0,1]\), \(\mathcal N_i\) are \(i\)'s live neighbors (excluding \(d\) and any node below a liveness floor), and \(\bar{s}_{\mathcal N_i}\) is their mean health (\(=s_i\) if \(i\) has no live neighbor).

## SR-1 is refuted as stated

**Refuted statement.** If the post-lesion graph \(G \setminus \{d\}\) is connected and at least one non-lesioned node starts at full health, then for any \(\rho \in (0,1]\) every non-lesioned health tends to \(1\).

Do not encode that statement as a proof obligation. Do not make it true by weakening a test or adding an axiom.

**Counterexample.** Start from the path \(d-a-b\) and lesion \(d\). The survivor graph is the edge \(a-b\). Take \(s_a(0)=1\), \(s_b(0)=9/10\), and any liveness floor at or below \(9/10\). Both survivors stay live, and clipping stays inactive.

- At \(\rho=1/2\), one step reaches \((19/20,19/20)\) and stays there. The field does not tend to \((1,1)\).
- At \(\rho=1\), \((1,9/10)\) alternates with \((9/10,1)\).

`tests/test_self_repair_sr1_counterexample.py` checks both trajectories with `fractions.Fraction`.

## Statements that remain proposals

These are replacement targets. None is Lean-verified. None is a runtime measurement. None restores the refuted claim.

**Proposed SR-1a, unforced consensus.** On a finite connected undirected survivor graph with at least two vertices, synchronous updates, constant \(0<\rho<1\), and every survivor initially at or above the liveness floor, health stays inside the initial range and approaches the degree-weighted mean of the initial field. The ordinary arithmetic mean is conserved only under an extra condition, such as a regular graph or a doubly stochastic update. If any survivor starts below \(1\), that weighted mean is below \(1\).

**Proposed SR-1b, pinned healthy boundary.** Change the mechanism: hold a nonempty anchor set at health \(1\), and update every other node by the original average. Require each free node to have a path to an anchor. The maximum deficit among free nodes can then be shown to contract over blocks of steps. An individual node need not improve at every step. A component with no anchor can stay at a constant below \(1\). This is a different model.

**Open SR-2, locked coordinates.** The unmodified average preserves a locked value \(1\) only when that node's live-neighbor mean is already \(1\), including the no-neighbor fallback. A locked label by itself does nothing. Preservation has to be part of the transition, initialized at \(1\), and proved. Assigning a constant health score does not show that a locked artifact stayed valid.

**Open SR-3, articulation.** For a finite simple undirected graph that starts connected and has at least three vertices, the second-smallest eigenvalue of the unnormalized Laplacian of \(G\setminus\{d\}\) is zero exactly when that survivor graph is disconnected, which is exactly when \(d\) is an articulation point. Without the original-connectivity hypothesis, deleting a vertex from one of two disjoint components can give eigenvalue zero even though that vertex was not an articulation point. Fewer than two surviving vertices needs its own convention. A floating-point near-zero is not an exact disconnection certificate. The machine-checked statement over the repository's concrete graph representation is still open.

## What a later proof may not say

A scalar health trajectory is not a service-recovery experiment. Bounded attempt counts, including runs in which every test fails, establish stopping, not successful repair. Promotion still requires a machine-checked proof of a stated, non-refuted claim. This document does not supply that proof.

## References

- Counterexample test: `tests/test_self_repair_sr1_counterexample.py`
- Fiedler, "Algebraic connectivity of graphs" (1973), Czechoslovak Mathematical Journal.
- Growing Neural Cellular Automata (Mordvintsev, Randazzo, Niklasson, Levin; Distill, 2020): <https://distill.pub/2020/growing-ca/>. That work studies learned regenerative update rules. It does not establish convergence of the scalar average above.
- Bounty convention: [`BOUNTY.md`](../BOUNTY.md). Unconditional Λ uniqueness stays a separate refuted-as-stated claim.
