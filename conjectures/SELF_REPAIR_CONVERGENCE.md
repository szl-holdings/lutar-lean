<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SZL Holdings — Formula-Graph Self-Repair Convergence · proposed conjecture for lutar-lean -->

# Self-Repair Convergence — Proposed Conjecture (OPEN)

> **Honest posture.** The Formula-Graph Brain's self-repair dynamics (Wave 16,
> served MODELED at `/api/killinchu/v1/fgbrain/repair`) are working, deterministic
> Python — but they have **no Lean statement**, not even as a declared open
> obligation. This document proposes the convergence property as a **new
> conjecture** for `lutar-lean`, so the mechanism enters the proof-tracking system
> honestly (as a CONJECTURE with a stated obligation) instead of living outside it.
> Until a machine-checked proof lands, this is **NOT a theorem** and the `/repair`
> endpoint continues to serve `label:"MODELED"`.

- **Doctrine:** v11 — locked-proven = exactly 8 `{F1,F4,F7,F11,F12,F18,F19,F22}`; this proposal adds **nothing** to that count. It proposes a new *conjecture*, not a locked formula.
- **Mechanism source:** `killinchu_organism.self_repair()` (Growing-NCA local-diffusion rule), re-expressed over the formula graph in `szl_fgbrain.py` (Wave 16).
- **Closes:** org-sweep Gap #2 (self-repair dynamics untracked in the proof system).

---

## The mechanism (what is actually computed)

Over an undirected graph \(G=(V,E)\) with a designated permanently-down (lesioned)
node \(d\), each non-lesioned node carries a health value \(s_i \in [0,1]\), updated
synchronously each step by neighbor-averaging toward its live neighbors:

\[
s_i^{(t+1)} \;=\; \mathrm{clip}_{[0,1]}\!\Big(s_i^{(t)} + \rho\big(\bar{s}_{\mathcal N_i}^{(t)} - s_i^{(t)}\big)\Big),
\qquad s_d^{(t)} = 0 \ \forall t,
\]

where \(\rho \in (0,1]\) is the repair rate, \(\mathcal N_i\) are \(i\)'s live
neighbors (excluding \(d\) and any node below a liveness floor), and
\(\bar{s}_{\mathcal N_i}\) is their mean health (\(=s_i\) if \(i\) has no live
neighbor). Connectivity of the post-lesion graph is measured by the Fiedler value
\(\lambda_2\) (second-smallest eigenvalue of the graph Laplacian).

## The conjectures

**Conjecture SR-1 (Neighborhood recovery).** If the post-lesion graph
\(G \setminus \{d\}\) is connected (\(\lambda_2 > 0\)) and at least one non-lesioned
node starts at full health, then for any \(\rho \in (0,1]\) the health field
converges: every non-lesioned node's health tends to \(1\) as \(t \to \infty\)
(the lesioned node stays pinned at \(0\)). Formally, \(\forall i \neq d,\ s_i^{(t)} \to 1\).

**Conjecture SR-2 (Canon is a fixed point).** The locked-proven core is a fixed
point of the dynamics: if no locked node is the lesion, every locked node's health
remains \(1\) for all \(t\) (the repair rule never *lowers* a fully-healthy proven
node). This is the dynamical-systems form of the doctrine invariant already
asserted in code (`locked_untouched`).

**Conjecture SR-3 (Cut-vertex detection soundness).** \(\lambda_2(G\setminus\{d\}) = 0\)
iff \(d\) is an articulation point (cut-vertex) of \(G\) — i.e. the `/repair`
endpoint's `still_connected_after_lesion` flag is sound. (This direction is close
to a standard spectral-graph result; SR-3 asks for the machine-checked version over
the concrete graph representation.)

```lean
-- Sketch of the target statement for SR-1 (informal; real statement pins the
-- graph/health representation used in lutar-lean).
theorem self_repair_neighborhood_recovery
    (G : SimpleGraph V) (d : V) (ρ : ℝ) (hρ : 0 < ρ ∧ ρ ≤ 1)
    (hconn : Connected (G.deleteVertex d))
    (hseed : ∃ i, i ≠ d ∧ health0 i = 1) :
    ∀ i, i ≠ d → Filter.Tendsto (fun t => healthStep^[t] health0 i) Filter.atTop (nhds 1) := by
  sorry  -- ← proposed obligation
```

## Why it belongs in the tracker now

The mechanism is already serving MODELED output and is depended on by the Wave 16
surface. Per Doctrine v11, every claim should trace to a proof status. Today
`self_repair()` has none — it is neither PROVEN, AXIOM, SORRY, nor a declared
CONJECTURE. Filing SR-1..SR-3 as open conjectures (each an explicit `sorry`
obligation, like Conjecture 1 for Λ) brings it inside the honesty system: the
endpoint stays MODELED, and the path to promotion is a real Lean proof — nothing
else.

## Promotion path (the only one)

Identical to every other SZL formula: a complete, machine-checked Lean 4 proof
compiling with **0 `sorry`s** landing in `lutar-lean` and reflected in the
`lean-kernel` live verifier. Evolution/self-repair/homeostasis all **propose**;
the Lean kernel **disposes**. No self-modifying process may promote SR-1..SR-3 —
only a proof.

---

## References

- Mechanism: [`killinchu_organism.py`](https://github.com/szl-holdings/killinchu/blob/main/killinchu_organism.py) · Wave-16 organ [`szl_fgbrain.py`](https://github.com/szl-holdings/killinchu/blob/main/szl_fgbrain.py)
- Growing Neural Cellular Automata (Mordvintsev et al., Distill 2020): <https://distill.pub/2020/growing-ca/>
- Fiedler, "Algebraic connectivity of graphs" (1973), Czechoslovak Math. J. — standard source for \(\lambda_2\) connectivity.
- Bounty convention mirrored from [`lutar-lean/BOUNTY.md`](https://github.com/szl-holdings/lutar-lean/blob/main/BOUNTY.md) (Conjecture 1, Λ-uniqueness).
