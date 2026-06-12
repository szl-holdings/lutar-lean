# Frontier showcase — The Relational Mesh · **EXPERIMENTAL** · original SZL

Kernel-checked, Mathlib-free formalization of the **SZL UDS organ mesh as a
relational graph**. Compiles on `leanprover/lean4:v4.18.0` core; zero `sorry`,
no `native_decide`. Source: [`RelationalMeshWitness.lean`](RelationalMeshWitness.lean).

## Provenance — inspired by, not copied from

You, Leskovec, He & Xie, *Graph Structure of Neural Networks*, ICML 2020
([arXiv:2007.06559](https://arxiv.org/abs/2007.06559)). They model a neural net
as a **relational graph** — nodes hold features, one layer = one **round of
message exchange** `x_v^{(r+1)} = AGG({ f(x_u) : u ∈ N(v) })` — and show
empirically that test accuracy is a smooth function of two graph statistics,
**clustering coefficient C** and **average path length L**, with a "sweet spot"
near `C ∈ [0.43, 0.50], L ∈ [1.82, 2.28]` (resembling the macaque cortex).

We adopt their **mathematical lens** and make it our own: the SZL UDS mesh is a
relational graph where **organs are nodes** and **signed cross-organ spans**
(`sentra.gate.*`, `amaru.sync.*`, `rosie.decision.*`, `killinchu.courier.*`,
`a11oy.graph.*`) are the edges a round of message exchange runs along.

## What is proven (all kernel-checked)

| Theorem | Statement | `#print axioms` |
|---|---|---|
| `no_isolated_organ` | every organ has ≥ 2 neighbors (resilience floor) | none |
| `a11oy_is_hub` | a11oy has degree 4 (orchestration hub) | none |
| `diameter_le_two` | every organ pair is within 2 hops → `L` ceiling = 2 (fast corroboration) | none |
| `positive_clustering` | ≥ 4 triangles (ring edges close through the hub) → `C` > 0 | none |
| `round_deterministic` | a round of message exchange is a pure function of (graph, state) — replayable | [propext, Quot.sound] |
| `unit_round_*_eq_degree` | concrete round: from the unit state, each organ → its degree | none |

The mesh topology: a11oy as a hub connected to all four other organs, plus a
corroboration ring sentra–amaru–rosie–killinchu. Short paths (diameter 2) +
positive clustering = the local-redundancy / fast-global-reach structure the
relational-graph lens cares about.

## What we explicitly DO NOT claim (honesty doctrine v11)

- **No transfer of the You-et-al. accuracy result.** Whether their topology
  "sweet spot" improves SZL trust/governance resilience is an **OPEN engineering
  hypothesis** ("topology shapes mesh resilience") — NOT a theorem, NOT proven,
  NOT one of the locked-8.
- These are discrete *structural* witnesses of OUR mesh wiring, not a claim about
  message semantics, BFT safety (= Conjecture 2), or Λ (= Conjecture 1).
- Lives outside `Lutar/` → NOT counted by `lean_numbers.py`; locked-proven set
  stays **EXACTLY 8** {F1,F4,F7,F11,F12,F18,F19,F22}.
- `round_deterministic` is an honest discrete witness of replay-determinism; it
  is **not** the locked F22 (replay determinism) theorem itself.
