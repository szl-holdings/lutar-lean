# FRONTIER Tier — Experimental · CI-green Theorem Library

> **Doctrine v11 LOCKED** · Locked-proven = **exactly 8** {F1,F4,F7,F11,F12,F18,F19,F22} · Λ = **Conjecture 1** (OPEN, machine-checked FALSE unconditionally) · NEVER inflate these counts.

This document is the honest index of the **FRONTIER / EXPERIMENTAL · CI-green** tier of `lutar-lean`. These are **real, machine-kernel-verified theorems** — they compile on `main` under `lake build`, produce `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`, and carry zero `sorry` — but they are **explicitly excluded** from the locked-8 count and never asserted as proven in the doctrine sense.

## How to read this document

| Label | Meaning |
|---|---|
| **LOCKED** | One of the 8 zero-sorry, kernel-only proven formulas at `c7c0ba17` — immutable |
| **EXPERIMENTAL · CI-green** | Machine-kernel-verified on `main`; real math; NOT in the locked set; may be conditional |
| **CONJECTURE** | Statement-only; proof-deferred or machine-checked false as stated |

**NEVER** call any EXPERIMENTAL result "proven" without qualification. Always cite the wave, the conditional hypotheses, and this document when referencing frontier results.

---

## Wave 11 — Graph, Cache, Early-Exit, Immune Bayes (CI-green)

Files: `Lutar/Wave11/`

| Ref | Name | Statement | Status |
|-----|------|-----------|--------|
| CF-1 | `GraphAutoDistInvariant` | Graph-automorphism distance invariance: automorphism-equivariant distance function is invariant under the automorphism group | **EXPERIMENTAL · CI-green** |
| CF-2 | `OuroKVCacheSlots` | Ouroboros KV-cache slot count is bounded by the loop depth | **EXPERIMENTAL · CI-green** |
| CF-3 | `OuroLoopEarlyExit` | Early-exit soundness: early-terminated loop agrees with completed loop on evaluated output | **EXPERIMENTAL · CI-green** |
| CF-5 | `ImmuneNeymanPearsonOpt` | Discrete Neyman–Pearson optimality for the immune-inspection gate (measurable-space hypothesis) | **EXPERIMENTAL · CI-green · conditional** |

Disclosed axiom sets: `wave11_axiom_sets_kernel_only` (machine-checked `decide` in `Lutar/Wave11/AxiomDisclosure.lean`). The Wave11 names are disjoint from the locked-8 (`wave11_excluded_from_locked`).

---

## Wave 12 — Λ Conditional Uniqueness, DEQ, Floating-Point (CI-green)

Files: `Lutar/Round13/Lambda_Uniqueness.lean`, inline Wave12 results

| Ref | Name | Statement | Status |
|-----|------|-----------|--------|
| CUT-2 | `lambda_unique_of_separable` | Axiom-free conditional Λ uniqueness: any A1–A5 aggregator with multiplicative, separable per-axis slices equals Λ | **EXPERIMENTAL · CI-green · axiom-free conditional** |
| CF-13 | DEQ input-Lipschitz well-posedness | Input-Lipschitz parameter implies well-posed DEQ solution | **EXPERIMENTAL · CI-green · conditional** |
| CF-17 | Floating-point summation error bound | Rounding error in sequential fp summation is O(n·ε) | **EXPERIMENTAL · CI-green** |

---

## Wave 13 — Replay, Quorum Shadow, HM Bottleneck (CI-green)

Files: `Lutar/Wave13/Sweep.lean`

| Ref | Name | Statement | Status |
|-----|------|-----------|--------|
| — | Replay-root completeness | Every receipt in the receipt store appears in the replay root | **EXPERIMENTAL · CI-green** |
| — | Non-Byzantine quorum shadow | Single-valued vote function yields quorum agreement (honest-only shadow; Byzantine liveness is Conjecture 2) | **EXPERIMENTAL · CI-green · honest shadow** |
| — | Hardy–Littlewood–Pólya HM bottleneck | HM inequality applied to the mesh throughput bottleneck | **EXPERIMENTAL · CI-green** |

---

## Wave 14 — Leibniz/Mādhava, Reed–Solomon, VCG, Cover–Thomas (CI-green)

Files: `Lutar/Wave14/`

| Ref | Name | Statement | Status |
|-----|------|-----------|--------|
| CF-18 | `LeibnizRemainder` | Leibniz/Mādhava alternating-series remainder bound | **EXPERIMENTAL · CI-green** |
| CF-19 | `ReedSolomonDistance` | Reed–Solomon MDS minimum distance theorem | **EXPERIMENTAL · CI-green** |
| CF-20 | `VCGEfficiency` | VCG mechanism efficiency + truthfulness core | **EXPERIMENTAL · CI-green** |
| CF-21 | `LogSumInequality` | Cover–Thomas log-sum inequality + Gibbs | **EXPERIMENTAL · CI-green** |

---

## Wave 15 — KL Divergence, DPO Repair, Bisymmetry Bridge (CI-green)

Files: `Lutar/Wave15/`

| Ref | Name | Statement | Status |
|-----|------|-----------|--------|
| CF-22 | `KLDivergenceSimplex` | `dpo_klDivergence_nonneg_on_simplex`: KL ≥ 0 on the simplex — conditionally repairs the false-as-stated DPO axiom | **EXPERIMENTAL · CI-green · conditional** |
| CF-24 | `BisymmetryCut1` | Axiom-free bisymmetry→CUT-2 bridge | **EXPERIMENTAL · CI-green · axiom-free** |
| — | `PinskerRoadmap` | Roadmap/scaffold for full Pinsker bound (Wave15 milestone) | **EXPERIMENTAL · CI-green** |

---

## Wave 16 — Binary-KL Convexity, Aczél Axioms, Scale-Invariance, Abacus (CI-green)

Files: `Lutar/Wave16/`

| Ref | Name | Statement | Status |
|-----|------|-----------|--------|
| CF-23 | `PinskerConvexity` | Binary-KL convexity crux | **EXPERIMENTAL · CI-green** |
| CF-24 | `Cut1MeanAxioms` | `geoBin` satisfies the full Aczél quasi-arithmetic axioms (idempotent/symmetric/homogeneous/monotone — the last analytic step before CUT-1) | **EXPERIMENTAL · CI-green** |
| CF-25 | `LambdaScaleInvariance` | Λ scale-invariance | **EXPERIMENTAL · CI-green** |
| CF-26 | `AbacusPlaceValue` | Abacus place-value arithmetic formalized | **EXPERIMENTAL · CI-green** |

---

## Wave 17 — Full Binary + Multiclass Pinsker, Monotone DEQ, Recurrent Depth (CI-green)

Files: `Lutar/Wave17/`

| Ref | Name | Statement | Status |
|-----|------|-----------|--------|
| CF-23 | `BinaryPinsker` | Full binary Pinsker: `2(p−q)² ≤ KL(p‖q)` — axiom-free | **EXPERIMENTAL · CI-green** |
| CF-23-FULL | `MultiClassPinsker` | k-bin Pinsker via binary data-processing reduction; axiom-free, conditional on non-degenerate partition | **EXPERIMENTAL · CI-green · conditional** |
| CF-27 | `MonDEQWellPosed` | Monotone-DEQ unique equilibrium | **EXPERIMENTAL · CI-green** |
| CF-28 | `RecurrentDepth` | Recurrent-depth `Kʳ`-Lipschitz bound | **EXPERIMENTAL · CI-green** |

---

## Waves 18–24 — CUT-1 Chain, Density, Quorum Safety Roadmap (CI-green)

Files: `Lutar/Wave18/` – `Lutar/Wave24/`

These waves complete the Aczél representation (Wave18), develop density results (Waves19–22), and approach the CUT-1 / Conjecture-1 boundary (Waves21–22). Wave23 contains `QuorumSafety.lean` (the honest honest-only liveness precursor to Conjecture 2). Wave24 contains `AdmissibilityCertificate.lean`.

> **Important:** None of Waves18–24 close Conjecture 1. Unconditional Λ uniqueness under bare A1–A5 remains machine-checked **FALSE** (`maxAgg_ne_Lambda`). These waves advance toward CUT-1 but the open prize remains at [`lambda-bounty`](https://github.com/szl-holdings/lambda-bounty).

| Wave | Headline files | Status |
|------|----------------|--------|
| 18 | `AczelRepresentation.lean`, `Cut1Chain.lean` | **EXPERIMENTAL · CI-green** |
| 19 | `AccumulationUncountable.lean`, `Cut1Density.lean`, `Density.lean`, `DisjointOpens.lean`, `DyadicImageDense.lean` | **EXPERIMENTAL · CI-green** |
| 20 | `Accumulation.lean`, `DisjointOpens.lean` | **EXPERIMENTAL · CI-green** |
| 21 | `Cut1Final.lean`, `DyadicImageDense.lean`, `Uncountable.lean` | **EXPERIMENTAL · CI-green** |
| 22 | `CorderClosure.lean`, `Cut1Corder.lean`, `GapShiftOrdering.lean`, `LambdaConditional.lean` | **EXPERIMENTAL · CI-green** |
| 23 | `QuorumSafety.lean` — honest non-Byzantine quorum precursor to Conjecture 2 | **EXPERIMENTAL · CI-green · honest shadow** |
| 24 | `AdmissibilityCertificate.lean` | **EXPERIMENTAL · CI-green** |

---

## Showcase / Frontier (outside `Lutar/` — not counted by `lean_numbers.py`)

Files: `Showcase/Frontier/`

These live outside the counted `Lutar/` namespace. They do not affect `749/14/163`. Each is labeled EXPERIMENTAL in its own README.

| File | Subject | Status |
|------|---------|--------|
| `CelestialIRTriangle.lean` | Pasterski–Strominger–Zhiboedov infrared triangle (discrete witness) | **EXPERIMENTAL · not counted** |
| `TopoInfoWitness.lean` | Topological information witness | **EXPERIMENTAL · not counted** |
| `QuantumInfoWitness.lean` | Quantum-information witness | **EXPERIMENTAL · not counted** |
| `RelationalMeshWitness.lean` | Relational-mesh governance witness | **EXPERIMENTAL · not counted** |
| `LandauerFloorWitness.lean` | Landauer floor energy bound (discrete) | **EXPERIMENTAL · not counted** |
| `EnergyBudgetWitness.lean` | Energy-budget audit witness | **EXPERIMENTAL · not counted** |
| `HarvestBudgetWitness.lean` | Harvest-budget bound | **EXPERIMENTAL · not counted** |
| `AgenticBodyWitness.lean` | Agentic-body pipeline witness | **EXPERIMENTAL · not counted** |

---

## Live-checkable demo path

Any result labeled **EXPERIMENTAL · CI-green** above can be live-checked against the Lean kernel:

```bash
# 1. Clone and build
git clone https://github.com/szl-holdings/lutar-lean
cd lutar-lean
lake exe cache get      # restore Mathlib olean cache
lake build              # full library — CI-green on main

# 2. Inspect axiom footprint of any frontier result
# Example: Wave17 binary Pinsker
lake env lean -e "#check Lutar.Wave17.BinaryPinsker" 2>&1
lake env lean -e "#print axioms Lutar.Wave17.BinaryPinsker.binary_pinsker" 2>&1
# → [propext, Classical.choice, Quot.sound]   ← kernel-only, no sorry

# 3. Verify the locked count hasn't moved
lake env lean -e "#eval Lutar.Wave8.AxiomDisclosure.locked_count_eight" 2>&1
# → 8   ← immutable

# 4. Live kernel browser (HF Space, no install)
# https://huggingface.co/spaces/SZLHOLDINGS/lean-kernel
#   /api/lean/check?decl=Lutar.Wave17.BinaryPinsker.binary_pinsker
```

The HF Space [`SZLHOLDINGS/lean-kernel`](https://huggingface.co/spaces/SZLHOLDINGS/lean-kernel) serves `#check` and `#print axioms` queries over HTTP. Any result in this document is live-checkable there without a local Lean install.

---

## What is NOT here

- **Conjecture 1 (`Conjecture1_LambdaUnique`)** — unconditional Λ uniqueness — is machine-checked **FALSE** as stated. It is not in this document. Open prize: [`lambda-bounty`](https://github.com/szl-holdings/lambda-bounty).
- **Conjecture 2 (`khipu_consensus_safety`)** and **Conjecture 3 (`khipu_consensus_liveness`)** — BFT safety/liveness — are proof-deferred. See [`khipu-consensus`](https://github.com/szl-holdings/khipu-consensus).
- **Putnam sorries** — 51 honest `sorry` obligations in `Showcase/PutnamLean/`; scope disclosed in `SORRIES.md`.

---

*Doctrine v11 LOCKED · 749/14/163 · c7c0ba17 · locked-proven = 8 · Λ = Conjecture 1*

Signed-off-by: Stephen Lutar <stephenlutar2@gmail.com>
