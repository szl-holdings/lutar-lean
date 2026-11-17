<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SZL Holdings — Frontier Census v2 · Sign: Vibe/dc CTO lane -->

# Frontier Census v2 — the sorry map of the estate (2026-11-16)

_Generated from GitHub code search (query: `sorry repo:szl-holdings/lutar-lean language:lean`, 50 file hits) + the repo's own SORRIES.md / STATUS.md scoreboard. UNVERIFIED drafts; input layer for the runtime proving lane. Not part of `lake build`._

## The scoreboard (canonical, from SORRIES.md @ 54b8d304)

- Compiled-corpus open `sorry`: **61** (pinned no-increase baseline 61; target 0)
- Tracked sorries total: **163** (112 baseline + 51 Putnam) — doctrine v11 @ c7c0ba17
- proposals/ scratch mirror (UNVERIFIED, not in lake build): 5 disclosed
- Λ = Conjecture 1 (OPEN; machine-checked false under A1-A5 — see maxAgg_ne_Lambda)
- Locked-proven formulas: exactly 8 {F1,F4,F7,F11,F12,F18,F19,F22} @ c7c0ba17

## Census: 50 sorry-carrying files (GitHub code search, grouped)

### Putnam showcase (competition frontier — 51 tracked Putnam sorries)
Showcase/PutnamLean/P01.lean
Showcase/PutnamLean/P02.lean
Showcase/PutnamLean/P03.lean
Showcase/PutnamLean/P04.lean

### Innovations rounds (estate-native frontier math)
Lutar/Innovations/round3/TopoDrift.lean
Lutar/Innovations/round5/CodonRoundTrip.lean
Lutar/Innovations/round5/HermesMoranIFS.lean
Lutar/Innovations/round5/CodonK4Compress.lean
Lutar/Innovations/round9/BrainBeliefUpdate.lean
Lutar/Innovations/round3/KhipuEmitMonotone.lean
Lutar/Innovations/round9/SkeletonLambdaSpine.lean
Lutar/Innovations/round5/TetractysHMBottleneck.lean
Lutar/Innovations/round7/GeneticKroneckerCompression.lean
Lutar/Innovations/round9/HeartReceiptSigma.lean
Lutar/Innovations/round9/NervousShannonAlarm.lean
Lutar/Innovations/round9/ImmuneNeymanPearson.lean
Lutar/Innovations/round9/WiresReidemeisterKnot.lean

### Waves (governance/substrate theorems)
Lutar/Wave11/AxiomDisclosure.lean
Lutar/Wave9/BasilicBDB.lean
Lutar/Wave10/DSSEToken.lean
Lutar/Wave9/AxiomDisclosure.lean
Lutar/Wave9/Merkle.lean
Lutar/Wave3/Consensus.lean
Lutar/Wave10/AxiomDisclosure.lean
Lutar/Wave8/AxiomDisclosure.lean
Lutar/Wave9/RobustDeclass.lean
Lutar/Wave10/ReplayDeterminism.lean
Lutar/Wave10/QuorumIntersection.lean
Lutar/Wave10/ReachabilityRedundancy.lean
Lutar/Wave10/STLRobustness.lean
Lutar/Wave10/NonInterferenceComposition.lean
Lutar/Wave6/InfoSubstrate.lean
Lutar/Wave6/GraphSubstrate.lean
Lutar/Wave5/DiscreteSubstrate.lean
Lutar/Wave7/DiscreteSubstrate.lean

### Puriq formulas (the formula library)
Lutar/Puriq/Formulas/ProvedFormulas.lean
Lutar/Puriq/Formulas/PuriqFormulaLean.lean

### Showcase Frontier witnesses
Showcase/Frontier/TopoInfoWitness.lean
Showcase/Frontier/HarvestBudgetWitness.lean
Showcase/Frontier/LandauerFloorWitness.lean
Showcase/Frontier/EnergyBudgetWitness.lean
Showcase/Frontier/QuantumInfoWitness.lean
Showcase/Frontier/AgenticBodyWitness.lean
Showcase/Frontier/RelationalMeshWitness.lean
Showcase/Frontier/CelestialIRTriangle.lean
Showcase/Frontier/CredoVerdictWitness.lean

### Other corpus files
Lutar/Transduction/ReceiptInvariant.lean
Lutar/Frontier/Killinchu.lean
Lutar/Covenant/DenyMonotonic.lean
Lutar/Agentic/Pipeline.lean

## Battery v2 spec (for the runtime proving lane)

Hard lessons from Round 1 (2026-11-16, laptop frontier_loop): a `first | ... | sorry`
fallback compiles GREEN (sorry is a warning), so build-green is NOT discharge evidence;
and per-decl axiom checks require the module oleans to exist — run FULL `lake build`
before any round (only 182 oleans were on disk vs a claimed-green 9,236-target baseline).

1. **Prerequisite:** full `lake build` green, olen count sanity-checked against module count.
2. **Per-tactic probe ladder (attribution, not first-fallback):** probe each tactic
   INDIVIDUALLY per target — rfl, omega, linarith, nlinarith, ring_nf, polyrith,
   field_simp, norm_num, simp_all, decide, aesop, gcongr, posit, exact?, apply? —
   recording WHICH tactic discharged (tactic-solvability map of the estate).
   `native_decide` is EXCLUDED (trust escape, same as the bounty CI).
3. **Escalating rounds:** round r adds combo batteries (rfl|omega|linarith|ring_nf|simp_all …)
   only for targets no single tactic closed.
4. **Discharge gate (axcheck-success, hard):** `#print axioms <decl>` must parse with
   NO `error`, NO `sorryAx`, and only allowlisted axioms (propext, Quot.sound,
   Classical.choice). Any error = FAIL + revert, never a discharge.
5. **Receipts:** per-attempt receipts with tactic attribution; sorry scoreboard delta
   must ratchet down only; CI sorry-gate (61 pin) stays authoritative.
