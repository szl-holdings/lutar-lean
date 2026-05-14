# CHANGELOG — Track 7: Prisca-GraphRAG v2 + lutar-lean obligations

**Date:** 2026-05-13  
**Author:** Stephen P. Lutar Jr. <stephen@szlholdings.com>  
**Doctrine:** v2 binding  

---

## amaru

### Added

- `src/graph/lambda-graph-store.types.ts` — Type definitions for Prisca-GraphRAG v2:
  `LambdaGraphHopLeaf`, `DoctrineGrade`, `GraphNode`, `GraphEdge`, `CommunityPartition`,
  `SentraHopVerdict`, `TraversalReceipt`. Canonical-JSON hash contract documented on every type.

- `src/graph/lambda-graph-store.ts` — Prisca-GraphRAG v2 graph store:
  - Append-only edge log with SHA-256 hash verification (`addEdge`, `verifyLogIntegrity`)
  - `addNode()` — content-addressed upsert
  - `getCommunities()` — C0–C3 Leiden stub (BFS component grouping; full Leiden [UNVERIFIED])
  - `traverseWithReceipt()` — PPR-seeded multi-hop traversal with Sentra guard + Λ_Ω leaf chain
  - `vectorSeed()` — ANN cosine similarity seed (dev brute-force; Neo4j `vector-2.0` in prod)
  - `sentraGuardHop()` — ALLOW / REJECT_CYCLE / REJECT_DEPTH per hop
  - Lean obligations: `GraphHop.lean :: graph_hop_monotone`, `traversal_acyclic`

- `src/graph/lambda-graph-store.replay.ts` — 5× variance replay test:
  seeds `[42, 137, 256, 512, 1024]`, 6 assertions per seed = 30 total.
  Tests: log integrity, determinism, REJECT_CYCLE, REJECT_CYCLE count,
  monotone hop_index, Merkle root re-computation.

---

## a11oy

### Added

- `src/rag/graph/prisca-v2-retriever.ts` — Prisca-GraphRAG v2 full retrieval pipeline:
  - `PriscaV2Config` with documented defaults (vectorSeedK=10, maxHopDepth=3, communityLevel='C1')
  - `PriscaRetrievalResult` with Lean-invariant documentation
  - `PriscaV2Retriever.retrieve()` — contextual preamble → ANN seed → PPR traversal →
    community summaries → doctrine composite → receipt assembly
  - `PriscaV2Retriever.getCommunityContext()` — community summary lookup stub
  - Lean obligations: `RAGReceipt.lean :: result_in_corpus`, `budget_terminates`,
    `GraphHop.lean :: graph_hop_monotone`

- `src/rag/graph/prisca-v2-retriever.replay.ts` — 5× variance replay test:
  seeds `[42, 137, 256, 512, 1024]`, 6 assertions per seed = 30 total.
  Tests: single-hop factual, multi-hop chain, hop_index monotone,
  receipt hash format, Zenodo anchor format, REJECT_CYCLE.

---

## lutar-lean

### Added

- `Lutar/RAGReceipt.lean` — Five Λ-QL v0.1 proof obligations (phd5_protocol.md §5.5):
  1. `result_in_corpus` — every returned chunk ∈ corpus_snapshot (sorry, needs axiom discharge)
  2. `sentra_gate_sound` — ∀ chunk, sentra_scores ≥ τ (sorry, needs Sentra gate formalisation)
  3. `doctrine_grade_monotone` — ∀ chunk, doctrine_grades ≥ min_grade (sorry)
  4. `merkle_root_binds_chunks` — merkle_root = hash_fn(chunk_hashes) (sorry, needs SHA-256 formalisation)
  5. `budget_terminates` — ∃ n ≤ max_chunks, n = chunk_hashes.card (**FULLY DISCHARGED**)
  
  Auxiliary axioms: `chunk_membership_from_receipt`, `sentra_gate_from_attestation`,
  `doctrine_filter_from_receipt`, `merkle_construction_correct` — each with TODO discharge comments.

- `Lutar/GraphHop.lean` — Prisca-GraphRAG v2 hop monotonicity (phd4_graph.md §5.3):
  1. `graph_hop_monotone` — visited ⊆ visited ∪ hop_result.toFinset (**FULLY DISCHARGED**)
  2. `traversal_acyclic` — List.Nodup → path injective (sorry, pending Mathlib version pin)
  3. `hop_index_monotone` — List.range n is valid hop chain (**FULLY DISCHARGED**)
  4. `hop_chain_strictly_increasing` — adjacent hop indices strictly increasing (**FULLY DISCHARGED**)
  5. `ppr_convergence_bounded` — PPR terminates in ≤ maxIter steps (trivial stub discharged;
     full convergence proof pending Mathlib spectral theory — phd4_graph.md §6)

- `Lutar/lakefile.lean` (snippet) — adds `.one \`Lutar.RAGReceipt` and `.one \`Lutar.GraphHop``
  to the existing `lean_lib Lutar` target. Instructions for Integrator included inline.

---

## [UNVERIFIED] open items propagated to Verifier

1. `vectorSeed()` Neo4j `vector-2.0` integration — stub only in this track
2. `getCommunities()` full Leiden algorithm — stub (BFS components) only
3. `syntheticEmbed()` → `text-embedding-3-large` API call needed in production
4. `generateContextualPreamble()` → Claude Haiku API call needed
5. Lean `traversal_acyclic` sorry → pending Mathlib4 exact lemma (`List.Nodup.get_inj_iff`)
6. Lean `ppr_convergence_bounded` full convergence proof → open question (phd4_graph.md §6)
7. Lean axioms (theorems 1–4) → full mechanisation requires receipt builder formal spec
