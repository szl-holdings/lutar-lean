# amaru — Graph Store README additions (Track 7)

## `src/graph/` — Prisca-GraphRAG v2 graph layer

New files added by Track 7 (Prisca-GraphRAG v2 + lutar-lean obligations):

### `amaru/src/graph/lambda-graph-store.types.ts`

Type definitions for the Prisca-GraphRAG v2 graph layer:

| Type | Description |
|---|---|
| `DoctrineGrade` | 9-axis doctrine v2 evaluation result (each axis 0–10) |
| `LambdaGraphHopLeaf` | Λ_Ω Merkle leaf for one graph traversal hop |
| `GraphNode` | Node in the knowledge graph (hash-addressed, embedding-indexed) |
| `GraphEdge` | Directed, weighted, hash-verified edge in the append-only log |
| `CommunityPartition` | Leiden community detection result (Zenodo-anchorable) |
| `SentraHopVerdict` | `ALLOW` \| `REJECT_CYCLE` \| `REJECT_DEPTH` |
| `TraversalReceipt` | Aggregated receipt from a full multi-hop traversal |

### `amaru/src/graph/lambda-graph-store.ts`

Prisca-GraphRAG v2 graph store. Features:

- **Append-only edge log** with SHA-256 hash-verified edges (`addEdge()`, `verifyLogIntegrity()`)
- **Node store** with content-addressed node hashes (`addNode()`, `getNodeByHash()`)
- **ANN vector seed** — brute-force cosine similarity (dev); swap for Neo4j `vector-2.0` in prod (`vectorSeed()`)
- **Leiden community detection stub** — BFS connected-component grouping at C0–C3 levels (`getCommunities()`)
- **PPR-seeded traversal with receipt** — Personalized PageRank + Sentra-guarded BFS, emits `LambdaGraphHopLeaf` per hop (`traverseWithReceipt()`)
- **Sentra guard** — `sentraGuardHop()` → `REJECT_CYCLE` | `REJECT_DEPTH` | `ALLOW`

Lean obligations: `GraphHop.lean :: graph_hop_monotone`, `traversal_acyclic`

### `amaru/src/graph/lambda-graph-store.replay.ts`

5× variance replay test (seeds `[42, 137, 256, 512, 1024]`):

| # | Test | Assertion |
|---|---|---|
| 1 | Log integrity | `verifyLogIntegrity() === true` |
| 2 | Determinism | `chain_merkle_root` identical across two runs |
| 3 | REJECT_CYCLE | No duplicate `node_id` in cycle-containing traversal |
| 4 | REJECT_CYCLE count | `rejected_hop_count > 0` for cycle-injected graph |
| 5 | Monotone hop_index | `leaf.hop_index === i` for all i |
| 6 | Merkle root | Re-computed root matches stored `chain_merkle_root` |

Run: `npx ts-node amaru/src/graph/lambda-graph-store.replay.ts`

---

## [UNVERIFIED] items

- `vectorSeed()`: production Neo4j `vector-2.0` integration is pending
- `getCommunities()`: full Leiden algorithm pending (stub = BFS component grouping)
- PPR convergence: `ppr_convergence_bounded` Lean theorem is a stub (phd4_graph.md §6)
