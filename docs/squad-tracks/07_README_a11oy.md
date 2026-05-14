# a11oy — Prisca-GraphRAG v2 Retriever README additions (Track 7)

## `src/rag/graph/` — Prisca-GraphRAG v2 retrieval pipeline

New files added by Track 7:

### `a11oy/src/rag/graph/prisca-v2-retriever.ts`

Full Prisca-GraphRAG v2 retrieval pipeline for the a11oy governed pipeline.

**Pipeline:**
1. Synthetic query embedding (stub → replace with `text-embedding-3-large`)
2. Optional contextual preamble (Anthropic Contextual Retrieval pattern, phd4_graph.md §1.5)
3. ANN vector seed via `LambdaGraphStore.vectorSeed()`
4. Personalized PageRank traversal via `traverseWithReceipt()` — one leaf per hop
5. Community summary lookup (stub; replace with pre-generated Leiden summaries)
6. Doctrine composite = per-axis min over all hop leaves
7. Assemble `PriscaRetrievalResult` with full receipt chain

**Key types:**

| Type | Description |
|---|---|
| `PriscaV2Config` | Full retriever configuration with documented defaults |
| `PriscaRetrievalResult` | Full retrieval output: nodes, receipts, summaries, Merkle root, Zenodo anchor |

**Lean obligations upheld:**
- `RAGReceipt.lean :: result_in_corpus` — only nodes in graph store returned
- `RAGReceipt.lean :: budget_terminates` — `receipts.length ≤ vectorSeedK × maxHopDepth`
- `GraphHop.lean :: graph_hop_monotone` — visited set grows monotonically

### `a11oy/src/rag/graph/prisca-v2-retriever.replay.ts`

5× variance replay test (seeds `[42, 137, 256, 512, 1024]`):

| # | Test | Assertion |
|---|---|---|
| 1 | Single-hop factual | `UNIT/hekat` node in `traversal_nodes` for "hekat" query |
| 2 | Multi-hop chain | `receipts.length ≥ 4` for truncated-pyramid query |
| 3 | Monotone hop_index | `leaf.hop_index === i` for all i |
| 4 | Receipt hash format | All hashes match `/^[0-9a-f]{64}$/` |
| 5 | Zenodo anchor | `zenodo_anchor` matches `/^10\.\d{4,}\/zenodo\.\d+$/` |
| 6 | REJECT_CYCLE | No duplicate `node_id` in cycle-containing traversal |

Run: `npx ts-node a11oy/src/rag/graph/prisca-v2-retriever.replay.ts`

---

## [UNVERIFIED] items

- `syntheticEmbed()`: replace with `text-embedding-3-large` API call in production
- `generateContextualPreamble()`: replace with Claude Haiku integration
- `buildCommunitySummary()`: replace with persistent community summary store
- `getCommunityContext()`: stub — requires community summary DB at index time
