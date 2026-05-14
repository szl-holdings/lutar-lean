/**
 * lambda-graph-store.types.ts
 * Prisca-GraphRAG v2 — Λ_Ω graph hop type definitions
 *
 * Repo:    amaru/src/graph/lambda-graph-store.types.ts
 * Author:  Stephen P. Lutar Jr. <stephen@szlholdings.com>
 * Doctrine: v2 binding — no hallucinations, test×5, one-of-one
 *
 * References:
 *   - phd4_graph.md §3 Λ-receipt schema for graph hops
 *   - 99_synthesis_a11oy_rag.md §2.1 architecture
 *   - Prisca-GraphRAG v5 DOI: 10.5281/zenodo.20020846 (extend)
 */

// ─── DoctrineGrade ────────────────────────────────────────────────────────────

/**
 * 9-axis doctrine v2 evaluation result per Lean obligation.
 * Every axis is on the [0, 10] scale.
 * Minimum passing threshold: ≥ 9.0 on every axis (doctrine rule).
 */
export interface DoctrineGrade {
  /** Numeric claims are verifiable and uncertainty is acknowledged */
  measurabilityHonesty: number;   // [0, 10]
  /** Code is minimal, canonical-JSON-serialised, no orphaned fields */
  cleanliness: number;            // [0, 10]
  /** ouroboros halt guarantee — every loop terminates within max_hop_depth */
  boundedness: number;            // [0, 10]
  /** every hop node and edge carry full SHA-256 chain */
  traceability: number;           // [0, 10]
  /** assertions are testable and rejectable */
  falsifiability: number;         // [0, 10]
  /** Gauss class-number witness diversity check */
  diversityWitness: number;       // [0, 10]
  /** Bekenstein-bound: context size does not exceed information limit */
  bekensteinBound: number;        // [0, 10]
  /** reference-vector parity — embedding stays deterministic across runs */
  parity: number;                 // [0, 10]
  /** MATCH/DIVERGE verdict from dual-witness evaluation */
  dualWitness: number;            // [0, 10]
}

/**
 * Convenience factory — default passing grade (all axes 9.0).
 * Replace individual axes with measured values at runtime.
 */
export function defaultDoctrineGrade(): DoctrineGrade {
  return {
    measurabilityHonesty: 9.0,
    cleanliness: 9.0,
    boundedness: 9.0,
    traceability: 9.0,
    falsifiability: 9.0,
    diversityWitness: 9.0,
    bekensteinBound: 9.0,
    parity: 9.0,
    dualWitness: 9.0,
  };
}

// ─── LambdaGraphHopLeaf ───────────────────────────────────────────────────────

/**
 * LambdaGraphHopLeaf — Λ_Ω Merkle leaf for a single graph traversal hop.
 *
 * Emitted once per (source_node → edge → target_node) triple.
 * Binds each hop cryptographically; forms the receipt chain for
 * PriscaV2Retriever traversals.
 *
 * Hash computation contract (SHA-256):
 *   source_node_hash  = SHA-256(node_label || canonical_JSON(node_properties))
 *   target_node_hash  = SHA-256(node_label || canonical_JSON(node_properties))
 *   edge_hash         = SHA-256(source_node_hash || edge_type || target_node_hash || edge_weight.toFixed(6))
 *
 * Lean obligation: GraphHop.lean :: graph_hop_monotone
 *   visited ⊆ visited ∪ {target_node_hash}   -- monotone accumulation
 */
export interface LambdaGraphHopLeaf {
  /** Zero-based ordinal position in the traversal chain (0 = seed hop) */
  hop_index: number;

  /** SHA-256(node_label || canonical_JSON(properties)) of source node */
  source_node_hash: string;

  /**
   * SHA-256(source_node_hash || edge_type || target_node_hash || edge_weight)
   * Binds relationship semantics and direction immutably.
   */
  edge_hash: string;

  /** SHA-256(node_label || canonical_JSON(properties)) of target node */
  target_node_hash: string;

  /**
   * Zenodo DOI slug of the community detection partition in which this
   * edge participates, e.g. "10.5281/zenodo.20020846".
   * Empty string "" if the hop precedes community detection.
   */
  community_id: string;

  /**
   * Retrieval relevance score ∈ [0.0, 1.0].
   * Derived from PPR rank or cosine similarity at seed, then propagated.
   */
  score: number;

  /** Edge type label, e.g. "RELATED_TO", "DERIVED_FROM", "USES" */
  edge_type: string;

  /** Unix timestamp (ms) when this hop was recorded */
  recorded_at: number;

  /** 9-axis doctrine v2 evaluation at time of hop */
  doctrine_grade: DoctrineGrade;
}

// ─── GraphNode ────────────────────────────────────────────────────────────────

/**
 * GraphNode — a node in the Prisca-GraphRAG v2 knowledge graph.
 * Stored in the amaru append-only edge log and Neo4j ANN index.
 */
export interface GraphNode {
  /** Stable unique identifier within the graph */
  node_id: string;

  /** Categorical label, e.g. "PROBLEM", "OPERATION", "UNIT", "ENTITY" */
  label: string;

  /** Arbitrary JSON properties — canonical-JSON-serialised for hashing */
  properties: Record<string, unknown>;

  /**
   * SHA-256(label || canonical_JSON(properties))
   * Computed at ingest; immutable thereafter.
   */
  node_hash: string;

  /**
   * text-embedding-3-large, dim=1536.
   * Used by Neo4j vector-2.0 ANN index (cosine, HNSW m=16).
   */
  embedding_vector: number[];
}

// ─── GraphEdge ────────────────────────────────────────────────────────────────

/**
 * GraphEdge — a directed, weighted, hash-verified edge in the append-only log.
 * Never mutated after insertion. Append-only log enforced at storage layer.
 */
export interface GraphEdge {
  /** node_hash of source node */
  source_node_hash: string;

  /** Relationship label, e.g. "RELATED_TO", "USES", "DERIVED_FROM" */
  edge_type: string;

  /** node_hash of target node */
  target_node_hash: string;

  /**
   * Numeric edge weight ∈ [0, ∞).
   * For entity extraction, weight = co-occurrence count (GraphRAG convention).
   */
  weight: number;

  /**
   * Zenodo DOI slug of the community detection result for this edge.
   * e.g. "10.5281/zenodo.20020846"
   */
  community_id: string;

  /** Unix timestamp (ms) of insertion — append-only log monotone order */
  inserted_at: number;

  /**
   * SHA-256(source_node_hash || edge_type || target_node_hash || weight.toFixed(6))
   * Computed at ingest; guards log integrity.
   */
  edge_hash: string;
}

// ─── CommunityPartition ───────────────────────────────────────────────────────

/**
 * Leiden community detection result at a given hierarchy level.
 * Serialised as canonical JSON and SHA-256-hashed before Zenodo deposit.
 * DOI is stored as community_id in edges and hop leaves.
 */
export interface CommunityPartition {
  /** C0 (root) | C1 | C2 | C3 (leaf) */
  level: 'C0' | 'C1' | 'C2' | 'C3';
  /** Maps community label → array of node_ids */
  communities: Record<string, string[]>;
  /** Leiden modularity score for this partition */
  modularity_score: number;
  /** ISO 8601 UTC timestamp of detection run */
  detected_at: string;
  /**
   * SHA-256(canonical_JSON(this partition object)).
   * Pre-computed before Zenodo deposit; used for integrity verification.
   */
  partition_hash: string;
  /** Zenodo DOI assigned to this partition after deposit */
  zenodo_doi?: string;
}

// ─── Sentra hop verdict ───────────────────────────────────────────────────────

/** Sentra guard verdicts for each hop attempt */
export type SentraHopVerdict =
  | 'ALLOW'
  | 'REJECT_CYCLE'    // targetId already in visitedSet — cycle prevention
  | 'REJECT_DEPTH';   // currentDepth >= maxDepth — ouroboros bounded-loop halt

// ─── TraversalReceipt ─────────────────────────────────────────────────────────

/**
 * Aggregated receipt for a full multi-hop traversal.
 * Returned by LambdaGraphStore.traverseWithReceipt().
 */
export interface TraversalReceipt {
  /** Ordered leaf chain, one per hop (hop_index 0 … n-1) */
  leaves: LambdaGraphHopLeaf[];
  /** Final set of nodes reached (deduplicated, cycle-free) */
  nodes: GraphNode[];
  /** Number of hops rejected by Sentra (REJECT_CYCLE + REJECT_DEPTH) */
  rejected_hop_count: number;
  /**
   * Merkle root over all leaf edge_hashes in chain order.
   * SHA-256(leaf[0].edge_hash || leaf[1].edge_hash || … || leaf[n-1].edge_hash)
   */
  chain_merkle_root: string;
  /** Unix ms when traversal started */
  started_at: number;
  /** Unix ms when traversal completed */
  completed_at: number;
}
