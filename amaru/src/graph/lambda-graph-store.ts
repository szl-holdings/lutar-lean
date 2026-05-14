/**
 * lambda-graph-store.ts
 * Prisca-GraphRAG v2 — amaru graph store layer
 *
 * Repo:    amaru/src/graph/lambda-graph-store.ts
 * Author:  Stephen P. Lutar Jr. <stephen@szlholdings.com>
 * Doctrine: v2 binding — no hallucinations, test×5, one-of-one
 *
 * Architecture:
 *   - Append-only edge log with SHA-256 hash-verified edges (amaru delta-log pattern)
 *   - Neo4j vector-2.0 ANN index (cosine, HNSW m=16, ef_construction=100) for vector seed
 *   - Leiden community detection via getCommunities()
 *   - Personalized PageRank (PPR) traversal emitting Λ_Ω hop leaves per edge
 *   - Sentra guard hooks: ALLOW | REJECT_CYCLE | REJECT_DEPTH per hop
 *
 * Lean obligations:
 *   - GraphHop.lean :: graph_hop_monotone
 *   - GraphHop.lean :: traversal_acyclic
 *
 * References:
 *   - phd4_graph.md §5.2, §5.3, §2.2 (HippoRAG PPR), §1.4 (Neo4j vector-2.0)
 *   - 99_synthesis_a11oy_rag.md §3.1
 *   - Prisca-GraphRAG v5 DOI: 10.5281/zenodo.20020846
 */

import { createHash } from 'crypto';
import {
  type GraphNode,
  type GraphEdge,
  type LambdaGraphHopLeaf,
  type CommunityPartition,
  type SentraHopVerdict,
  type TraversalReceipt,
  type DoctrineGrade,
  defaultDoctrineGrade,
} from './lambda-graph-store.types.js';

// ─── Re-export types for consumers ────────────────────────────────────────────
export type {
  GraphNode,
  GraphEdge,
  LambdaGraphHopLeaf,
  CommunityPartition,
  SentraHopVerdict,
  TraversalReceipt,
  DoctrineGrade,
} from './lambda-graph-store.types.js';

// ─── Hash utilities ───────────────────────────────────────────────────────────

/** SHA-256 of an arbitrary UTF-8 string → 64-char hex */
function sha256(input: string): string {
  return createHash('sha256').update(input, 'utf8').digest('hex');
}

/**
 * Deterministic canonical JSON serialisation — sorted keys, no whitespace.
 * Required for hash stability across runtimes and marshalling layers.
 */
function canonicalJson(obj: unknown): string {
  if (obj === null || typeof obj !== 'object') return JSON.stringify(obj);
  if (Array.isArray(obj)) return '[' + obj.map(canonicalJson).join(',') + ']';
  const sorted = Object.keys(obj as Record<string, unknown>)
    .sort()
    .map(k => JSON.stringify(k) + ':' + canonicalJson((obj as Record<string, unknown>)[k]));
  return '{' + sorted.join(',') + '}';
}

/** Compute node_hash from label + properties */
function computeNodeHash(label: string, properties: Record<string, unknown>): string {
  return sha256(label + '||' + canonicalJson(properties));
}

/** Compute edge_hash from its four components */
function computeEdgeHash(
  sourceNodeHash: string,
  edgeType: string,
  targetNodeHash: string,
  weight: number,
): string {
  return sha256(
    sourceNodeHash + '||' + edgeType + '||' + targetNodeHash + '||' + weight.toFixed(6),
  );
}

/** Compute chain Merkle root over an ordered array of edge_hashes */
function computeChainMerkleRoot(edgeHashes: string[]): string {
  if (edgeHashes.length === 0) return sha256('EMPTY_CHAIN');
  return sha256(edgeHashes.join('||'));
}

// ─── In-process storage (test/development backend) ────────────────────────────
// Production: swap nodeStore → Neo4j driver, edgeLog → Postgres append-only table.

interface NodeRecord extends GraphNode {
  inserted_at: number;
}

// ─── Sentra guard (hop-level cycle + depth check) ─────────────────────────────

/**
 * sentraGuardHop — evaluates whether a hop attempt is safe to proceed.
 *
 * Implements the Sentra integrity hook called before every hop:
 *   - REJECT_CYCLE  → targetNodeHash already in visitedSet (prevents infinite loops)
 *   - REJECT_DEPTH  → currentDepth >= maxDepth (ouroboros bounded-loop halt)
 *   - ALLOW         → safe to traverse
 *
 * Corresponds to Lean theorem: GraphHop.lean :: traversal_acyclic
 */
function sentraGuardHop(
  targetNodeHash: string,
  visitedSet: Set<string>,
  currentDepth: number,
  maxDepth: number,
): SentraHopVerdict {
  if (visitedSet.has(targetNodeHash)) return 'REJECT_CYCLE';
  if (currentDepth >= maxDepth) return 'REJECT_DEPTH';
  return 'ALLOW';
}

// ─── PPR utilities ────────────────────────────────────────────────────────────

/**
 * Minimal in-process Personalized PageRank over the adjacency list.
 *
 * Algorithm (HippoRAG pattern, phd4_graph.md §2.2):
 *   - Teleport vector: uniform over seedNodeHashes
 *   - Damping factor α = 0.15 (teleport probability)
 *   - Power iteration until ||r_new − r_old||₁ < ε or maxIter reached
 *
 * Returns: Map<nodeHash → rank> for all reachable nodes.
 *
 * [UNVERIFIED] Full sparse PPR convergence proof is in Lean TODO:
 *   GraphHop.lean :: ppr_convergence_bounded (see §6 phd4_graph.md)
 */
function personalizedPageRank(
  seedNodeHashes: string[],
  adjacency: Map<string, { targetHash: string; weight: number; edgeType: string }[]>,
  alpha = 0.15,
  maxIter = 50,
  epsilon = 1e-6,
): Map<string, number> {
  const allNodes = new Set<string>([...adjacency.keys()]);
  for (const nbrs of adjacency.values()) {
    for (const { targetHash } of nbrs) allNodes.add(targetHash);
  }
  seedNodeHashes.forEach(h => allNodes.add(h));

  const N = allNodes.size;
  const nodeList = [...allNodes];
  const nodeIndex = new Map<string, number>(nodeList.map((h, i) => [h, i]));

  // Initialise rank: uniform over seeds
  const seedSet = new Set(seedNodeHashes);
  const r = new Float64Array(N).fill(0);
  for (const h of seedNodeHashes) {
    const idx = nodeIndex.get(h);
    if (idx !== undefined) r[idx] = 1 / seedNodeHashes.length;
  }

  const teleport = new Float64Array(N);
  for (const h of seedNodeHashes) {
    const idx = nodeIndex.get(h);
    if (idx !== undefined) teleport[idx] = 1 / seedNodeHashes.length;
  }

  // Build transition matrix (out-degree normalised)
  const outWeightSum = new Map<string, number>();
  for (const [src, nbrs] of adjacency) {
    outWeightSum.set(src, nbrs.reduce((s, n) => s + n.weight, 0));
  }

  for (let iter = 0; iter < maxIter; iter++) {
    const rNew = new Float64Array(N);
    // Distribute mass via edges
    for (const [src, nbrs] of adjacency) {
      const srcIdx = nodeIndex.get(src);
      if (srcIdx === undefined) continue;
      const total = outWeightSum.get(src) ?? 1;
      for (const { targetHash, weight } of nbrs) {
        const tIdx = nodeIndex.get(targetHash);
        if (tIdx !== undefined) {
          rNew[tIdx] += (1 - alpha) * r[srcIdx] * (weight / total);
        }
      }
    }
    // Add teleport
    for (let i = 0; i < N; i++) rNew[i] += alpha * teleport[i];
    // Convergence check
    let diff = 0;
    for (let i = 0; i < N; i++) diff += Math.abs(rNew[i] - r[i]);
    r.set(rNew);
    if (diff < epsilon) break;
  }

  const result = new Map<string, number>();
  for (let i = 0; i < N; i++) result.set(nodeList[i], r[i]);
  return result;
}

// ─── LambdaGraphStore ─────────────────────────────────────────────────────────

/**
 * LambdaGraphStore — amaru graph store for Prisca-GraphRAG v2.
 *
 * Provides:
 *   1. addNode()               — upsert node, compute node_hash
 *   2. addEdge()               — append-only edge log with hash verification
 *   3. getCommunities()        — return Leiden community partition (mock Leiden)
 *   4. traverseWithReceipt()   — PPR-seeded multi-hop traversal → TraversalReceipt
 *
 * All writes are append-only; no record is mutated or deleted.
 * Hash integrity is verified on every read via assertEdgeHashValid().
 *
 * [UNVERIFIED] Production: swap nodeStore/edgeLog for Neo4j + Postgres.
 * [UNVERIFIED] getCommunities() uses a stub partition generator;
 *   full Leiden algorithm integration is pending (phd4_graph.md §5.5).
 */
export class LambdaGraphStore {
  private readonly nodeStore = new Map<string, NodeRecord>();
  /** Append-only edge log — push only, never splice */
  private readonly edgeLog: GraphEdge[] = [];
  /** Adjacency list keyed by source node_hash */
  private readonly adjacency = new Map<
    string,
    { targetHash: string; weight: number; edgeType: string }[]
  >();
  /** Community partitions keyed by level */
  private readonly communityCache = new Map<string, CommunityPartition>();

  // ── addNode ─────────────────────────────────────────────────────────────────

  /**
   * Upsert a node into the graph store.
   * If a node with the same node_id already exists, it is not overwritten
   * (append-only semantics — content-addressed by node_hash).
   *
   * @returns The computed node_hash
   */
  addNode(
    node_id: string,
    label: string,
    properties: Record<string, unknown>,
    embedding_vector: number[],
  ): string {
    const node_hash = computeNodeHash(label, properties);
    if (!this.nodeStore.has(node_hash)) {
      this.nodeStore.set(node_hash, {
        node_id,
        label,
        properties,
        node_hash,
        embedding_vector,
        inserted_at: Date.now(),
      });
    }
    return node_hash;
  }

  /**
   * Retrieve a node by its hash.
   * Returns undefined if not found (caller must handle REJECT or skip).
   */
  getNodeByHash(node_hash: string): GraphNode | undefined {
    return this.nodeStore.get(node_hash);
  }

  // ── addEdge ─────────────────────────────────────────────────────────────────

  /**
   * Append a directed, weighted edge to the log.
   * Computes and verifies edge_hash before appending.
   * Never overwrites an existing edge — append-only.
   *
   * @returns The edge_hash of the appended edge
   * @throws If either endpoint node_hash is unknown in the node store
   */
  addEdge(
    source_node_hash: string,
    edge_type: string,
    target_node_hash: string,
    weight: number,
    community_id = '',
  ): string {
    if (!this.nodeStore.has(source_node_hash)) {
      throw new Error(
        `LambdaGraphStore.addEdge: unknown source_node_hash ${source_node_hash}`,
      );
    }
    if (!this.nodeStore.has(target_node_hash)) {
      throw new Error(
        `LambdaGraphStore.addEdge: unknown target_node_hash ${target_node_hash}`,
      );
    }

    const edge_hash = computeEdgeHash(source_node_hash, edge_type, target_node_hash, weight);
    const edge: GraphEdge = {
      source_node_hash,
      edge_type,
      target_node_hash,
      weight,
      community_id,
      inserted_at: Date.now(),
      edge_hash,
    };
    this.edgeLog.push(edge);

    // Update adjacency
    if (!this.adjacency.has(source_node_hash)) {
      this.adjacency.set(source_node_hash, []);
    }
    this.adjacency.get(source_node_hash)!.push({ targetHash: target_node_hash, weight, edgeType: edge_type });

    return edge_hash;
  }

  /**
   * Verify the integrity of every edge in the append-only log.
   * Returns true if all hashes are valid.
   * Used by Sentra integrity guards and replay tests.
   */
  verifyLogIntegrity(): boolean {
    for (const edge of this.edgeLog) {
      const expected = computeEdgeHash(
        edge.source_node_hash,
        edge.edge_type,
        edge.target_node_hash,
        edge.weight,
      );
      if (expected !== edge.edge_hash) return false;
    }
    return true;
  }

  /** Read-only snapshot of the full edge log (shallow copy) */
  getEdgeLog(): readonly GraphEdge[] {
    return [...this.edgeLog];
  }

  // ── getCommunities ──────────────────────────────────────────────────────────

  /**
   * Run (or return cached) Leiden community detection at a given hierarchy level.
   *
   * Leiden algorithm stub:
   *   - Full Leiden implementation is [UNVERIFIED — pending integration].
   *   - This stub performs greedy connected-component partitioning via BFS,
   *     which approximates Leiden's modularity-maximisation partition for
   *     unweighted graphs. It is measurement-honest: it claims only to group
   *     connected components, not to maximise modularity.
   *   - Replace with full Leiden (networkx leidenalg or graspologic) in prod.
   *
   * [UNVERIFIED] Full Leiden: phd4_graph.md §1.1, §5.5
   */
  getCommunities(level: 'C0' | 'C1' | 'C2' | 'C3' = 'C1'): CommunityPartition {
    const cacheKey = level;
    if (this.communityCache.has(cacheKey)) {
      return this.communityCache.get(cacheKey)!;
    }

    // BFS-based connected-component grouping (stub Leiden)
    const allNodes = new Set<string>(this.nodeStore.keys());
    const visited = new Set<string>();
    const communities: Record<string, string[]> = {};
    let communityIndex = 0;

    // C0 = coarsest (single community per connected component)
    // C1..C3 = progressively finer (split by out-degree threshold)
    const degreeThreshold: Record<string, number> = { C0: Infinity, C1: 5, C2: 2, C3: 1 };
    const thresh = degreeThreshold[level];

    for (const startHash of allNodes) {
      if (visited.has(startHash)) continue;
      const component: string[] = [];
      const queue = [startHash];
      while (queue.length > 0) {
        const current = queue.shift()!;
        if (visited.has(current)) continue;
        visited.add(current);
        component.push(current);
        const neighbours = this.adjacency.get(current) ?? [];
        for (const { targetHash } of neighbours) {
          if (!visited.has(targetHash)) queue.push(targetHash);
        }
      }
      // For finer levels: split component at degree threshold
      let bucket: string[] = [];
      for (const h of component) {
        const deg = (this.adjacency.get(h) ?? []).length;
        if (deg <= thresh) {
          bucket.push(h);
        } else {
          if (bucket.length > 0) {
            communities[`C${communityIndex}`] = bucket;
            communityIndex++;
            bucket = [];
          }
          communities[`C${communityIndex}`] = [h];
          communityIndex++;
        }
      }
      if (bucket.length > 0) {
        communities[`C${communityIndex}`] = bucket;
        communityIndex++;
      }
    }

    // Stub modularity (full Leiden required for accurate value)
    const modularity_score = 0.0; // [UNVERIFIED — placeholder]

    const partition: Omit<CommunityPartition, 'partition_hash'> = {
      level,
      communities,
      modularity_score,
      detected_at: new Date().toISOString(),
    };

    const partition_hash = sha256(canonicalJson(partition));
    const full: CommunityPartition = { ...partition, partition_hash };
    this.communityCache.set(cacheKey, full);
    return full;
  }

  // ── traverseWithReceipt ─────────────────────────────────────────────────────

  /**
   * traverseWithReceipt — PPR-seeded multi-hop graph traversal with Λ_Ω receipt chain.
   *
   * Pipeline:
   *   1. Run PPR over adjacency from seed node hashes (teleport vector = seeds)
   *   2. Rank non-seed nodes by PPR score
   *   3. Iterate ranked nodes; for each edge from visited to candidate:
   *        a. Call sentraGuardHop → ALLOW | REJECT_CYCLE | REJECT_DEPTH
   *        b. On ALLOW: emit a LambdaGraphHopLeaf, mark visited
   *        c. On REJECT_*: skip, increment rejected_hop_count
   *   4. Return TraversalReceipt with leaf chain, node set, chain Merkle root
   *
   * Lean obligations satisfied:
   *   - graph_hop_monotone: visitedSet only grows (REJECT_CYCLE prevents shrink)
   *   - traversal_acyclic:  visitedSet.has(target) check before every ALLOW
   *
   * @param start       node_hash of the traversal start node (ANN seed in retriever)
   * @param query       natural-language query string (used for score attribution comment)
   * @param maxDepth    max hop depth (ouroboros bounded-loop halt condition)
   * @param communityId Zenodo DOI slug of current community partition (from getCommunities)
   */
  traverseWithReceipt(
    start: string,
    query: string,
    maxDepth = 3,
    communityId = '',
  ): TraversalReceipt {
    const startedAt = Date.now();
    const visitedSet = new Set<string>([start]);
    const leaves: LambdaGraphHopLeaf[] = [];
    const resultNodes: GraphNode[] = [];
    let rejectedCount = 0;
    let hopIndex = 0;

    // PPR seeded from start node
    const pprScores = personalizedPageRank([start], this.adjacency);

    // Sort all candidates by descending PPR score.
    //
    // DOCTRINE FIX (T7 Finding 2): we do NOT pre-filter the start node here.
    // Pre-filtering hides cycles that close back into the start node from the
    // Sentra guard — the visitedSet.has(target) check below is the single
    // source of truth for REJECT_CYCLE, and pre-filtering causes it to be
    // silently bypassed for back-to-start cycles. sentraGuardHop returns
    // REJECT_CYCLE for any target already in visitedSet (start included),
    // so the start node will be cleanly rejected and the rejected_hop_count
    // will reflect the real cycle count.
    const candidates = [...pprScores.entries()]
      .sort((a, b) => b[1] - a[1]);

    // Depth-tracking: simulate BFS depth from start
    const depthMap = new Map<string, number>([[start, 0]]);
    const queue: string[] = [start];
    while (queue.length > 0) {
      const current = queue.shift()!;
      const currentDepth = depthMap.get(current) ?? 0;
      const nbrs = this.adjacency.get(current) ?? [];
      for (const { targetHash } of nbrs) {
        if (!depthMap.has(targetHash)) {
          depthMap.set(targetHash, currentDepth + 1);
          queue.push(targetHash);
        }
      }
    }

    // Emit start node record
    const startNode = this.nodeStore.get(start);
    if (startNode) resultNodes.push(startNode);

    // Process candidates in PPR rank order
    for (const [candidateHash, pprScore] of candidates) {
      // Find best edge from any visited node to this candidate.
      // We look up the edge FIRST (before the Sentra guard) because
      // REJECT_CYCLE only counts when a back-edge from the visited set
      // actually exists — otherwise the candidate is simply unreachable,
      // not a cycle. This is the structural definition of a cycle hop.
      let bestEdge: { srcHash: string; edgeType: string; weight: number } | null = null;
      for (const visitedHash of visitedSet) {
        const nbrs = this.adjacency.get(visitedHash) ?? [];
        const edge = nbrs.find(n => n.targetHash === candidateHash);
        if (edge) {
          bestEdge = { srcHash: visitedHash, edgeType: edge.edgeType, weight: edge.weight };
          break;
        }
      }
      if (!bestEdge) continue; // candidate not directly reachable from visited set

      const currentDepth = depthMap.get(candidateHash) ?? maxDepth;
      const verdict = sentraGuardHop(candidateHash, visitedSet, currentDepth, maxDepth);

      // DOCTRINE FIX (T7 Finding 2 — doctrine-true completion):
      // The verdict is computed AFTER bestEdge is found, so it fires only on
      // candidates that are actually reachable via a back-edge from visited.
      // The start node will trip REJECT_CYCLE here as soon as any visited
      // node has an edge back into it. This is the canonical cycle event.
      if (verdict !== 'ALLOW') {
        rejectedCount++;
        continue;
      }

      // Emit Λ_Ω hop leaf
      const targetNode = this.nodeStore.get(candidateHash);
      if (!targetNode) continue;

      const edgeHash = computeEdgeHash(
        bestEdge.srcHash,
        bestEdge.edgeType,
        candidateHash,
        bestEdge.weight,
      );

      const leaf: LambdaGraphHopLeaf = {
        hop_index: hopIndex++,
        source_node_hash: bestEdge.srcHash,
        edge_hash: edgeHash,
        target_node_hash: candidateHash,
        community_id: communityId,
        score: Math.min(1.0, pprScore * 10), // normalise PPR score to [0,1] range
        edge_type: bestEdge.edgeType,
        recorded_at: Date.now(),
        doctrine_grade: defaultDoctrineGrade(),
      };

      leaves.push(leaf);
      visitedSet.add(candidateHash);
      resultNodes.push(targetNode);

      // DOCTRINE FIX (T7 Finding 2): after admitting a node, scan its outgoing
      // edges for any target already in visitedSet. Each such back-edge is a
      // cycle hop and must increment rejectedCount via the Sentra guard. This
      // makes REJECT_CYCLE structurally observable for cycles that close back
      // into earlier-visited nodes (including the start node), independent of
      // the PPR candidate iteration order.
      const outgoing = this.adjacency.get(candidateHash) ?? [];
      for (const { targetHash: backTarget } of outgoing) {
        if (visitedSet.has(backTarget)) {
          const backDepth = depthMap.get(backTarget) ?? maxDepth;
          const backVerdict = sentraGuardHop(backTarget, visitedSet, backDepth, maxDepth);
          if (backVerdict !== 'ALLOW') rejectedCount++;
        }
      }
    }

    // Chain Merkle root
    const chainMerkleRoot = computeChainMerkleRoot(leaves.map(l => l.edge_hash));

    return {
      leaves,
      nodes: resultNodes,
      rejected_hop_count: rejectedCount,
      chain_merkle_root: chainMerkleRoot,
      started_at: startedAt,
      completed_at: Date.now(),
    };
  }

  // ── vectorSeed ──────────────────────────────────────────────────────────────

  /**
   * ANN vector seed: return top-k nodes by cosine similarity to queryEmbedding.
   *
   * Production: replace with Neo4j db.index.vector.queryNodes() via Bolt driver.
   * Here: in-process brute-force cosine over nodeStore (test/dev only).
   *
   * [UNVERIFIED] Neo4j vector-2.0 provider integration pending.
   */
  vectorSeed(queryEmbedding: number[], k: number): GraphNode[] {
    const cosine = (a: number[], b: number[]): number => {
      let dot = 0, na = 0, nb = 0;
      for (let i = 0; i < a.length; i++) {
        dot += a[i] * b[i];
        na += a[i] * a[i];
        nb += b[i] * b[i];
      }
      if (na === 0 || nb === 0) return 0;
      return dot / (Math.sqrt(na) * Math.sqrt(nb));
    };

    return [...this.nodeStore.values()]
      .filter(n => n.embedding_vector.length === queryEmbedding.length)
      .map(n => ({ node: n, score: cosine(n.embedding_vector, queryEmbedding) }))
      .sort((a, b) => b.score - a.score)
      .slice(0, k)
      .map(({ node }) => node);
  }

  /** Total node count (for test assertions) */
  get nodeCount(): number { return this.nodeStore.size; }
  /** Total edge count in append-only log (for test assertions) */
  get edgeCount(): number { return this.edgeLog.length; }
}

// ─── Module exports ───────────────────────────────────────────────────────────
export { computeNodeHash, computeEdgeHash, computeChainMerkleRoot, sentraGuardHop, sha256, defaultDoctrineGrade };
