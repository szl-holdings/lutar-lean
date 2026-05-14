/**
 * lambda-graph-store.replay.ts
 * Prisca-GraphRAG v2 — LambdaGraphStore 5× variance replay test
 *
 * Repo:    amaru/src/graph/lambda-graph-store.replay.ts
 * Author:  Stephen P. Lutar Jr. <stephen@szlholdings.com>
 * Doctrine: v2 binding — test×5 seeds [42, 137, 256, 512, 1024], no bandaids
 *
 * Test contract (from 99_synthesis §3.4):
 *   1. Determinism:        leaf edge_hash identical across runs for same seed
 *   2. Log integrity:      verifyLogIntegrity() === true after all writes
 *   3. Cycle rejection:    deliberate cycle injection → REJECT_CYCLE assertion
 *   4. Monotone traversal: visitedSet never shrinks (hop_index always increases)
 *   5. Merkle root:        chain_merkle_root matches re-computed value
 *
 * Run: npx ts-node lambda-graph-store.replay.ts
 *      OR: node --loader ts-node/esm lambda-graph-store.replay.ts
 */

import { LambdaGraphStore, computeChainMerkleRoot, sha256 } from './lambda-graph-store.js';
import type { TraversalReceipt } from './lambda-graph-store.types.js';

// ─── Seeds ────────────────────────────────────────────────────────────────────

const SEEDS = [42, 137, 256, 512, 1024] as const;

// ─── Corpus builder (Egyptian-math adapter, phd4_graph.md §5.4) ───────────────

/**
 * buildEgyptianMathGraph — builds a deterministic Egyptian-math test corpus.
 *
 * Nodes represent problems, operations, quantities, and units from the
 * Rhind Mathematical Papyrus (Rhind_P79, P41) and hekat unit system.
 * Edge types: USES, DERIVED_FROM, PART_OF, MULTIPLES.
 *
 * The graph includes a deliberate cycle (UNIT_hekat → UNIT_ro → UNIT_hekat)
 * to test REJECT_CYCLE assertion in test 3.
 */
function buildEgyptianMathGraph(seed: number): {
  store: LambdaGraphStore;
  nodeHashes: Record<string, string>;
  cyclePairHashes: [string, string]; // [A, B] where A→B and B→A both exist
} {
  const store = new LambdaGraphStore();
  // Deterministic pseudo-random embedding based on seed
  const embed = (name: string): number[] => {
    const dim = 16;
    const v = new Array<number>(dim).fill(0);
    for (let i = 0; i < name.length; i++) {
      v[i % dim] += (name.charCodeAt(i) * seed) % 256;
    }
    const norm = Math.sqrt(v.reduce((s, x) => s + x * x, 0)) || 1;
    return v.map(x => x / norm);
  };

  // Nodes (phd4_graph.md §5.4 Egyptian-math corpus)
  const n: Record<string, string> = {};

  n.problem_p41 = store.addNode('PROBLEM_P41', 'PROBLEM', {
    papyrus_ref: 'Rhind_P41', text: 'Truncated pyramid volume computation',
  }, embed('PROBLEM_P41'));

  n.op_cube_root = store.addNode('OP_CUBE_ROOT', 'OPERATION', {
    name: 'cube_root', papyrus_ref: 'Rhind_P41',
  }, embed('OP_CUBE_ROOT'));

  n.op_multiply = store.addNode('OP_MULTIPLY', 'OPERATION', {
    name: 'multiply', papyrus_ref: 'Rhind_P41',
  }, embed('OP_MULTIPLY'));

  n.qty_height = store.addNode('QTY_HEIGHT', 'QUANTITY', {
    name: 'height', numeric_value: 6, papyrus_ref: 'Rhind_P41',
  }, embed('QTY_HEIGHT'));

  n.qty_base = store.addNode('QTY_BASE', 'QUANTITY', {
    name: 'base', numeric_value: 4, papyrus_ref: 'Rhind_P41',
  }, embed('QTY_BASE'));

  n.unit_hekat = store.addNode('UNIT_HEKAT', 'UNIT', {
    name: 'hekat', papyrus_ref: 'Rhind_hekat',
  }, embed('UNIT_HEKAT'));

  n.unit_ro = store.addNode('UNIT_RO', 'UNIT', {
    name: 'ro', fraction: '1/320', papyrus_ref: 'Rhind_hekat',
  }, embed('UNIT_RO'));

  n.qty_ration = store.addNode('QTY_RATION', 'QUANTITY', {
    name: 'ration', papyrus_ref: 'Rhind_hekat',
  }, embed('QTY_RATION'));

  n.problem_p79 = store.addNode('PROBLEM_P79', 'PROBLEM', {
    papyrus_ref: 'Rhind_P79', text: 'Houses contain cats contain mice contain wheat',
  }, embed('PROBLEM_P79'));

  // Edges — 4-hop chain: PROBLEM_P41 → OP_CUBE_ROOT → OP_MULTIPLY → QTY_HEIGHT → QTY_BASE
  store.addEdge(n.problem_p41, 'USES', n.op_cube_root, 1.0, '10.5281/zenodo.20020846');
  store.addEdge(n.op_cube_root, 'DERIVED_FROM', n.op_multiply, 0.8, '10.5281/zenodo.20020846');
  store.addEdge(n.op_multiply, 'USES', n.qty_height, 0.9, '10.5281/zenodo.20020846');
  store.addEdge(n.qty_height, 'RELATED_TO', n.qty_base, 0.7, '10.5281/zenodo.20020846');

  // Hekat unit chain: UNIT_HEKAT → UNIT_RO → QTY_RATION
  store.addEdge(n.unit_hekat, 'PART_OF', n.unit_ro, 1.0, '10.5281/zenodo.20020846');
  store.addEdge(n.unit_ro, 'RELATED_TO', n.qty_ration, 0.6, '10.5281/zenodo.20020846');

  // Cross-link: PROBLEM_P79 → UNIT_HEKAT
  store.addEdge(n.problem_p79, 'USES', n.unit_hekat, 0.5, '10.5281/zenodo.20020846');

  // ── Deliberate cycle injection (test 3) ──────────────────────────────────
  // UNIT_HEKAT → UNIT_RO exists above.
  // Add reverse edge: UNIT_RO → UNIT_HEKAT (creates cycle).
  // The traversal Sentra guard MUST reject this as REJECT_CYCLE when
  // UNIT_HEKAT is already in visitedSet during a traversal starting at UNIT_HEKAT.
  store.addEdge(n.unit_ro, 'RELATED_TO', n.unit_hekat, 0.4, '10.5281/zenodo.20020846');

  return { store, nodeHashes: n, cyclePairHashes: [n.unit_hekat, n.unit_ro] };
}

// ─── Test runner ──────────────────────────────────────────────────────────────

type TestResult = { seed: number; passed: boolean; reason?: string };

function runReplayTests(seed: number): TestResult[] {
  const results: TestResult[] = [];
  const { store, nodeHashes } = buildEgyptianMathGraph(seed);

  // ── Test 1: Log integrity after all writes ───────────────────────────────
  const integrityOk = store.verifyLogIntegrity();
  results.push({
    seed,
    passed: integrityOk,
    reason: integrityOk ? undefined : 'verifyLogIntegrity() returned false',
  });

  // ── Test 2: Deterministic traversal from PROBLEM_P41 ────────────────────
  // Run twice with same start node; chain_merkle_root must be identical.
  const r1 = store.traverseWithReceipt(
    nodeHashes.problem_p41,
    'Rhind Papyrus truncated pyramid volume computation',
    4,
    '10.5281/zenodo.20020846',
  );
  const r2 = store.traverseWithReceipt(
    nodeHashes.problem_p41,
    'Rhind Papyrus truncated pyramid volume computation',
    4,
    '10.5281/zenodo.20020846',
  );
  const deterministic = r1.chain_merkle_root === r2.chain_merkle_root;
  results.push({
    seed,
    passed: deterministic,
    reason: deterministic
      ? undefined
      : `Merkle roots differ: ${r1.chain_merkle_root} vs ${r2.chain_merkle_root}`,
  });

  // ── Test 3: REJECT_CYCLE assertion ──────────────────────────────────────
  // Start from UNIT_HEKAT; the cycle UNIT_RO → UNIT_HEKAT must be rejected.
  const rCycle = store.traverseWithReceipt(
    nodeHashes.unit_hekat,
    'hekat subfractions',
    5,
    '10.5281/zenodo.20020846',
  );
  // No node should appear twice in traversal_nodes
  const nodeIdsSeen = rCycle.nodes.map(n => n.node_id);
  const uniqueNodeIds = new Set(nodeIdsSeen);
  const noDuplicates = uniqueNodeIds.size === nodeIdsSeen.length;
  results.push({
    seed,
    passed: noDuplicates,
    reason: noDuplicates
      ? undefined
      : `Duplicate nodes in traversal (cycle not rejected): ${JSON.stringify(nodeIdsSeen)}`,
  });
  // Also assert that rejected_hop_count > 0 (cycle was encountered and rejected)
  const cycleWasRejected = rCycle.rejected_hop_count > 0;
  results.push({
    seed,
    passed: cycleWasRejected,
    reason: cycleWasRejected
      ? undefined
      : 'REJECT_CYCLE: expected rejected_hop_count > 0 but got ' + rCycle.rejected_hop_count,
  });

  // ── Test 4: Monotone hop_index in traversal from PROBLEM_P41 ────────────
  const monotone = r1.leaves.every((leaf, i) => leaf.hop_index === i);
  results.push({
    seed,
    passed: monotone,
    reason: monotone
      ? undefined
      : 'hop_index not monotone: ' + JSON.stringify(r1.leaves.map(l => l.hop_index)),
  });

  // ── Test 5: chain_merkle_root re-computation matches stored value ────────
  const recomputed = sha256(r1.leaves.map(l => l.edge_hash).join('||'));
  const merkleOk =
    r1.leaves.length === 0
      ? r1.chain_merkle_root === sha256('EMPTY_CHAIN')
      : r1.chain_merkle_root === recomputed;
  results.push({
    seed,
    passed: merkleOk,
    reason: merkleOk
      ? undefined
      : `Merkle mismatch: stored=${r1.chain_merkle_root} recomputed=${recomputed}`,
  });

  return results;
}

// ─── Main ─────────────────────────────────────────────────────────────────────

function main(): void {
  console.log('=== lambda-graph-store.replay.ts ===');
  console.log(`Seeds: [${SEEDS.join(', ')}]\n`);

  let totalPass = 0;
  let totalFail = 0;
  const allResults: TestResult[] = [];

  for (const seed of SEEDS) {
    const results = runReplayTests(seed);
    allResults.push(...results);
    const pass = results.filter(r => r.passed).length;
    const fail = results.filter(r => !r.passed).length;
    totalPass += pass;
    totalFail += fail;
    console.log(`Seed ${seed}: ${pass}/${results.length} passed`);
    for (const r of results) {
      if (!r.passed) console.log(`  FAIL [seed=${r.seed}]: ${r.reason}`);
    }
  }

  console.log(`\nTotal: ${totalPass}/${totalPass + totalFail} passed`);

  if (totalFail > 0) {
    console.error(`\n[REPLAY FAIL] ${totalFail} assertion(s) failed.`);
    process.exit(1);
  } else {
    console.log('\n[REPLAY PASS] All 5× seeds × 6 assertions = 30 assertions passed.');
  }
}

main();
