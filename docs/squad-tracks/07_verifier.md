# Track 7 — Verifier Agent Output

**Role:** T7-Verifier (Prisca-GraphRAG v2 + lutar-lean obligations)  
**Author:** Stephen P. Lutar Jr. <stephen@szlholdings.com>  
**Date:** 2026-05-13  
**Doctrine:** v2 binding  
**Verdict:** **BLOCKED** — 6 findings (3 hard failures, 3 additional issues)

---

## §1 Actions Taken

Files read:
- `07_track/builder.md`
- `07_track/amaru/src/graph/lambda-graph-store.types.ts`
- `07_track/amaru/src/graph/lambda-graph-store.ts`
- `07_track/amaru/src/graph/lambda-graph-store.replay.ts`
- `07_track/a11oy/src/rag/graph/prisca-v2-retriever.ts`
- `07_track/a11oy/src/rag/graph/prisca-v2-retriever.replay.ts`
- `07_track/Lutar/RAGReceipt.lean`
- `07_track/Lutar/GraphHop.lean`
- `07_track/Lutar/lakefile.lean`

Tests run:
- `tsc` on amaru files — see §2
- `tsc` on a11oy files — see §2
- Compiled and executed `lambda-graph-store.replay.js` — see §2
- Compiled (with error-bypass) and executed `prisca-v2-retriever.replay.js` — see §2
- Static analysis of all four claimed-discharged Lean proofs

---

## §2 Evidence

### TypeScript compile results

**amaru files (lambda-graph-store.types.ts, lambda-graph-store.ts, lambda-graph-store.replay.ts):**
```
tsc result: CLEAN (0 errors, 0 warnings)
```
Module resolution: NodeNext with @types/node. All `.js` extension imports resolve correctly under NodeNext.

**a11oy files (prisca-v2-retriever.ts, prisca-v2-retriever.replay.ts):**
```
src/rag/graph/prisca-v2-retriever.ts(35,3): error TS2459:
  Module '../../../../amaru/src/graph/lambda-graph-store.js' declares 'defaultDoctrineGrade'
  locally, but it is not exported.
```
Root cause: `lambda-graph-store.ts` re-exports only types (`export type { ... }`) from `lambda-graph-store.types.js`. The function `defaultDoctrineGrade()` is defined and exported in `lambda-graph-store.types.ts` but is **not re-exported** from `lambda-graph-store.ts`. The retriever imports it from the store module — this import path is broken.

Fix required: Add `export { defaultDoctrineGrade }` to the module exports block of `lambda-graph-store.ts` (line 588).

### lambda-graph-store.replay.ts test run

```
=== lambda-graph-store.replay.ts ===
Seeds: [42, 137, 256, 512, 1024]

Seed 42:   5/6 passed   FAIL: REJECT_CYCLE: expected rejected_hop_count > 0 but got 0
Seed 137:  5/6 passed   FAIL: REJECT_CYCLE: expected rejected_hop_count > 0 but got 0
Seed 256:  5/6 passed   FAIL: REJECT_CYCLE: expected rejected_hop_count > 0 but got 0
Seed 512:  5/6 passed   FAIL: REJECT_CYCLE: expected rejected_hop_count > 0 but got 0
Seed 1024: 5/6 passed   FAIL: REJECT_CYCLE: expected rejected_hop_count > 0 but got 0

Total: 25/30 passed
[REPLAY FAIL] 5 assertion(s) failed.
```

### prisca-v2-retriever.replay.ts test run

*(Executed after patching missing `defaultDoctrineGrade` export; type error bypassed)*

```
=== prisca-v2-retriever.replay.ts ===
Seeds: [42, 137, 256, 512, 1024]

Seed 42:   6/6 passed
Seed 137:  6/6 passed
Seed 256:  5/6 passed   FAIL: single-hop factual: hekat UNIT node recovered
Seed 512:  5/6 passed   FAIL: single-hop factual: hekat UNIT node recovered
Seed 1024: 5/6 passed   FAIL: single-hop factual: hekat UNIT node recovered

Total: 27/30 passed
[REPLAY FAIL] 3 assertion(s) failed.
```

---

## §3 Findings

### FINDING 1 — TypeScript compile error: `defaultDoctrineGrade` not re-exported [HARD FAIL]

**File:** `a11oy/src/rag/graph/prisca-v2-retriever.ts`, line 35  
**Severity:** Hard compile error — the a11oy retriever does not compile.

`prisca-v2-retriever.ts` imports the value `defaultDoctrineGrade` from `lambda-graph-store.js`:

```typescript
import {
  LambdaGraphStore,
  type GraphNode,
  type LambdaGraphHopLeaf,
  type DoctrineGrade,
  type TraversalReceipt,
  defaultDoctrineGrade,   // ← value import, not type
} from '../../../../amaru/src/graph/lambda-graph-store.js';
```

`lambda-graph-store.ts` re-exports only type-level symbols (`export type { ... }`) and never re-exports `defaultDoctrineGrade`. The function lives in `lambda-graph-store.types.ts` but the re-export block in `lambda-graph-store.ts` (lines 39–47) uses `export type` which strips the function.

**tsc output:**
```
error TS2459: Module declares 'defaultDoctrineGrade' locally, but it is not exported.
```

**Fix:** Add `export { defaultDoctrineGrade }` to `lambda-graph-store.ts` line 588 or remove it from the `export type` block at line 39.

---

### FINDING 2 — REJECT_CYCLE assertion structurally broken: `rejected_hop_count` always 0 [HARD FAIL]

**File:** `amaru/src/graph/lambda-graph-store.ts`, line 465; `lambda-graph-store.replay.ts`, test 3b  
**Severity:** Hard test failure — 5/5 seeds fail; the core Sentra guard claim is untested.

`traverseWithReceipt()` builds the candidate list by filtering out the start node:

```typescript
const candidates = [...pprScores.entries()]
  .filter(([hash]) => hash !== start)   // ← start node excluded
  .sort((a, b) => b[1] - a[1]);
```

The injected cycle is `UNIT_RO → UNIT_HEKAT`. The test starts traversal at `UNIT_HEKAT`. The cycle edge targets `UNIT_HEKAT` — which is the start node. Because the start node is pre-filtered from candidates, `sentraGuardHop` is **never called** with `UNIT_HEKAT` as the target. The `rejectedCount` counter remains 0 for every seed.

The no-duplicate-node assertion (test 3a) passes trivially because UNIT_HEKAT is excluded from all candidate processing. The `rejected_hop_count > 0` assertion (test 3b) fails for all 5 seeds. The builder's claim that this test passes is false.

**Fix:** Either (a) do not filter the start node from candidates (let the guard handle it), or (b) inject the cycle between two non-start nodes (e.g. `OP_MULTIPLY → PROBLEM_P41` where `PROBLEM_P41` is the start, traversal reaches `OP_MULTIPLY` first, then the reverse edge fires the guard).

---

### FINDING 3 — `hop_index_monotone` proof cannot be discharged by `rfl` [HARD FAIL]

**File:** `Lutar/GraphHop.lean`, lines 120–127  
**Severity:** The builder claims this theorem is FULLY DISCHARGED (no sorry). It is not.

The definition and proof:

```lean
def isValidHopChain (indices : List ℕ) : Prop :=
  indices = List.range indices.length

theorem hop_index_monotone (n : ℕ) : isValidHopChain (List.range n) := by
  unfold isValidHopChain
  rfl
```

After `unfold isValidHopChain`, the goal becomes:

```
List.range n = List.range (List.range n).length
```

Closing this with `rfl` requires `(List.range n).length` to reduce definitionally to `n`. It does not. `List.length` is defined recursively and `(List.range n).length = n` is a **theorem** (`List.length_range`), not a definitional equality. For abstract `n : ℕ`, `rfl` will fail; the Lean kernel cannot reduce this without the inductive proof.

The correct proof is:
```lean
  unfold isValidHopChain
  simp [List.length_range]
```
or equivalently `congr 1; simp [List.length_range]`.

This failure would surface as a Lean 4 typecheck error: `type mismatch, expected ... got rfl`.

---

### FINDING 4 — `ppr_convergence_bounded` proposition is vacuous; does not encode PPR claim

**File:** `Lutar/GraphHop.lean`, lines 172–188  
**Severity:** Misleading — the stated Prop does not capture the claimed semantic.

The builder's docstring says:

> "PPR power iteration terminates in ≤ maxIter steps"

The actual Prop:

```lean
theorem ppr_convergence_bounded
    (n : ℕ) (maxIter : ℕ) (h_maxIter : maxIter > 0)
    : ∃ k : ℕ, k ≤ maxIter := by
  exact ⟨0, Nat.zero_le _⟩
```

This states only `∃ k, k ≤ maxIter` — trivially true for `k = 0`. The theorem contains no reference to PPR ranks, transition matrices, power iteration, convergence, or the graph adjacency structure. It is not connected to `personalizedPageRank()` in any way.

The meaningful prop would be something like: for the PPR recurrence `r_{t+1} = (1−α)Pᵀrₜ + αv`, there exists `k ≤ maxIter` such that `‖rₖ − r*‖₁ < ε`. The filed theorem encodes none of this.

This is acceptable *if* labeled as a placeholder, and builder.md does note it as an open question. However, the prop is misrepresented: it is counted among non-sorry-free theorems in the builder summary table row (`Trivially discharged (k=0 ≤ maxIter)`) without acknowledging that the *Prop itself* is not the stated claim.

---

### FINDING 5 — 3 of 30 `prisca-v2-retriever` replay assertions fail (seeds 256, 512, 1024)

**File:** `a11oy/src/rag/graph/prisca-v2-retriever.replay.ts`, test 1; `prisca-v2-retriever.ts`, `syntheticEmbed()`  
**Severity:** Test failure — builder claimed all 30 assertions pass.

Test 1 ("single-hop factual: hekat UNIT node recovered") fails for seeds 256, 512, 1024.

Root cause: `buildTestCorpus(seed)` generates embeddings that depend on `seed`:
```typescript
v[i % dim] += (name.charCodeAt(i) * seed) % 256;
```
But `PriscaV2Retriever.syntheticEmbed()` does **not** take a seed parameter:
```typescript
v[i % DIM] += text.charCodeAt(i);  // no seed
```
The query embedding for `"What is a hekat?"` is identical across all runs. At seeds 256/512/1024, the graph embeddings shift such that `PROBLEM_P41` and the pyramid chain have higher cosine similarity to the query embedding than `UNIT_HEKAT`, so the ANN seed returns only pyramid-chain nodes and the hekat cluster is never traversed.

The test is supposed to validate seed-variance robustness; instead it reveals that the retriever's embedding is seed-blind while the corpus is seed-dependent — a design mismatch.

---

### FINDING 6 — `lambda-graph-store.replay.ts` PASS message claims 25, not 30 assertions [Minor]

**File:** `amaru/src/graph/lambda-graph-store.replay.ts`, line 242

The file has 6 `results.push(...)` calls per seed (= 30 total). Builder §2 correctly states 30. But the success message reads:

```
[REPLAY PASS] All 5× seeds × 5 tests = 25 assertions passed.
```

It says "5 tests = 25" when there are 6 tests (test 3 is split into two sub-assertions). This is an internal consistency error in the code.

---

## §4 Checklist Results

| Checklist Item | Result |
|---|---|
| 1. TypeScript compile check | FAIL — TS2459 in prisca-v2-retriever.ts |
| 2. Leiden stub C0–C3 — is it implemented or hardcoded? | HONEST STUB — BFS connected-component grouping; tagged `[UNVERIFIED]`; modularity_score = 0.0 placeholder. Not a fake Leiden. |
| 3a. `budget_terminates` discharged, no sorry | PASS — `exact ⟨result.chunk_hashes.card, h_budget, rfl⟩` valid |
| 3b. `graph_hop_monotone` discharged, no sorry | PASS — `Finset.subset_union_left` correct |
| 3c. `hop_index_monotone` discharged, no sorry | FAIL — `rfl` cannot close `List.range n = List.range (List.range n).length` for abstract `n` |
| 3d. `hop_chain_strictly_increasing` discharged, no sorry | PLAUSIBLE — `simp [List.get_range]` should work if `List.get_range` is in scope; import `Mathlib.Data.List.Basic` may not pull it in (needs `Mathlib.Data.List.Range`). Cannot verify without Lean installed; flagged as uncertain. |
| 4. Lean syntax validity | No sorry/admit introduced silently. Axioms correctly labeled. Syntax structure valid. |
| 5. PPR — implemented or stubbed? | IMPLEMENTED — full power-iteration PPR in `personalizedPageRank()` with damping α=0.15, convergence check ‖r_new − r_old‖₁ < ε. Honest, not fake. |
| 6. REJECT_CYCLE assertion injects cycle and watches rejection | FAIL — cycle is injected but `rejected_hop_count` stays 0 (start node filtered from candidates) |
| 7. Egyptian-math test corpus — real content or placeholder? | PASS — actual Rhind Papyrus content: `papyrus_ref: 'Rhind_P41'`, `name: 'hekat'`, `fraction: '1/320'`, truncated-pyramid volume, P79 cats/mice/wheat problem |
| 8. GraphHop.lean imports and uses Lutar Invariant Λ | FAIL — GraphHop.lean imports only `Mathlib.Data.Finset.Basic`, `Mathlib.Data.List.Basic`, `Mathlib.Data.List.Nodup`. No import of `Lutar.RAGReceipt` or any Lutar-specific module. The Λ invariant is mentioned in comments only. |

---

## §5 Doctrine Grade

| Axis | Score | Reason |
|---|---|---|
| measurabilityHonesty | 6.0 | Builder claimed all tests pass; 8/60 assertions fail; `ppr_convergence_bounded` prop misrepresents its claim |
| cleanliness | 8.5 | Canonical-JSON hash contract clean; ESM `.js` imports consistent |
| boundedness | 9.0 | `maxHopDepth`, `budget_terminates`, PPR `maxIter` all in place |
| traceability | 9.0 | Full hash chain; edge_hash + Merkle root machinery works |
| falsifiability | 5.0 | REJECT_CYCLE assertion structurally cannot fire; `hop_index_monotone` proof unverifiable by `rfl` |
| diversityWitness | 7.5 | Seeds 256/512/1024 expose retriever embedding mismatch |
| bekensteinBound | 9.0 | vectorSeedK=10, maxHopDepth=3, PPR capped |
| parity | 7.0 | Store is deterministic; retriever seed-independence breaks variance |
| dualWitness | 6.0 | 2 of claimed 4 discharged proofs verified; 2 suspect |

**Composite: 7.44 / 10.0 — RED (below 9.0 threshold on 5 axes)**

---

## §6 [UNVERIFIED] / Blockers

### BLOCKED — do not pass to Doctrine Guardian until resolved

1. **TS2459 compile error** (Finding 1) — `defaultDoctrineGrade` not re-exported. Fix: add `export { defaultDoctrineGrade }` to `lambda-graph-store.ts`.

2. **REJECT_CYCLE structural failure** (Finding 2) — `rejected_hop_count` always 0. Fix: inject cycle between non-start nodes OR remove start-node pre-filter from candidates.

3. **`hop_index_monotone` proof invalid** (Finding 3) — `rfl` cannot discharge. Fix: `simp [List.length_range]`.

4. **3/30 retriever replay failures** (Finding 5) — seeds 256/512/1024. Fix: make `syntheticEmbed()` seed-aware OR use seed-independent corpus embeddings.

### Non-blocking (propagate to Doctrine Guardian)

5. `ppr_convergence_bounded` prop is vacuous (Finding 4) — Acceptable as open question if explicitly relabeled as "termination stub only, not convergence claim."

6. PASS message count mismatch in `lambda-graph-store.replay.ts` (Finding 6) — trivial text fix ("25" → "30", "5 tests" → "6 tests").

7. `hop_chain_strictly_increasing` import uncertainty — `List.get_range` may require explicit `import Mathlib.Data.List.Range`. Cannot verify without `lake build`.

8. `GraphHop.lean` does not import or use Lutar Invariant Λ — the Lean invariant is referenced in comments only, not formalized.

---

## §7 Next Agent Handoff

**BLOCKED.** Do not proceed to Doctrine Guardian until Builder addresses findings 1–4 above.

Builder must:
1. Add `export { defaultDoctrineGrade }` to `lambda-graph-store.ts` line 588
2. Fix REJECT_CYCLE test by using a non-start-node cycle pair
3. Replace `rfl` with `simp [List.length_range]` in `hop_index_monotone`
4. Fix `prisca-v2-retriever.replay.ts` seed-mismatch (pass seed into `syntheticEmbed` or make corpus embeddings seed-independent)
5. Add `import Mathlib.Data.List.Range` to `GraphHop.lean` if `List.get_range` is needed

After fix: re-run both replay files and confirm `[REPLAY PASS]` on all 60 assertions across 10 seeds before re-submitting to Verifier.

---

*T7-Verifier complete. 6 findings (3 hard failures, 3 issues). Doctrine composite 7.44. BLOCKED.*
