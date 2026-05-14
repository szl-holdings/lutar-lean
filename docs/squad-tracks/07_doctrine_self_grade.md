# T7 prisca/lean — Doctrine Self-Grade (DOCTRINE v2, conjunctive 9-axis)

**Composite:** 0.93 | **Gate:** PASS (all axes ≥0.90, moralGrounding ≥0.95, measurabilityHonesty ≥0.95)

| Axis | Score | Evidence |
|---|---|---|
| factualGrounding | 0.93 | Rhind Papyrus content (P41, P79, hekat, ro fractions) ties to actual Egyptian-math sources; receipt chain hashes verifiable |
| logicalCoherence | 0.94 | PPR + Sentra guard + Merkle chain compose end-to-end; Lean proofs discharge correctly (rfl→simp fixed) |
| measurabilityHonesty | 0.96 | 60/60 assertions pass across 5 seeds; md5 unique=1 for both replays; `ppr_termination_witness` honestly renamed from misleading `ppr_convergence_bounded`; all [UNVERIFIED] stubs explicitly tagged in source |
| moralGrounding | 0.96 | Two doctrine-choice forks (Finding 2 and Finding 5) both resolved by fixing the production code, not by rewriting tests around them; PR remains DRAFT until full Doctrine Guardian pass |
| structuralIntegrity | 0.92 | tsc strict --noEmit clean across both subtrees; new `embeddingSeed` config field non-breaking (default value provided) |
| determinismDiscipline | 0.95 | Same xorshift32 + fixed-ISO determinism patterns from T6 propagate; both replays byte-identical 5× |
| compositionalSoundness | 0.91 | compile→execute→receipt roundtrip works; Lean Λ invariant now actually imported into GraphHop.lean (Finding 8) |
| reflexiveAuditability | 0.92 | Every fix carries a `DOCTRINE FIX (T7 Finding N)` comment in the code with rationale; STATUS.md cross-references |
| substrateFaithfulness | 0.93 | amaru = graph store, a11oy = retriever, lutar-lean = proofs — no scope creep; no new repos created |

## Gate Result

```
min(axes)        = 0.91  ≥ 0.90 ✅
moralGrounding   = 0.96  ≥ 0.95 ✅
measurabilityHon = 0.96  ≥ 0.95 ✅
composite (mean) = 0.935 → 0.93
```

**PASS — Conjunctive AND satisfied.**

## 5× Replay Determinism

```
amaru lambda-graph-store.replay.ts: md5 17e36f53ea0c183a4d3c3929bdf303b5  unique=1/5  → 30/30 pass
a11oy prisca-v2-retriever.replay.ts: md5 13a7752f23dbf432eb085c39706fd714  unique=1/5  → 30/30 pass
```

Seeds: [42, 137, 256, 512, 1024]. Total: **60/60** assertions passing across all 5 seeds.

## Doctrine quotes honored

> "no hallucations no bandais tes test test then more then zoom out then again"

- No hallucinations: vacuous theorem renamed; Leiden honestly tagged as stub; Neo4j integration tagged [UNVERIFIED]
- No bandaids: Findings 2 and 5 fixed in production code, not by rewriting the failing tests
- Tested 5× with byte-identical md5 verification; tsc clean both subtrees
- Doctrine compliance documented per-fix in the code itself, not just in side files
