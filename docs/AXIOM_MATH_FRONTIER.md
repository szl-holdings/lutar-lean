# Axiom Math × SZL: verified-proof frontier (research lane)

**Reviewed:** 2026-11-17. **Owner:** SZL / `lutar-lean`. **Status:** EXPERIMENTAL; NOT production admission. No outside service or training API is invoked by this change.

## Primary references and lawful adoption

| Public surface | Verified public capability | SZL action |
|---|---|---|
| [Axiom AXLE](https://arxiv.org/abs/2606.26442), [SDK source](https://github.com/AxiomMath/axiom-lean-engine) | 14 proof/declaration utilities (check, strict verify, extraction, merge, repair, normalize, disprove, etc.); multi-version isolated Lean cloud. SDK MIT-licensed; hosted service is independently operated. | Study the SDK and adopt its **conceptual** strict verification/repair loop. Do not transmit unpublished theorem sources externally by default; never equate a remote `okay` or `check` response with local release authority. |
| [Axiom Stacks](https://github.com/AxiomMath/Stacks) | Large Lean formalization; human-reviewed `StacksCore` and AI-frontier `StacksFrontier`; source-tag mappings and explicit axiom disclosure. Apache-2.0 repository; original Stacks scholarly source has separate licensing. | Use the human-review/AI-frontier separation and claim-to-source linkage as design patterns. Do not bulk-copy the library or call it SZL's own original research. |
| [Axiom CFSG](https://github.com/AxiomMath/CFSG), [formalizations](https://axiommath.ai/) | Formalized advanced mathematical structures with reusable dependent lemma graphs. | Benchmark theorem reuse, dependency-closure and source attribution before adding optional imports. |
| [Axiom axplorer](https://github.com/AxiomMath/axplorer) | Public search-and-learning recipe: generate, train, sample, search/score, select, checkpoint. Apache-2.0. | Adapt experiments using distinct SZL datasets and original search objectives; keep provenance for training/evaluation splits and cost. |
| [DeepSeek Prover V2](https://github.com/deepseek-ai/DeepSeek-Prover-V2) and [OpenProver](https://arxiv.org/abs/2607.09217) | Open agentic/recursive proof planning; Lean kernel as final proof authority. | Evaluate as *comparators*, with fixed problems and exact toolchain, not as production or mathematical discovery claims. |

**Boundary:** Axiom's proprietary `AxiomProver` model/training weights are not made public merely because its research papers and some code are public. Reuse must follow each repository's license and provenance; proprietary internals are not available to copy.

## What was built in this bounded experiment

1. **Lean-native admission propositions** in `Showcase/Frontier/ReleaseAdmissionWitness.lean`, compiled by default `lake build` via `FrontierShowcase`. A conditional `Admission` proof requires the **same exact immutable SHA** for source, checked CI, published artifacts and live runtime; current required CI, signed receipt, fresh evidence, runtime probe, owner approval and open maintenance window.
2. **Refusal theorems:** missing signature, stale evidence, wrong CI head, publisher/source mismatch, runtime mismatch, missing approval or closed window imply **no admission**. A publisher mismatch is not automatically proven `SOURCE_AHEAD`; GitHub ancestry and publisher readback are needed for that classification.
3. **Noncompensatory advisory math:** let `g(e) ∈ {0,1}` represent conjunction of mandatory admission witnesses and let `Λ(e)∈[0,1]` be an advisory trust score. Define `T(e)=g(e)·Λ(e)`. Even a high Λ cannot compensate for a failed mandatory gate. This is a new **SZL policy composition**, **not a claim to have invented the underlying Boolean algebra or proved Λ uniqueness**.
4. **Offline executable oracle** in `tools/release_admission.py`, paired with `tools/test_release_admission.py` exhaustive 64-way Boolean refusal matrix and SHA drift/absence checks. The existing **snapshot-anchor-selftest** GitHub Actions job runs the oracle's tests without a new workflow.
5. **Important separation:** the Lean propositions and Python oracle agree on the declared gate shape. There is **no refinement proof** linking Python, GitHub APIs, signature verifier or the Hugging Face runtime, and no external collector in this PR. Consequently, an `ELIGIBLE_NOT_DEPLOYED` result is **not** a production release.

## AXLE strictness / gaps before scaling

- **Exact theorem statement**: forbid automated proof agents from altering theorem signatures. Pin the source statement, full Lean/Mathlib version and source SHA; compare candidate theorem against that exact statement.
- **Axiom hygiene**: treat `sorryAx`, novel axioms, `unsafe` evaluation and proof-evaluation tricks as separate refusal classes. Lean compilation alone is insufficient; require explicit `#print axioms` or a vetted Comparator/lean4checker and a named allowlist. **Do not classify the entire existing `lutar-lean` corpus as sorry-free**: `SORRIES.md` reports a 61-placeholder tracked corpus baseline as of Nov 6. Keep the locked-eight claim unchanged.
- **Toolchain mismatch**: SZL `lean-toolchain` is pinned to Lean v4.35.0, while Axiom Stacks README describes Lean v4.34.0-rc2. Never combine libraries across these toolchains without an explicit reproducible migration.
- **Published origin**: source CI `success` does not prove signed HF receipts, live readback, correct source SHA, resolved deployment window or cryptographic signature. This release policy must **fail closed** until a trusted collector supplies these observations.
- **Training honesty**: cache only proof candidates and a versioned corpus, publish kernel-checked results separately from candidate rankings; enforce non-leakage splits and independent held-out tasks; do not advertise autonomous theorem discoveries from a draft proof.

## Next admission work (not completed by this PR)

Implement an authenticated read-only collector that records protected-main SHA, required status checks, per-workflow current heads, signature verification using an authorized key/trust policy, freshness, exact HF published SHA and runtime readback. Replay the collector's serialized observations through the Python oracle. Independently evaluate Lean kernel-checked candidates against public Axiom/DeepSeek/OpenProver benchmarks with explicit licenses and theorem-statement preservation. Keep repo changes behind protected-branch CI/approval; no bulk 2,000-workflow dispatch or auto-production release.
