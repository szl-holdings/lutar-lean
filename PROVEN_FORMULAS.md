<!--
  szl-holdings/lutar-lean — PROVEN_FORMULAS.md
  The single honest showcase of every proven / kernel-verified result, with proof links + maturity.
  Source of truth: lutar-lean@main (kernel c7c0ba17, 749 declarations / 14 unique axioms / 163 sorries).
  Honesty doctrine v11 LOCKED — locked proven = exactly 5; Λ = Conjecture 1 (never a theorem).
-->

# Proven Formulas — the honest showcase

> **One rule governs this page:** we list only what the Lean kernel checks, with the exact maturity of each result and a link to its proof. The **locked proven set is exactly five formulas**. Everything newer is **experimental / CI-green** and is *never* folded into the locked count. **Λ-uniqueness is Conjecture 1** — proven only conditionally, machine-checked *false* unconditionally.

**Toolchain:** Lean `v4.13.0` · Mathlib pinned `d7317655` (`v4.13.0`)
**Locked kernel:** `c7c0ba17` · **749** declarations / **14** unique axioms / **163** tracked sorries · `lake build` clean
**Maturity legend:** **PROVEN** = sorry-free, Lean-core axioms only `[propext, Classical.choice, Quot.sound]` · **AXIOM-GATED** = sorry-free given a declared, cited idealization · **CI-GREEN(MD)** = Mathlib-dependent, kernel-checked by CI · **COND.** = conditional on a declared axiom · **CONJECTURE** = not a theorem

---

## 1. Locked kernel — proven, sorry-free (exactly 5)

These five are the only formulas counted as **proven** in the locked Doctrine-v11 kernel `c7c0ba17`. Source: [`Lutar/Puriq/Formulas/PuriqFormulaLean.lean`](https://github.com/szl-holdings/lutar-lean/blob/main/Lutar/Puriq/Formulas/PuriqFormulaLean.lean).

| ID | Theorem | What it proves | Maturity | `#print axioms` |
|---|---|---|---|---|
| **F1** | Replay-Hash Determinism (`f1_replay_fold_deterministic`, `f1_replay_fold_eq_trace_last`) | A pure deterministic replay step is a congruence: replaying the **same** recorded log from the same initial state yields a **bit-identical** trace — no drift. Underpins the Khipu replay-hash gate. | **PROVEN** | Lean-core only |
| **F11** | Ayni Reciprocity Conservation (`f11_ayni_reciprocity_conservation`, `f11_tit_for_tat_parity`) | Fold-replay of an append-only reciprocity log conserves the balance invariant (Axelrod–Hamilton tit-for-tat parity). | **PROVEN** | Lean-core only |
| **F12** | Kuramoto Phase-Coupling Boundedness — **additive fragment** (`f12_*`) | The discretised reciprocity coupling stays bounded under additive superposition over an organ set. **Honesty caveat: additive scaffolding ONLY — NOT the full nonlinear Kuramoto synchronization.** | **PROVEN** (additive fragment) | Lean-core only |
| **F18** | Reed–Solomon `RS(10,6)` Recovery Arithmetic (`f18_*`) | Erasure tolerance: data is recoverable **iff at least 6 of 10 shards survive** — the resilience arithmetic for the receipt/payload encoding. | **PROVEN** | Lean-core only |
| **F19** | Bekenstein Additive Scaffolding (`f19_*`) | Entropy budget is additive and monotone over a region partition (per-region ≤ total). **Honesty caveat: monotone scaffolding ONLY — NOT the full Bekenstein bound `S ≤ 2πkRE/(ℏc)`.** | **PROVEN** (additive fragment) | Lean-core only |

> F12 and F19 prove **only the additive / linear fragment** — never described as "Kuramoto synchronization proved" or "Bekenstein bound proved." The Lean docstrings carry the caveat verbatim.

---

## 2. Experimental, kernel-verified (CI-green) — labeled experimental, NOT in the locked 5

Every campaign below is kernel-checked by lutar-lean CI but lives in the **experimental scope** — it does **not** move the locked count of 5 and does **not** change Λ's Conjecture-1 status. Cite the PR for the green head SHA and `#print axioms` cleanliness.

| Campaign | PR | CI-green head | Count | Axiom posture |
|---|---|---|---|---|
| **Agentic loop P1–P6** — the governed RAG→MCP→kernel→receipt loop proven as a **system** | [#188](https://github.com/szl-holdings/lutar-lean/pull/188) | `2ede47a2` | 28 theorems | 14 axiom-free; P5 axiom-gated on `hashFn_collision_resistant` (NIST FIPS 180-4) |
| **Wave-5** — AM–GM, Cauchy–Schwarz, conformal coverage, receipt-collision pigeonhole, optional-stopping | [#186](https://github.com/szl-holdings/lutar-lean/pull/186) | `b71114cf` | 11 | 0 new axioms (6 Mathlib-dep CI-green + 5 bare-lean) |
| **Wave-6** — graph substrate: Λ-graph iso-invariance, GNN≤1-WL ceiling, spectral contraction, DAG termination | [#189](https://github.com/szl-holdings/lutar-lean/pull/189) | `dc7ae26d` | 11 | 0 new axioms |
| **Wave-7** — conformal rank-count/p-value, Doob two-sided audit envelope, PAC-Bayes routing envelope, degree-sum iso-invariance | [#190](https://github.com/szl-holdings/lutar-lean/pull/190) | `d6a232ba` | 10 | 0 new axioms |
| **Mathlib-bump C3/C4/C5** — concentration / KL re-exports | [#187](https://github.com/szl-holdings/lutar-lean/pull/187) | — | 3 | re-exports, CI-green |
| **Coder formulas** — code-substrate formula ports | [#193](https://github.com/szl-holdings/lutar-lean/pull/193) | — | — | CI-green |
| **Λ-uniqueness (Set α + Set δ)** — conditional uniqueness within **strengthened** axiom classes | [#192](https://github.com/szl-holdings/lutar-lean/pull/192) | `5f0bb5ee` | 22 results | 3 declared, cited bridge axioms; 10 impostor-deaths axiom-free |

### 2.1 Agentic-loop P1–P6 (PR #188 @ `2ede47a2`) — the system-level proof

| Property | Guarantee | Maturity |
|---|---|---|
| **P1** receipt-completeness | every hop leaves exactly one chained receipt; no silent drop/reorder | PROVEN |
| **P2** gate-soundness | Emit ALLOW ⇔ both policy gate and kernel gate ALLOW; DENY absorbing | PROVEN |
| **P3** non-interference (Goguen–Meseguer) | poisoned/untrusted retrieval **provably cannot** flip a DENY→ALLOW | PROVEN (axiom-free core) |
| **P4** replay-determinism | re-running a recorded run reproduces a byte-identical receipt chain | PROVEN (axiom-free) |
| **P5** tamper-evidence | any single-receipt mutation makes re-verify reject | AXIOM-GATED (`hashFn_collision_resistant`, disclosed) |
| **P6** monotone auditability | an accepted prefix never has to be retracted as the log grows | PROVEN |

---

## 3. Λ — the honest line on uniqueness (Conjecture 1)

Λ is the geometric-mean trust aggregator over four axes (provenance, containment, coherence, convergence). Its uniqueness is **Conjecture 1** — and this page states exactly what was proven and what was not. Source: [`Lutar/Wave6/SetAlphaUniqueness.lean`](https://github.com/szl-holdings/lutar-lean) + [`SetDeltaUniqueness.lean`](https://github.com/szl-holdings/lutar-lean), PR [#192](https://github.com/szl-holdings/lutar-lean/pull/192) @ `5f0bb5ee`.

### What we proved (CI-green)

- **Uniqueness within Set α** = `{A1 symmetry, A2 idempotency, A3 all-strict monotonicity, A4 continuity, A5′ multiplicativity}` — `lambda_unique_setAlpha`, **conditional on one declared, cited bridge axiom** `setAlpha_cauchy`.
- **Uniqueness within Set δ** = `{δ1 reflexivity, δ2 symmetry, δ3 bisymmetry, δ4 per-argument strict monotonicity, δ5′ multiplicativity}` — `geomMean_unique_KS`, continuity derived for free via Kiss–Shulman (2026), **conditional on two declared, cited bridge axioms** `KS_theorem_1_1` + `setDelta_stage2`.
- **Λ-membership and all ten impostor-deaths are AXIOM-FREE** (Lean-core only, no `sorryAx`): AM, HM, PM², max, min each fail A5′ (Set α) or δ4-PSI/δ5′ (Set δ) at a concrete witness — so the discriminator is genuine.

### `#print axioms` — verbatim from the SUCCESS build log @ `5f0bb5ee`

```text
'Lutar.Wave6.SetAlpha.lambda_unique_setAlpha' depends on axioms:
  [propext, Classical.choice, Quot.sound, Lutar.Wave6.SetAlpha.setAlpha_cauchy]
'Lutar.Wave6.SetDelta.geomMean_unique_KS' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   Lutar.Wave6.SetDelta.KS_theorem_1_1, Lutar.Wave6.SetDelta.setDelta_stage2]
'Lutar.Wave6.SetAlpha.maxAgg_not_A5prime'      depends on axioms: [propext, Classical.choice, Quot.sound]  -- impostor death, axiom-free
'Lutar.Wave6.SetDelta.arithmeticMean_not_delta5' depends on axioms: [propext, Classical.choice, Quot.sound]  -- impostor death, axiom-free
```

### What we do **not** claim

- **NOT** unconditional uniqueness under the original weaker axioms A1–A5. That statement is **machine-checked false** — the in-tree counterexample `Round13.maxAgg_ne_Lambda` exhibits an aggregator satisfying A1–A5 that is **not** Λ.
- Λ-uniqueness therefore **stays Conjecture 1**, never a theorem. Strengthening the axiom class (A5 → A5′ multiplicativity, or deriving continuity via Kiss–Shulman) is *how* the conditional results become provable; it does not close the original weaker conjecture.

**Open bounty:** [BOUNTY.md](https://github.com/szl-holdings/lutar-lean/blob/main/BOUNTY.md).

---

## 4. Counts (honest)

| Metric | Value |
|---|---|
| **Locked proven formulas** | **5** — `{F1, F11, F12, F18, F19}` @ `c7c0ba17` |
| Locked kernel | `749` declarations / `14` unique axioms / `163` tracked sorries · `lake build` clean |
| Experimental kernel-verified (CI-green) | wave-5 (11), wave-6 (11), wave-7 (10), agentic-loop (28), Λ-uniqueness Set α+δ (22 results) — **never in the locked count** |
| Λ-uniqueness | **Conjecture 1** — conditional within strengthened classes (CI-green); unconditional uniqueness machine-checked **false** |
| SLSA | Build **L1 + L2** on service images (cosign + `slsa.dev/provenance/v0.2`). **No** L3 / FedRAMP / Iron Bank / CMMC. |

---

## 5. Citations

- Λ axiomatic characterization: Aczél & Saaty (1983), *Procedures for synthesizing ratio judgements*, J. Math. Psych. 27(1):93–102, [doi:10.1016/0022-2496(83)90028-7](https://doi.org/10.1016/0022-2496(83)90028-7); Csató (2018), [arXiv:1706.07256](https://arxiv.org/abs/1706.07256); Kiss & Shulman (2026), Theorem 1.1, [arXiv:2606.05221](https://arxiv.org/abs/2606.05221).
- Loop: Goguen & Meseguer (1982), [doi:10.1109/SP.1982.10014](https://doi.org/10.1109/SP.1982.10014); Merkle (1987); NIST FIPS 180-4.
- DOI lineage: [Zenodo concept DOI 10.5281/zenodo.19944926](https://doi.org/10.5281/zenodo.19944926).

*Proof reports: `team/PROVE_WAVE5..7_REPORT.md`, `team/PROVE_AGENTIC_LOOP_REPORT.md`, `team/LAMBDA_UNIQUENESS_PROOF_REPORT.md`. All commits Signed-off-by Stephen P. Lutar Jr. <stephenlutar2@gmail.com>.*
