# PROVE-WAVE-3 REPORT — Lean 4 + Mathlib formalization of C1–C20

**Engineer:** Lean proof subagent (SZL Holdings)
**Date:** 2026-06-06
**Toolchain:** Lean 4.13.0 (commit 6d22e0e5cc5a, Release), `~/.elan/bin/lean`.
**Verification policy (honesty doctrine):**
- **Mathlib-FREE** proofs were compiled and **bare-`lean` verified sorry-free in this
  sandbox** (0 errors), with a verbatim `#print axioms` ledger (below).
- **Mathlib-DEPENDENT** proofs (Tier 1 instantiations) are **NOT compilable in the
  sandbox** (Mathlib needs ~6 GB; only 4.4 GB free) and are submitted for
  verification by lutar-lean CI (`lake-build.yml` / `Lean kernel check`). They are
  reported as **CI-PENDING** and are NOT claimed "compiled" until CI is green.
- **Λ (F23) stays Conjecture 1.** C7 (Aczél/A6) is conditional on the **declared**
  axiom `A6_bisymmetric` only; unconditional Λ uniqueness is FALSE under A1–A5
  (machine-checked `maxAgg_ne_Lambda`). Never reported as an unconditional theorem.
- **Locked kernel (749/14/163 @ c7c0ba17, Doctrine v11) is UNCHANGED.** All Wave-3
  work lives in an **experimental/wave3 scope** (`Lutar/Wave3/*`) that is
  counter-excluded from the locked count.

---

## 1. Commits

| Repo | Commit SHA | Contents |
|---|---|---|
| `szl-holdings/lutar-lean` | **`775093f0f8ef7f530272c38d513c28fdaec3366b`** | added 4 files `Lutar/Wave3/{Consensus,MerkleKraft,InfoEstim,Tier1Mathlib}.lean` |
| `szl-holdings/lutar-lean` | `f01a5914063164c949be6ca2745e2995ffa48a90` | wired all 4 `Lutar/Wave3/*` into `Lutar.lean` lib root — **SUPERSEDED** (Tier1Mathlib import broke the strict `Lean kernel check` since Mathlib-dep modules can't be built without the import; reverted below) |
| `szl-holdings/lutar-lean` | **`02e44c30657c9986475ff7373113728f4ba38f67`** (CURRENT HEAD) | root fix: removed `import Lutar.Wave3.Tier1Mathlib` from root, kept the 3 bare-lean-verified Mathlib-FREE modules (Consensus, MerkleKraft, InfoEstim) wired in. **CI VERIFIED GREEN** (see §1a). |
| `szl-holdings/a11oy` | **`3d12344dc8471602dcd827f3236a51a4b6972b29`** | `packages/a11oy-knowledge/src/knowledge.json` proof_summary + wave3 block |

### 1a. CI verification (authoritative — `gh run list` on HEAD `02e44c30`)

| Check | HEAD `02e44c30` | wave2 baseline `655c1f18` | Verdict |
|---|---|---|---|
| **Lean kernel check** (full Mathlib build — the authoritative verifier) | **success** ✅ | success | GREEN — wave3 Mathlib-free modules kernel-verified |
| `CI` / `Doctrine` / `Tests` / `DCO` / `gitleaks` / `SBOM` / `CodeQL` / `Trivy+Grype` / `OpenSSF Scorecard` | all success ✅ | — | GREEN |
| `Lake build (gate + numbers)` | failure | **failure** (same) | PRE-EXISTING red on wave2 baseline — NOT caused by Wave-3 |
| `huklla-t11-doi-title-gate` | failure (exit 28, network timeout) | **failure** (same) | PRE-EXISTING red on wave2 baseline — NOT caused by Wave-3 |

HEAD `02e44c30` reproduces the EXACT CI signature of the clean wave2 baseline
`655c1f18`: **Lean kernel check green**, the two pre-existing reds unchanged. This
proves the Wave-3 Mathlib-free additions (C8–C14b, C9/C17/C20 fragments) are
kernel-verified and broke nothing. The C1/C2/C6 Mathlib re-exports remain present
as a file (`Tier1Mathlib.lean`, commit `775093f0`) but are deliberately **NOT wired
into the lib root** — they are Mathlib-dependent and could not be independently
CI-verified in the current lakefile configuration, so per the honesty doctrine they
stay **CI-PENDING / NOT claimed compiled**.

C7 (Aczél/A6 conditional Λ uniqueness) was already delivered in **WAVE 2**
(`Lutar/Puriq/Formulas/F23_Uniqueness.lean`, commit `655c1f18…`): `lambda_unique_under_A6`
gated on the declared `A6_bisymmetric`, re-exporting the in-tree (fully proved)
`lambda_unique_of_factors`. It is cited here, not duplicated.

---

## 2. Per-candidate table

Maturity legend: **proven** = sorry-free, Lean-core axioms only (propext / Quot.sound
/ Classical.choice); **axiom-gated** = sorry-free given a DECLARED idealization;
**CI-pending** = Mathlib-dependent, awaiting CI; **conjectured** = not a theorem.

| ID | Statement (Lean theorem) | Proved sorry-free? | Mathlib-dep/free | Maturity | Commit | Substrate use |
|---|---|---|---|---|---|---|
| **C1** | Tsirelson 2√2 — `c1_lutar_omega_tsirelson_ceiling` (re-export `tsirelson_inequality`); `c1a_tsirelson_constant` √2³=2√2 | yes (re-export) | Mathlib-dep | **CI-pending** | `775093f0` | Lutar-Omega EPR–Bell diagnostic (operator ceiling) |
| **C2** | CHSH ≤ 2 — `c2_lutar_omega_classical_ceiling` (re-export `CHSH_inequality_of_comm`) | yes (re-export) | Mathlib-dep | **CI-pending** | `775093f0` | Lutar-Omega classical ceiling (2 vs 2√2 separation) |
| **C3** | Hoeffding (sub-Gaussian sums) | — | Mathlib (`Probability.Moments.SubGaussian`) | **available, not instantiated** | — | trust scoring / receipt sampling concentration |
| **C4** | Azuma–Hoeffding (martingale) | — | Mathlib (`Probability.Moments.SubGaussian`) | **available, not instantiated** | — | streaming/online trust drift |
| **C5** | Gibbs / KL ≥ 0 | — | Mathlib (`InformationTheory.KullbackLeibler`) | **available, not instantiated** | — | active-inference free-energy core |
| **C6** | Jensen (convex) — `c6_jensen_forecaster` (re-export `ConvexOn.map_sum_le`) | yes (re-export) | Mathlib-dep | **CI-pending** | `775093f0` | honestly-conservative forecaster (ELBO direction) |
| **C7** | Aczél bisymmetry ⇒ Λ uniqueness — `lambda_unique_under_A6` | yes, **CONDITIONAL on declared A6** | Mathlib-dep | **axiom-gated (A6); Λ still Conjecture 1** | `655c1f18` (wave2) | Λ aggregator — the honest A6 route |
| **C8** | Kraft inequality — `c8_kraft_equality_doctrine`, `c8a_kraft_sub_code`, `c8b_kraft_mixed_lengths` | **yes (bare-lean)** | Mathlib-free | **proven** | `775093f0` | audit doctrine (receipt-length budget) |
| **C9** | Shannon L ≥ H (doctrine tight case) — `c9_shannon_tight`, `c9a_no_undershoot`, `c9b_entropy_value` | **yes (bare-lean)** | Mathlib-free | **proven (fragment)** | `775093f0` | audit doctrine (receipt info lower bound) |
| **C10** | Byzantine 3f+1 — `c10_threeFPlusOne`, `c10a_quorum_intersection`, `c10b_honest_majority`, `c10c_infeasible_at_3f` | **yes (bare-lean)** | Mathlib-free | **proven** | `775093f0` | a11oy consensus quorum sizing (n≥3f+1, 2f+1 intersection) |
| **C11** | DLS partial-synchrony f<n/3 — `c11_dls_threshold`, `c11a_three_groups` | **yes (bare-lean)** | Mathlib-free | **proven** | `775093f0` | a11oy consensus under partial synchrony |
| **C12** | FLP (statement + bivalence core) — `c12a_bivalent_xor_univalent`, `c12b_no_decision_from_bivalent` | **yes (bare-lean), partial** | Mathlib-free | **proven (core; full FLP NOT claimed)** | `775093f0` | consensus liveness honesty bound |
| **C13** | Merkle–Damgård CR preservation — `c13_md_step_cr`, `c13a_md_append_cr` | **yes (bare-lean)** | Mathlib-free | **axiom-gated** (`compression_collision_resistant`) | `775093f0` | receipts / hash-chain (F13′ upgrade) |
| **C14** | Merkle-tree CR binding — `c14_merkle_binding` | **yes (bare-lean)** | Mathlib-free | **axiom-gated** (`node`/`leaf_collision_resistant`, `domain_separation`) | `775093f0` | receipts-Merkle binding (F15 upgrade) |
| **C14b** | Domain separation blocks 2nd-preimage — `c14b_no_second_preimage` | **yes (bare-lean)** | Mathlib-free | **axiom-gated** (only `domain_separation` tag — structural, no hardness) | `775093f0` | Merkle second-preimage defense |
| **C15** | McDiarmid bounded-differences | — | Mathlib (port arXiv:2503.19605) | **available, not ported** | — | trust scoring stability / generalization |
| **C16** | PAC-Bayes (McAllester) | — | Mathlib-provable (hard) | **not attempted** | — | Sim2Real learned-trust generalization |
| **C17** | Gauss–Markov / BLUE (variance-decomp core) — `c17_blue_min_variance`, `c17a_blue_equality` | **yes (bare-lean), scalar core** | Mathlib-free | **proven (fragment; full matrix-PSD = CI target)** | `775093f0` | killinchu track fusion (min-variance linear fuser) |
| **C18** | Arrow impossibility | — | LEAN-EXISTS (Souther–Davidson / TCSlib) | **available, not ported** | — | preference-aggregation honesty bound |
| **C19** | Gibbard–Satterthwaite | — | Mathlib-provable (hard) | **not attempted** | — | consensus truthfulness (complements VCG) |
| **C20** | Softmax 1/2-Lipschitz (order-preservation core) — `c20_argmax_stable`, `c20a_translation_invariant`, `c20b_robust_margin` | **yes (bare-lean), order core** | Mathlib-free | **proven (fragment; tight 1/2 in every ℓₚ = CI target)** | `775093f0` | retrieval / sparse-attention stability |

---

## 3. Verbatim `#print axioms` ledger (Mathlib-FREE, bare-`lean` 4.13.0)

```
-- Consensus (C10/C11/C12) — Lean-core only, NO non-core axioms
Wave3.Consensus.c10_threeFPlusOne             does not depend on any axioms
Wave3.Consensus.c10a_quorum_intersection      [propext, Quot.sound]
Wave3.Consensus.c10b_honest_majority          [propext, Classical.choice, Quot.sound]
Wave3.Consensus.c10c_infeasible_at_3f         [propext, Quot.sound]
Wave3.Consensus.c11_dls_threshold             [propext, Classical.choice, Quot.sound]
Wave3.Consensus.c11a_three_groups             [propext, Quot.sound]
Wave3.Consensus.c12a_bivalent_xor_univalent   does not depend on any axioms
Wave3.Consensus.c12b_no_decision_from_bivalent does not depend on any axioms

-- MerkleKraft — C8 pure; C13/C14 AXIOM-GATED on DECLARED idealizations
Wave3.MerkleKraft.c8_kraft_equality_doctrine  does not depend on any axioms
Wave3.MerkleKraft.c8a_kraft_sub_code          does not depend on any axioms
Wave3.MerkleKraft.c8b_kraft_mixed_lengths     does not depend on any axioms
Wave3.MerkleKraft.c13_md_step_cr              [Wave3.MerkleKraft.compression_collision_resistant]
Wave3.MerkleKraft.c13a_md_append_cr           [propext, Wave3.MerkleKraft.compression_collision_resistant]
Wave3.MerkleKraft.c14_merkle_binding          [Wave3.MerkleKraft.domain_separation,
                                               Wave3.MerkleKraft.leaf_collision_resistant,
                                               Wave3.MerkleKraft.node_collision_resistant]
Wave3.MerkleKraft.c14b_no_second_preimage     [Wave3.MerkleKraft.domain_separation]

-- InfoEstim — C9/C17/C20 cores, Lean-core only
Wave3.InfoEstim.c9_shannon_tight              does not depend on any axioms
Wave3.InfoEstim.c9a_no_undershoot             does not depend on any axioms
Wave3.InfoEstim.c9b_entropy_value             does not depend on any axioms
Wave3.InfoEstim.c17_blue_min_variance         [propext, Quot.sound]
Wave3.InfoEstim.c17a_blue_equality            [propext, Classical.choice, Quot.sound]
Wave3.InfoEstim.c20_argmax_stable             does not depend on any axioms
Wave3.InfoEstim.c20a_translation_invariant    [propext, Quot.sound]
Wave3.InfoEstim.c20b_robust_margin            [propext, Quot.sound]
```

**No `sorryAx` appears anywhere.** The only non-core axioms are the FOUR declared
Merkle idealizations (`compression_collision_resistant`, `node_collision_resistant`,
`leaf_collision_resistant`, `domain_separation`) — injective-oracle abstractions,
NOT proofs of cryptographic hardness, disclosed exactly like the existing kernel
crypto axioms (`hash_collision_resistant`, `ecdsa_unforgeable`, `h2_collision_resistant`).

Raw output saved to `team/proof_work/wave3/axiom_audit_wave3_mathlibfree.txt`.

### C7 / A6 ledger (already shipped wave2, CI-verified)
`lambda_unique_under_A6` `#print axioms` lists `A6_bisymmetric` as a DECLARED,
non-core axiom (Kolmogorov–Nagumo–Aczél bisymmetry). Λ uniqueness is therefore
**conditional on A6**; unconditionally it is FALSE (`maxAgg_ne_Lambda`), so F23
remains **Conjecture 1**.

---

## 4. HONEST COUNTS (Wave 3)

### (a) NEW sorry-free, Lean-core axioms only — bare-`lean` VERIFIED
> **19 theorems** across C8 (3), C9 (3), C10 (4), C11 (2), C12 (2), C17 (2), C20 (3).
Several of these (C9, C12, C17, C20) are explicitly the **Mathlib-free FRAGMENT** of
the full result (tight case / core lemma), labeled as such in every docstring — they
are honest partial formalizations, not claims of the full real-analytic theorem.

A conservative "substantive, non-trivial" subset (excluding the most `decide`-trivial
arithmetic envelopes): **C10a/b/c quorum theory, C11 DLS threshold, C12 bivalence
dichotomy, C13/C14 Merkle reductions, C8 Kraft** ≈ 10–12 hard theorems.

### (b) NEW axiom-gated (DECLARED idealizations) — bare-`lean` VERIFIED
> **4 theorems**: C13 (`c13_md_step_cr`, `c13a_md_append_cr` → `compression_collision_resistant`),
> C14 (`c14_merkle_binding` → node/leaf CR + `domain_separation`), C14b
> (`c14b_no_second_preimage` → `domain_separation` tag only, structural).

### (c) CI-pending (Mathlib-dependent, NOT yet verified)
> **3 theorems**: C1 (`c1_*`), C2 (`c2_*`), C6 (`c6_jensen_forecaster`) — direct
> re-exports of `tsirelson_inequality`, `CHSH_inequality_of_comm`, `ConvexOn.map_sum_le`.
> Reported as CI-pending. They live in `Tier1Mathlib.lean` (commit `775093f0`) but
> are NOT wired into the lib root (current HEAD `02e44c30`), so the green `Lean
> kernel check` does NOT cover them. To promote them to `proven (Mathlib-dep)` a
> separate Mathlib-enabled lake target must build the file and go green; until then
> they stay CI-pending per the honesty doctrine.

### (d) Λ / F23
> **F23 = Conjecture 1.** NOT a theorem. C7 gives only the CONDITIONAL
> `lambda_unique_under_A6` under the DECLARED `A6_bisymmetric`. Unconditional
> uniqueness is FALSE under A1–A5 (`maxAgg_ne_Lambda`). UNCHANGED from wave2.

### (e) Locked kernel
> **749/14/163 @ c7c0ba17 (Doctrine v11) — UNCHANGED.** locked_proven stays the
> wave2-recorded distinct {F1,F11,F12,F18,F19}=5. All Wave-3 work is experimental.

**Headline:** **+19 sorry-free (Lean-core only, bare-lean verified), +4 axiom-gated
(declared idealizations), 3 Mathlib re-exports CI-pending, Λ still Conjecture 1.**

---

## 5. F1–F23 PURIQ pack revisit

The full F1–F23 pack was formalized, doctrined, and committed in **WAVE 2**
(`PuriqFormulaLean.WAVE2.lean`, `ProvedFormulas.lean`, `F23_Uniqueness.lean`),
bare-`lean` verified: **21 sorry-free** (F1–F22 excl. F23, incl. the additive
scaffolding F12/F19 with caveats), **3 axiom-gated** (F13′/F14/F15′), **F23 =
Conjecture 1**. Wave-3 status:

- **F6 (LMDB WAL durability), F8 (OSS-only voice safety), F9 (advisory
  non-interference), F16 (immune cross-cut completeness)** — the spec flagged these
  as "stay open if not closable." They were in fact **closed sorry-free in wave2**
  (`f6_lmdb_durability [propext,Quot.sound]`, `f8_wallpa_oss_only`/`f8_no_human_clone`
  no axioms, `f9_wasi_rikuq_noninterference` no axioms, `f16_sentra_immune_complete
  [propext]`) — verified in the wave2 `#print axioms` ledger. No honesty issue; they
  are genuine, substantive sorry-free proofs. They are NOT re-opened.
- **F23** stays Conjecture 1 (see §3 C7 ledger). The conditional theorem
  `lambda_unique_of_factors` is proved; uniqueness closes only under declared A6.
- No new sorries were closed or opened in F1–F23 during wave 3 (the pack was already
  at its honest ceiling); wave-3 effort went to the NEW C-candidate theorems.

---

## 6. knowledge.json update (a11oy)

Added a `proof_summary.wave3` block recording the new proven / axiom-gated /
CI-pending theorems with maturity labels, the verbatim axiom ledger summary, the
commit SHAs, and the substrate mapping. **`locked_proven` stays 5**;
**`conjecture` stays `["F23"]`**; F23 maturity stays `conjectured`. Committed to
`szl-holdings/a11oy` (SHA in final summary).

---

## 7. Honesty statement

Every Mathlib-free theorem in this report was compiled sorry-free under bare `lean`
4.13.0 (0 errors) and its axiom dependencies disclosed verbatim above; the only
non-core axioms are four explicitly-DECLARED Merkle idealizations. The three
Mathlib-dependent re-exports are honestly marked CI-PENDING and are NOT claimed to
compile until the lutar-lean CI is green. Λ (F23) is Conjecture 1, neither closed
nor faked; C7 is conditional on a declared, disclosed bisymmetry axiom A6. The
locked kernel count (749/14/163 @ c7c0ba17) is unchanged; all Wave-3 work is in a
separate experimental scope.
