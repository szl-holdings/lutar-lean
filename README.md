<div align="center">

# λ &nbsp;lutar-lean

### The formal-methods spine of the SZL governance substrate

**Machine-checked Lean 4 + Mathlib proofs for the Λ trust aggregator, the audit-fiber invariants, and the receipt/consensus theorems that every SZL runtime claim depends on.**

[![Lake build](https://github.com/szl-holdings/lutar-lean/actions/workflows/lake-build.yml/badge.svg?branch=main)](https://github.com/szl-holdings/lutar-lean/actions/workflows/lake-build.yml)
[![CI](https://github.com/szl-holdings/lutar-lean/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/szl-holdings/lutar-lean/actions/workflows/ci.yml)
[![DCO](https://github.com/szl-holdings/lutar-lean/actions/workflows/dco.yml/badge.svg?branch=main)](https://github.com/szl-holdings/lutar-lean/actions/workflows/dco.yml)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-0B1F3A.svg?style=flat-square&logo=apache&logoColor=white)](./LICENSE)
[![Lean 4](https://img.shields.io/badge/Lean-4%20%2B%20Mathlib-2C2C54.svg?style=flat-square)](https://leanprover.github.io/)
[![SLSA L1 honest · L2 roadmap](https://img.shields.io/badge/SLSA-L1_honest_%C2%B7_L2_roadmap-22c55e.svg?style=flat-square)](https://slsa.dev/spec/v1.0/levels)
[![Λ = Conjecture 1](https://img.shields.io/badge/%CE%9B-Conjecture_1-b3541e.svg?style=flat-square)](./BOUNTY.md)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20434308.svg)](https://doi.org/10.5281/zenodo.20434308)

[Org](https://github.com/szl-holdings) · [Thesis (szl-papers)](https://github.com/szl-holdings/szl-papers) · [Λ bounty](./BOUNTY.md) · [🤗 SZLHOLDINGS](https://huggingface.co/SZLHOLDINGS)

`receipts.in ≡ receipts.out`

</div>

---

## What this is

**lutar-lean** is the Lean 4 library that formally underwrites SZL's governance math. It defines the **Λ aggregator** (a geometric-mean trust score over four axes — provenance, containment, coherence, convergence), states the axiom system `LutarAxioms` (A1–A5), and machine-checks the theorems that the runtime relies on: aggregator bounds, monotonicity, permutation-invariance, hash-chain tamper-evidence, conformal coverage, and quorum agreement.

It is the **single source of truth** for every "proven" claim made anywhere in the SZL ecosystem. If a property is asserted in the apps, the papers, or the marketing, it is either (a) proven here and labeled *locked*, (b) proven here under explicit hypotheses and labeled *experimental / conditional*, or (c) honestly labeled a **conjecture**. Nothing is overstated.

---

## Proof status — read this before citing anything

SZL runs a strict **two-tier** honesty doctrine. The two tiers never blend.

### Tier 1 — LOCKED (proven, sorry-free, count machine-enforced)

> **Exactly 5 formulas are locked-proven: `F1, F11, F12, F18, F19`.**

They are zero-`sorry`, use only Lean-core axioms `[propext, Classical.choice, Quot.sound]`, and the fact that there are **exactly 5** is *itself* a Lean theorem (`Lutar.Wave8.AxiomDisclosure.locked_count_five`, which depends on **no** axioms). The locked set cannot silently grow.

### Tier 2 — EXPERIMENTAL · CI-green (kernel-verified, labeled, never in the locked count)

> The experimental library on `main` type-checks at **1323 declarations / 23 axioms (22 unique), CI-green** on Lean `v4.18.0` (`lake build + numbers` ✅, DCO ✅).

These are real, kernel-verified theorems — waves 5/6/7/8, the agentic loop P1–P6, the airtight-Λ conditional results, and the [Wave-13 sweep](https://github.com/szl-holdings/lutar-lean) — but they are an explicitly separate **EXPERIMENTAL · CI-green** tier and are **never** folded into the locked-5.

### The Λ line — Conjecture 1 (do not misquote this)

| Claim | Status |
|---|---|
| Λ satisfies A1–A5 | **Proven** (`lambda_satisfiesAxioms_round13`), sorry-free |
| Λ uniqueness, **unconditional** under A1–A5 | **Machine-checked FALSE** (`Round13.maxAgg_ne_Lambda`: `maxAgg` and `min` satisfy A1–A5 and are not Λ) — stays **Conjecture 1** |
| Λ uniqueness, **conditional** (CUT-2, axiom-free) | **Proven**: any A1–A5 aggregator with multiplicative, separable per-axis slices equals Λ (`lambda_unique_of_separable`), reducing to the in-tree `multiplicative_monotone_isPow_pos` + `lambda_unique_of_factors` with **no new axiom token** |
| Λ uniqueness, **conditional** (Set α / Set δ) | **Proven** under explicitly declared, cited bridge axioms ([PR #192](https://github.com/szl-holdings/lutar-lean/pull/192)) |
| Byzantine BFT safety (equivocating organ) | **Khipu Conjecture 2 — open.** The Wave-13 `quorum_agreement_single_valued_vote` is an honestly-labeled *non-Byzantine shadow* (single-valued `voteOf`); the real `ubuntu_quorum_safety` obligation is left untouched. |

> **Bottom line:** Λ is **Conjecture 1**. We have a *proven, axiom-free conditional* core (CUT-2) and *proven conditional* variants — but **never** an unconditional uniqueness theorem, because that statement is false. Open prize: [BOUNTY.md](./BOUNTY.md).

Full proof table with verbatim `#print axioms`, run IDs, and per-result maturity → **[PROVEN_FORMULAS.md](./PROVEN_FORMULAS.md)**.

---

## Architecture

```
Lutar/
├── Axioms.lean              -- LutarAxioms A1–A5 (monotone, 1-homogeneous,
│                               diagonal-normalized, bounded-by-max, symmetric)
├── Puriq/Formulas/
│   └── PuriqFormulaLean.lean -- the 5 LOCKED formula theorems {F1,F11,F12,F18,F19}
├── Round13/                 -- Λ-uniqueness machinery (Cauchy/Aczél, CUT-2 conditional)
│   ├── CauchyND_Closure.lean   -- monotone+additive ⇒ linear (rational squeeze, 0 sorry)
│   └── Lambda_Uniqueness.lean  -- maxAgg_ne_Lambda counterexample (Conjecture-1 anchor)
├── Wave8/AxiomDisclosure.lean  -- locked_count_five (no-axiom theorem: exactly 5 locked)
├── Wave13/Sweep.lean        -- experimental: quorum shadow + HM bottleneck (CI-green)
├── Khipu/                   -- receipt summation invariants, hash-chain tamper-evidence
├── Innovations/round*/      -- experimental frontier formulas (labeled, gated)
└── Putnam/                  -- hard analysis obligations (honest sorries, references intact)
```

**How it fits the ecosystem:** the proofs here are *enforced* at runtime by the receipt layer — the runtime emits DSSE-signed receipts over a SHA-256 hash chain, stored append-only in [`szl-lake`](https://github.com/szl-holdings/szl-lake), witnessed by [`khipu-consensus`](https://github.com/szl-holdings/khipu-consensus), and surfaced for offline verification in [`szl-trust`](https://github.com/szl-holdings/szl-trust). The bounded-recursion runtime that consumes them lives in [`ouroboros`](https://github.com/szl-holdings/ouroboros). The live kernel browser is [`lean-kernel`](https://github.com/szl-holdings/lean-kernel); the open prize for unconditional Λ is [`lambda-bounty`](https://github.com/szl-holdings/lambda-bounty).

---

## Quickstart

```bash
git clone https://github.com/szl-holdings/lutar-lean
cd lutar-lean
lake exe cache get      # fetch the Mathlib olean cache
lake build              # type-checks the whole library (CI-green on main)
```

Inspect the honest proof posture of any declaration:

```bash
# the locked count is itself a no-axiom theorem
echo '#print axioms Lutar.Wave8.AxiomDisclosure.locked_count_five' | lake env lean --stdin
# the Conjecture-1 counterexample
echo '#print axioms Lutar.Round13.maxAgg_ne_Lambda' | lake env lean --stdin
```

---

## Honest disclosures

- **Open `sorry`s are tracked, not hidden.** Putnam analysis, the xoshiro period bound (GF(2)²⁵⁶ companion-matrix primitivity), Hoeffding–Azuma assembly, Reed–Solomon Singleton, and the Brouwer/cohomology obligations are genuinely hard (multi-day to multi-week or need Mathlib facts absent at v4.18.0). They stay honest `sorry`s with their references intact.
- **Declared axioms are honest assumptions**, not proofs: cryptographic-hardness axioms (SHA-256 collision-resistance, domain separation), the Λ-family bridge axioms, and deep-math axioms (Gleason, Reidemeister, Liu-Hui) are disclosed and isolated. `#print axioms` is the source of truth.
- **No fabricated metrics. No inflated proof counts.** The locked count is exactly 5 and machine-enforced; the experimental count is reported separately and CI-measured.

---

## Lineage

Mathematical patterns trace to durable, scholarly-documented sources (Rhind Papyrus false position, Inka khipu summation, Liu Hui polygon π, Madhava series-remainder bounds, Cauchy–Aczél functional equations). Ancient sources *inspire* verifiable patterns — no secret-decoding claims, no mystical language (Doctrine v11 boundary).

## License & citation

[Apache-2.0](./LICENSE) — SZL Holdings. ORCID [0009-0001-0110-4173](https://orcid.org/0009-0001-0110-4173).

```
S. P. Lutar Jr., "lutar-lean — Lean 4 Formal Proofs for the SZL Governance Substrate,"
Zenodo, DOI 10.5281/zenodo.20434308, 2026.
```
