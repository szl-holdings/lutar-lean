# lutar-lean

**Machine-checked Lean 4 proofs of the Lutar Invariant.**

[![CI](https://github.com/szl-holdings/lutar-lean/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/szl-holdings/lutar-lean/actions/workflows/lean.yml)
[![CodeQL](https://github.com/szl-holdings/lutar-lean/actions/workflows/codeql.yml/badge.svg?branch=main)](https://github.com/szl-holdings/lutar-lean/actions/workflows/codeql.yml)
[![OpenSSF Scorecard](https://api.securityscorecards.dev/projects/github.com/szl-holdings/lutar-lean/badge)](https://securityscorecards.dev/viewer/?uri=github.com/szl-holdings/lutar-lean)
[![License](https://img.shields.io/badge/license-Apache--2.0-2DA44E?style=flat-square)](./LICENSE)


This repository is the formal companion to *“The Λ-Ouroboros Substrate:
Four Machine-Verified Mechanisms for Governed AI Runtimes”* (SZL Holdings,
Paper v12). It contains the Lean 4 + Mathlib formalisation of:

1. **Axioms A1–A4** — the four properties any Lutar-style invariant must satisfy.
2. **Theorem 1 (Uniqueness)** — under A1–A4, the invariant `Λ_k` is unique.
3. **Theorem 2 (Bound)** — for every axes vector, `min ≤ Λ_k ≤ max`.
4. **Egyptian-exactness lemma** — the unit-fraction weight `1/k` is forced
   when all axes share equal importance.

The proofs are kernel-checked by every CI run. When the `sorry` count
reaches **0**, the substrate of [`szl-holdings/ouroboros`](https://github.com/szl-holdings/ouroboros)
stands on a machine-verified foundation. The kernel is the referee.

## Status

| Theorem | File | Status |
|---|---|---|
| Axioms A1..A4 | `Lutar/Axioms.lean` | ✅ stated |
| Egyptian uniqueness lemma | `Lutar/Egyptian.lean` | 🟡 1 lemma proved, 1 `sorry` |
| Λ_k definition | `Lutar/Invariant.lean` | ✅ defined |
| Theorem 2 (bound) | `Lutar/Bound.lean` | 🟡 stated, proof scaffolded |
| Theorem 1 (uniqueness) | `Lutar/Uniqueness.lean` | 🟡 stated, proof scaffolded |

Track the remaining `sorry` count in every CI run summary.

## Build

Requires:

* [`elan`](https://github.com/leanprover/elan) (Lean version manager)
* `lake` (bundled with elan)

```bash
git clone https://github.com/szl-holdings/lutar-lean
cd lutar-lean
lake build          # ← runs the Lean kernel on the whole library
lake exe check      # ← runs the verification entry point
```

CI runs the same two commands on every push.

## How Lean signs off

Lean does not need human approval. The Lean kernel is a small, audited
proof-checking program. If `lake build` succeeds with **zero `sorry`** in
the library files, every theorem has been verified by the kernel —
end of story.

For the cryptographic-style audit trail: each release is Zenodo-archived
with a DOI; Paper v12 cites that DOI directly.

## Companion benchmarks

Empirical performance of the four substrate mechanisms (Λ-gate, receipt
chain, Bekenstein cascade, dual-witness verdict) is measured by
[`packages/ouroboros-integrations/bench/the-four.bench.ts`](https://github.com/szl-holdings/ouroboros/tree/main/packages/ouroboros-integrations/bench)
in the `szl-holdings/ouroboros` monorepo.

Representative numbers (N = 10,000 each, Node 24, Linux x86_64):

| Mechanism | p50 | p99 | Headline |
|---|---|---|---|
| **I — Λ₉ gate** | 3.9 µs | 26 µs | bound holds 100% · admits 100% clean / 21% noisy |
| **II — Receipt chain** | 69 µs | 190 µs | 7,054 receipts/sec · 100% chain-verifiable |
| **III — Bekenstein gate** | 0.07 µs | 0.25 µs | fires 38.3% in tight regime |
| **IV — Dual-witness** | 0.09 µs | 0.29 µs | 100% MATCH clean · 100% DIVERGE adversarial |

Composed: **Λ-gate reduces downstream error rate by 45.2%** on the
synthetic-noisy mixed workload.

## License

Apache-2.0. © 2026 Stephen P. Lutar Jr. / SZL Holdings.
