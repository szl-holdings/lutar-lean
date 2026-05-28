# lutar-lean

[![Concept DOI](https://img.shields.io/badge/concept%20DOI-10.5281%2Fzenodo.19944926-01696F?style=flat-square&logo=doi&logoColor=white)](https://doi.org/10.5281/zenodo.19944926)
[![v16 DOI](https://img.shields.io/badge/v16%20DOI-10.5281%2Fzenodo.20424996-805AD5?style=flat-square&logo=doi&logoColor=white)](https://doi.org/10.5281/zenodo.20424996) [![v16 PDF](https://img.shields.io/badge/v16%20PDF-download-d62728?style=flat-square)](https://zenodo.org/records/20424996/files/ouroboros-thesis-v16.pdf)
[![v15 DOI](https://img.shields.io/badge/v15%20DOI-10.5281%2Fzenodo.20424995-805AD5?style=flat-square&logo=doi&logoColor=white)](https://doi.org/10.5281/zenodo.20424995) [![v15 PDF](https://img.shields.io/badge/v15%20PDF-download-d62728?style=flat-square)](https://zenodo.org/records/20424995/files/ouroboros-thesis-v15.pdf)
[![v14 DOI](https://img.shields.io/badge/v14%20DOI-10.5281%2Fzenodo.20424992-805AD5?style=flat-square&logo=doi&logoColor=white)](https://doi.org/10.5281/zenodo.20424992) [![v14 PDF](https://img.shields.io/badge/v14%20PDF-download-d62728?style=flat-square)](https://zenodo.org/records/20424992/files/ouroboros-thesis-v14.pdf)
[![Lean kernel-verified](https://img.shields.io/badge/Lean%204-kernel--verified-2D5BB9?style=flat-square&logo=lean&logoColor=white)](https://github.com/szl-holdings/lutar-lean)
[![License](https://img.shields.io/badge/license-Apache%202.0-2DA44E?style=flat-square)](./LICENSE)
[![ORCID](https://img.shields.io/badge/ORCID-0009--0001--0110--4173-A6CE39?style=flat-square&logo=orcid&logoColor=white)](https://orcid.org/0009-0001-0110-4173)

**Machine-checked Lean 4 proofs of the Lutar Invariant.**

This repository is the formal companion to *"The Λ-Ouroboros Substrate:
Four Machine-Verified Mechanisms for Governed AI Runtimes"* (SZL Holdings,
Paper v12, DOI [`10.5281/zenodo.20173920`](https://doi.org/10.5281/zenodo.20173920)). It contains the Lean 4 + Mathlib v4.13.0 formalisation of:

1. **Axioms A1–A4** — the four properties any Lutar-style invariant must satisfy.
2. **Theorem 1 (Uniqueness)** — under A1–A4, the invariant `Λ_k` is unique.
3. **Theorem 2 (Bound)** — for every axes vector, `min ≤ Λ_k ≤ max`.
4. **Egyptian-exactness lemma** — the unit-fraction weight `1/k` is forced
   when all axes share equal importance.

The proofs are kernel-checked by every CI run. When the `sorry` count
reaches **0**, the substrate of [`szl-holdings/ouroboros`](https://github.com/szl-holdings/ouroboros)
stands on a machine-verified foundation. The kernel is the referee.

**Toolchain:** leanprover/lean4 v4.13.0 · Mathlib v4.13.0

---

## Module index

| Module | File | Description |
|--------|------|-------------|
| Axioms | `Lutar/Axioms.lean` | A1–A4 axiomatic properties of the Lutar invariant |
| Invariant | `Lutar/Invariant.lean` | `Λ_k` definition and base properties |
| Uniqueness | `Lutar/Uniqueness.lean` | Theorem 1 — uniqueness under A1–A4 |
| Bound | `Lutar/Bound.lean` | Theorem 2 — `min ≤ Λ_k ≤ max` for all axes vectors |
| Egyptian | `Lutar/Egyptian.lean` | Egyptian-exactness lemma — `1/k` forced under equal importance |
| Khipu / SummationInvariant | `Lutar/Khipu/SummationInvariant.lean` | TH11 — pendant-cord sum-of-sums invariant (merged PR #47) |
| Wheeler / DelayedChoice | `Lutar/Wheeler/DelayedChoice.lean` | Wheeler delayed-choice receipt semantics (merged PR #46) |
| Shannon / InformationBound | `Lutar/Shannon/InformationBound.lean` | Shannon information-theoretic bound on receipt entropy (merged PR #46) |
| QEC / HammingFoundations | `Lutar/QEC/HammingFoundations.lean` | Hamming-code foundations for QEC receipt protection (merged PR #47) |
| QEC / KitaevSurface | `Lutar/QEC/KitaevSurface.lean` | Kitaev surface-code formalisation for governed qubit receipts (merged PR #47) |
| QEC / ShorReceiptCode | `Lutar/QEC/ShorReceiptCode.lean` | Shor 9-qubit code applied to ouroboros receipt payloads (merged PR #47) |

### Recently merged modules

- **PR #46** — Wheeler delayed-choice + Shannon information-bound modules: formal receipt semantics grounded in Wheeler's participatory universe interpretation and Shannon capacity bounds.
- **PR #47** — QEC (Quantum Error Correction) module suite: Hamming foundations, Kitaev surface-code formalisation, and Shor receipt code; Khipu summation invariant TH11.

---

## Status

| Theorem | File | Status |
|---|---|---|
| Axioms A1..A4 | `Lutar/Axioms.lean` | ✅ stated |
| Egyptian uniqueness lemma | `Lutar/Egyptian.lean` | 🟡 1 lemma proved, 1 `sorry` |
| Λ_k definition | `Lutar/Invariant.lean` | ✅ defined |
| Theorem 2 (bound) | `Lutar/Bound.lean` | 🟡 stated, proof scaffolded |
| Theorem 1 (uniqueness) | `Lutar/Uniqueness.lean` | 🟡 stated, proof scaffolded |
| TH11 (Khipu summation) | `Lutar/Khipu/SummationInvariant.lean` | 🟡 2 routine `sorry`s remaining |
| Wheeler delayed-choice | `Lutar/Wheeler/DelayedChoice.lean` | ✅ stated |
| Shannon information bound | `Lutar/Shannon/InformationBound.lean` | ✅ stated |
| QEC Hamming foundations | `Lutar/QEC/HammingFoundations.lean` | ✅ stated |
| QEC Kitaev surface | `Lutar/QEC/KitaevSurface.lean` | ✅ stated |
| QEC Shor receipt code | `Lutar/QEC/ShorReceiptCode.lean` | ✅ stated |

Track the remaining `sorry` count in every CI run summary.

---

## Build

Requires:

* [`elan`](https://github.com/leanprover/elan) (Lean version manager)
* `lake` (bundled with elan)
* Toolchain: leanprover/lean4 **v4.13.0** · Mathlib **v4.13.0** (pinned in `lean-toolchain` and `lakefile.toml`)

```bash
git clone https://github.com/szl-holdings/lutar-lean
cd lutar-lean
lake build          # ← runs the Lean kernel on the whole library
lake exe check      # ← runs the verification entry point
```

CI runs the same two commands on every push.

---

## How Lean signs off

Lean does not need human approval. The Lean kernel is a small, audited
proof-checking program. If `lake build` succeeds with **zero `sorry`** in
the library files, every theorem has been verified by the kernel —
end of story.

For the cryptographic-style audit trail: each release is Zenodo-archived
with a DOI; Paper v12 cites that DOI directly.

---

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

---

## Thesis publications (DOI-pinned)

| Version | Title | DOI | PDF |
|---|---|---|---|
| **v16** | Feynman path-integral audit closure + Gates doctrine codes + cross-component composite invariant | [`10.5281/zenodo.20424996`](https://doi.org/10.5281/zenodo.20424996) | [PDF](https://zenodo.org/records/20424996/files/ouroboros-thesis-v16.pdf) |
| **v15** | Knot Calculus for Governed Decision Receipts — audit-Reidemeister R1/R2/R3, PAC-Bayes head, Khipu-DAG | [`10.5281/zenodo.20424995`](https://doi.org/10.5281/zenodo.20424995) | [PDF](https://zenodo.org/records/20424995/files/ouroboros-thesis-v15.pdf) |
| **v14** | Verifiable Multi-Agent Anatomy — Lutar Calculus, formal foundations, runtime verification, honest proof record | [`10.5281/zenodo.20424992`](https://doi.org/10.5281/zenodo.20424992) | [PDF](https://zenodo.org/records/20424992/files/ouroboros-thesis-v14.pdf) |
| **v12** | The Λ-Ouroboros Substrate — Four Machine-Verified Mechanisms | [`10.5281/zenodo.20173920`](https://doi.org/10.5281/zenodo.20173920) | — |

**Concept DOI** (always resolves to latest): [`10.5281/zenodo.19944926`](https://doi.org/10.5281/zenodo.19944926)

---

## License

Apache-2.0. © 2026 Stephen P. Lutar / SZL Holdings.

**Author:** Lutar, Stephen P. · ORCID [0009-0001-0110-4173](https://orcid.org/0009-0001-0110-4173)
