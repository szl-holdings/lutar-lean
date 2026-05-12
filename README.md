# lutar-lean

**Machine-checked Lean 4 proofs of the Lutar Invariant.**

[![Lean 4](https://img.shields.io/badge/Lean-4-2D5BB9?style=flat-square&logo=lean&logoColor=white)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/Mathlib-required-1F3B73?style=flat-square)](https://github.com/leanprover-community/mathlib4)
[![Thesis v11](https://img.shields.io/badge/thesis%20v11-10.5281%2Fzenodo.20119582-1f78b4?style=flat-square)](https://doi.org/10.5281/zenodo.20119582)
[![Concept DOI](https://img.shields.io/badge/Concept%20DOI-10.5281%2Fzenodo.19944926-1f78b4?style=flat-square)](https://doi.org/10.5281/zenodo.19944926)
[![Runtime parity](https://img.shields.io/badge/runtime%20parity-bit--exact%20across%203%20runtimes-2DA44E?style=flat-square)](#reference-vector-parity)
[![License](https://img.shields.io/badge/license-Apache--2.0-2DA44E?style=flat-square)](./LICENSE)

This repository is the formal companion to the **Ouroboros Thesis** paper line ([`szl-holdings/ouroboros-thesis`](https://github.com/szl-holdings/ouroboros-thesis)). It contains the Lean 4 + Mathlib formalisation of:

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

## Reference-vector parity (Wave 2)

A new entry point — [`lake exe ref_vectors <path>`](./MainRef.lean) — reads a JSON file of golden Λ₉ inputs and asserts that Lean's reference implementation (Float-based, IEEE-754) produces values matching the production TypeScript runtime within an absolute tolerance of `1e-12` and relative tolerance of `1e-9`.

The canonical vector set is checked into [`reference-vectors.json`](./reference-vectors.json) (10 golden vectors covering uniform, monotone, sparse, ground-truth, and adversarial-noisy axes). CI runs the parity check on every push:

```yaml
- name: Λ parity check
  run: lake exe ref_vectors reference-vectors.json
```

On the platform side the same vectors are loaded by [`packages/ouroboros-invariant/test/reference-vectors.test.ts`](https://github.com/szl-holdings/platform) (private) and by every runtime's [`runtime-parity.test.ts`](https://github.com/szl-holdings/platform/blob/main/packages/a11oy-runtime/test/runtime-parity.test.ts) (private). Three runtimes — a11oy, amaru, sentra — are bit-exact equal to the Lean reference and to each other.

**Caveat (honest).** Lean `Float` is IEEE-754 trusted at the builtin level; it is not kernel-verified. The mathematical correctness of `Λ_k(x) = (∏ xᵢ)^(1/k)` lives in the kernel-verified `Lutar/Invariant.lean`; the `ref_vectors` exe checks operational parity, not numerical truth.

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

## How to cite

If you cite this proof artifact in academic or industry work, use the metadata in [`CITATION.cff`](./CITATION.cff) (or cite the latest paper DOI [`10.5281/zenodo.20119582`](https://doi.org/10.5281/zenodo.20119582)).

## License

Apache-2.0. © 2026 Stephen P. Lutar Jr. / SZL Holdings.
