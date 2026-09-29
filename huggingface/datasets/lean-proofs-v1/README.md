---
license: apache-2.0
tags:
- lean4
- formal-verification
- mathematics
- theorem-proving
- ouroboros-invariant
- szl-holdings
- doi:10.5281/zenodo.19944926
task_categories:
- other
pretty_name: SZL Holdings Lean Proofs v1
size_categories:
- n<1K
language:
- en
configs:
- config_name: reference-vectors
  data_files:
  - split: test
    path: reference-vectors.json
---

<!-- SZL-ESTATE-CARD:v2:START -->
<p align="center"><a href="https://a-11-oy.com/"><img src="https://huggingface.co/spaces/SZLHOLDINGS/README/resolve/main/assets/estate-banner-v2.svg" alt="SZL Holdings — governed, receipted, verifiable" width="100%"></a></p>
<p align="center">
  <a href="https://github.com/szl-holdings/.github/tree/main/doctrine"><img src="https://img.shields.io/badge/doctrine-v11%20LOCKED-0B1F3A?style=flat-square" alt="doctrine v11"></a>
  <a href="https://a-11-oy.com/"><img src="https://img.shields.io/badge/evidence%20wall-LIVE%20%C2%B7%20verify%20in%20browser-3AF4C8?style=flat-square" alt="live evidence wall"></a>
  <a href="https://huggingface.co/datasets/SZLHOLDINGS/szl-lake"><img src="https://img.shields.io/badge/szl--lake-offline%20verifiable-C9B787?style=flat-square" alt="szl-lake offline verifiable"></a>
  <a href="https://huggingface.co/spaces/SZLHOLDINGS/szl-command-lab"><img src="https://img.shields.io/badge/estate%20map-Atlas-5B8DEE?style=flat-square" alt="SZL Atlas estate map"></a>
</p>
<p align="center"><sub>Part of the <a href="https://huggingface.co/SZLHOLDINGS">SZL Holdings</a> governed estate — claims are designed to carry checkable receipts. Verification proves integrity &amp; origin, never accuracy or performance.</sub></p>
<!-- SZL-ESTATE-CARD:v2:END -->

<div align="center">
<p>

[![dataset](https://img.shields.io/badge/dataset-Lean%204%20proofs-3af4c8?style=flat-square)](https://huggingface.co/datasets/SZLHOLDINGS/lean-proofs-v1/tree/main)
[![license](https://img.shields.io/badge/license-apache--2.0-7e8aa3?style=flat-square)](https://huggingface.co/datasets/SZLHOLDINGS/lean-proofs-v1)

</p>
</div>

# SZLHOLDINGS/lean-proofs-v1

The complete Lean 4 theorem library for the **SZL Holdings Ouroboros Invariant** research programme.

## Doctrine v10/v11 Canonical Numbers

| Metric | Value |
|--------|-------|
| Declarations | **749** |
| Unique axioms | **14** (15 raw, 1 dup) |
| Sorries | **163** (112 baseline + 51 Putnam) |
| Tag | `0086521` |

**Honesty rule:** Every theorem is displayed with explicit status — PROVEN / SORRY / AXIOM / CONJECTURE. We NEVER claim "zero sorry".

## Key Theorems

| Theorem | File | Status |
|---------|------|--------|
| A2 IsHomogeneous | Lutar/Axioms.lean | AXIOM |
| A4 IsBounded | Lutar/Bound.lean | PROVEN |
| Λ uniqueness (Conjecture 1) | Lutar/Uniqueness.lean | CONJECTURE (sorry at line 120) |
| TH6 DPI Soundness (Bekenstein) | Lutar/DPI/TH6_DPI_Soundness.lean | PROVEN |
| TH11 Khipu Summation Invariant | Lutar/Khipu/SummationInvariant.lean | PROVEN |

## Build Instructions

```bash
lake build
```

Requires Lean 4 toolchain pinned in `lean-toolchain`. Mathlib v4.13.0 via `lake-manifest.json`.

## Reference Vectors

`reference-vectors.json` contains the **10 golden verification vectors** for the Λ aggregator (weighted geometric mean):

```json
{
  "formula": "Λ_k(x) = (∏ xᵢ)^(1/k)",
  "toleranceAbs": 1e-12,
  "vectors": [ ...10 test cases... ]
}
```

## Sibling Datasets

- `SZLHOLDINGS/rag-corpus-v1` — chunked embeddings for RAG (complementary; this dataset is the raw source-of-truth)
- `SZLHOLDINGS/canonical-formulas-v1` — Python + Lean obligation stubs for every canonical formula
- `SZLHOLDINGS/thesis-corpus-v18` — v18 thesis chapters + 179 formal blocks
- `SZLHOLDINGS/doctrine-v10-v11` — locked doctrine documents

## Citation


**Cite this.** Part of the SZL Holdings *Ouroboros Thesis* (Governed Post-Determinism).  
Concept DOI (always-latest): [10.5281/zenodo.19944926](https://doi.org/10.5281/zenodo.19944926).  
Author: Stephen P. Lutar Jr. · [ORCID 0009-0001-0110-4173](https://orcid.org/0009-0001-0110-4173) · Dataset license: Apache-2.0; the cited program publication is CC-BY-4.0.  
Full DOI-pinned lineage (v1→v26) + the 8 papers: [szl-papers PAPERS_INDEX](https://github.com/szl-holdings/szl-papers/blob/main/PAPERS_INDEX.md).  
No artifact-specific DOI is minted for this dataset; the concept DOI above covers the program.

Honesty (Doctrine v11): Λ unconditional uniqueness is **Conjecture 1** (machine-checked FALSE as stated) — never a theorem; conditional uniqueness is **Theorem U** (axiom-free). Locked-proven formulas = **exactly 8** {F1,F4,F7,F11,F12,F18,F19,F22}; ~185 experimental theorems are a separate CI-green tier; Khipu BFT safety = Conjecture 2. Trust never 100%.

```bibtex
@dataset{szl_lean_proofs_v1,
  author       = {Lutar Jr., Stephen P.},
  title        = {SZL Holdings Lean Proofs v1},
  year         = 2026,
  publisher    = {Hugging Face},
  doi          = {10.5281/zenodo.19944926},
  url          = {https://huggingface.co/datasets/SZLHOLDINGS/lean-proofs-v1},
  note         = {ORCID: 0009-0001-0110-4173}
}
```

Concept DOI: [10.5281/zenodo.19944926](https://doi.org/10.5281/zenodo.19944926)

---

### ◇ Explore the SZL Holdings estate
[▶ a11oy console (a-11-oy.com)](https://a-11-oy.com) · [a11oy Space](https://huggingface.co/spaces/SZLHOLDINGS/a11oy) · [killinchu](https://huggingface.co/spaces/SZLHOLDINGS/killinchu) · [holographic (3D)](https://huggingface.co/spaces/SZLHOLDINGS/holographic) · [all datasets & models → SZLHOLDINGS](https://huggingface.co/SZLHOLDINGS) · [GitHub org](https://github.com/szl-holdings) · [llm-router](https://szlholdings-llm-router-live.hf.space) · [receipt verifier](https://github.com/szl-holdings/governed-receipt-spec) · [receipt spec](https://github.com/szl-holdings/governed-receipt-spec)

---

<div align="center">

**[🛡️ SZLHOLDINGS on Hugging Face →](https://huggingface.co/SZLHOLDINGS)**   ·   **[a-11-oy.com →](https://a-11-oy.com)**   ·   **[SZL Atlas — estate map →](https://huggingface.co/spaces/SZLHOLDINGS/szl-command-lab)**

### Governed AI you can prove.

<sub>SLSA: L1 honest · L2 attested · L3 roadmap. Λ = Conjecture 1 (advisory, never a theorem). Trust ceiling 0.97 — never 100%. Labels honest by default: MEASURED / REPORTED / MODELED / HEURISTIC / UNKNOWN / UNAVAILABLE. locked-proven = exactly 8 {F1,F4,F7,F11,F12,F18,F19,F22}.</sub>

</div>

## Dataset-server loading boundary

The `reference-vectors` config exposes the machine-readable verification vectors as one JSON record. Lean source files, `lake-manifest.json`, and build metadata remain versioned artifacts and are not coerced into tabular examples. A loadable vector record does not establish that every Lean declaration is proved; use the explicit theorem status and build evidence in this card.
