---
license: apache-2.0
language:
- en
tags:
- formal-verification
- lean4
- mathlib
- dsse
- governance
- agentic-ai
- doctrine-v11
- rae-1
- theorems
- graph
- dependency
- dataset
- doi:10.5281/zenodo.19944926
pretty_name: Lean Theorem Tree — Declaration Manifest Snapshot (269 decls @ c4d13795)
size_categories:
- n<1K
task_categories:
- other
ecosystem-stage: generated-mirror
configs:
- config_name: default
  data_files:
  - split: train
    path: data/lean_theorem_tree.json
  field: declarations
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

[![dataset](https://img.shields.io/badge/dataset-Lean%20theorem%20tree-3af4c8?style=flat-square)](https://huggingface.co/datasets/SZLHOLDINGS/lean-theorem-tree/tree/main)
[![license](https://img.shields.io/badge/license-apache--2.0-7e8aa3?style=flat-square)](https://huggingface.co/datasets/SZLHOLDINGS/lean-theorem-tree)

</p>
</div>

# Lean Theorem Tree — Declaration Manifest Snapshot (269 @ c4d13795)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20434276.svg)](https://doi.org/10.5281/zenodo.20434276)
[![Lean Kernel Green](https://img.shields.io/badge/Lean_4.13--kernel--green@c7c0ba17-22c55e?style=flat-square)](https://github.com/szl-holdings/lutar-lean/commit/c7c0ba17)
[![Sorries](https://img.shields.io/badge/sorries-163-blue?style=flat-square)](https://github.com/szl-holdings/lutar-lean/commit/c7c0ba17)
[![SLSA L1](https://img.shields.io/badge/SLSA-L1_SBOM+DCO-blue?style=flat-square)](https://slsa.dev)
[![DSSE](https://img.shields.io/badge/DSSE-PAE_v1-22c55e?style=flat-square)](https://github.com/secure-systems-lab/dsse)
[![RAE-1](https://img.shields.io/badge/RAE--1-v1.0-D97757?style=flat-square)](https://github.com/szl-holdings/a11oy/pull/122)
[![License](https://img.shields.io/badge/License-Apache_2.0-blue?style=flat-square)](https://www.apache.org/licenses/LICENSE-2.0)

> **Doctrine v11 LOCKED.** No marketing. Every number resolves to a CI log, a Lean proof, or a Zenodo DOI.

Dependency-graph SNAPSHOT of the Lean 4 declarations in the Ouroboros corpus **as of commit `c4d13795` (2026-05-29, Lean v4.14.0-rc1)** — this data file contains **269 declarations** (247 GREEN / 22 TRACKED), NOT the current count. Records include: declaration name, type, dependencies, axiom-usage flags, sorry status. **The current authoritative counts live in [lutar-lean](https://github.com/szl-holdings/lutar-lean) and the szl-lake receipt ledger: 749/14/163 @ c7c0ba17 (Doctrine v11 LOCKED, 8 locked-proven) and 1401/25/270 on experimental `main`@dc64dd80 (CI-green, never folded into the locked count).** Regeneration of this snapshot from the current HEAD is ROADMAP.

5 declarations carry sorry (down from 7 after [PR #109](https://github.com/szl-holdings/lutar-lean/pull/109) discharged P6 and P7). The tree provides the dependency graph data for proof landscape visualization. A `lutar-lean-browser` space is ROADMAP.

## Snapshot (dated; verify against the linked sources)

Counts below are dated snapshots, not live state; the estate inventory is maintained in [profile/public-inventory.json](https://github.com/szl-holdings/.github/blob/main/profile/public-inventory.json).

| Metric | Value | Verify |
|---|---|---|
| Declarations in THIS snapshot | 269 (@ c4d13795, 2026-05-29) | data/lean_theorem_tree.json |
| Current locked-baseline declarations | 749 @ c7c0ba17 | [lutar-lean](https://github.com/szl-holdings/lutar-lean) + szl-lake |
| Current experimental-main declarations | 1401 @ dc64dd80 (CI-green) | szl-lake tier-state receipt |
| Lean axioms | 15 (14 unique) | A1–A18 honest gap |
| Lean sorries | 163 | [lutar-lean@c7c0ba17](https://github.com/szl-holdings/lutar-lean/commit/c7c0ba17) — Doctrine v11 LOCKED |
| Anchor formulas | 44 specified | [a11oy#114](https://github.com/szl-holdings/a11oy/pull/114) |
| Kernel green | Mathlib 4.13.0 d7317655 | [PR #106](https://github.com/szl-holdings/lutar-lean/pull/106) |
| Zenodo DOIs | 6 release + 1 concept alias | [10.5281/zenodo.20434276](https://doi.org/10.5281/zenodo.20434276) |
| RAE-1 protocol | merged | [a11oy#122](https://github.com/szl-holdings/a11oy/pull/122) |

## Cross-references

- **Thesis**: [Ouroboros Thesis v18](https://doi.org/10.5281/zenodo.20434276) · DOI 10.5281/zenodo.20434276
- **Lean companion**: [lutar-lean](https://doi.org/10.5281/zenodo.20424992) · DOI 10.5281/zenodo.20424992
- **Receipt gateway source**: [szl-holdings/hatun-mcp](https://github.com/szl-holdings/hatun-mcp) (GitHub; no public Space is currently published for it)
- **Verifiable corpus**: [SZLHOLDINGS/a11oy-verifiable-corpus](https://huggingface.co/datasets/SZLHOLDINGS/a11oy-verifiable-corpus) — signed receipts + kernel-checked theorems (verify-it-yourself)
- **Live demo**: [a11oy console → a-11-oy.com](https://a-11-oy.com) · [a11oy Space](https://huggingface.co/spaces/SZLHOLDINGS/a11oy) · [killinchu](https://huggingface.co/spaces/SZLHOLDINGS/killinchu)
- **Catalog**: [SZLHOLDINGS on HuggingFace](https://huggingface.co/SZLHOLDINGS)
- **Source**: [lean-theorem-tree on GitHub](https://github.com/szl-holdings/lutar-lean)


## Provenance

| Field | Value |
|---|---|
| Ecosystem stage | `generated-mirror` |
| Doctrine | v11 LOCKED (749/14/163 @ c7c0ba17) — no marketing language, every number resolves to a CI log or Zenodo DOI |
| Thesis DOI | [10.5281/zenodo.20434276](https://doi.org/10.5281/zenodo.20434276) |
| Lean companion DOI | [10.5281/zenodo.20424992](https://doi.org/10.5281/zenodo.20424992) |
| Author | Stephen Paul Lutar Jr. · [ORCID 0009-0001-0110-4173](https://orcid.org/0009-0001-0110-4173) |
---

*SZL Holdings · Lean 749/14/163 @ c7c0ba17 · Doctrine v11 LOCKED*  
*Signed-off-by: Stephen Lutar <stephenlutar2@gmail.com>*

---

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.19944926.svg)](https://doi.org/10.5281/zenodo.19944926)

## Citation


**Cite this.** Part of the SZL Holdings *Ouroboros Thesis* (Governed Post-Determinism).  
Concept DOI (always-latest): [10.5281/zenodo.19944926](https://doi.org/10.5281/zenodo.19944926).  
Author: Stephen P. Lutar Jr. · [ORCID 0009-0001-0110-4173](https://orcid.org/0009-0001-0110-4173) · Dataset license: Apache-2.0; the cited program publication is CC-BY-4.0.  
Full DOI-pinned lineage (v1→v26) + the 8 papers: [szl-papers PAPERS_INDEX](https://github.com/szl-holdings/szl-papers/blob/main/PAPERS_INDEX.md).  
No artifact-specific DOI is minted for this dataset; the concept DOI above covers the program.

Honesty (Doctrine v11): Λ unconditional uniqueness is **Conjecture 1** (machine-checked FALSE as stated) — never a theorem; conditional uniqueness is **Theorem U** (axiom-free). Locked-proven formulas = **exactly 8** {F1,F4,F7,F11,F12,F18,F19,F22}; ~185 experimental theorems are a separate CI-green tier; Khipu BFT safety = Conjecture 2. Trust never 100%.

```bibtex
@misc{lutar_szl_ouroboros,
  author    = {Lutar, Stephen P., Jr.},
  title     = {SZL Holdings --- The Ouroboros Thesis (Governed Post-Determinism)},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.19944926},
  url       = {https://doi.org/10.5281/zenodo.19944926},
  note      = {Concept DOI --- always resolves to the latest version. ORCID 0009-0001-0110-4173. CC-BY-4.0.}
}
```

*Signed-off-by: Stephen Lutar <stephenlutar2@gmail.com>*

---

<div align="center">

**[🛡️ SZLHOLDINGS on Hugging Face →](https://huggingface.co/SZLHOLDINGS)**   ·   **[a-11-oy.com →](https://a-11-oy.com)**   ·   **[SZL Atlas — estate map →](https://huggingface.co/spaces/SZLHOLDINGS/szl-command-lab)**

### Governed AI you can prove.

<sub>SLSA: L1 honest · L2 attested · L3 roadmap. Λ = Conjecture 1 (advisory, never a theorem). Trust ceiling 0.97 — never 100%. Labels honest by default: MEASURED / REPORTED / MODELED / HEURISTIC / UNKNOWN / UNAVAILABLE. locked-proven = exactly 8 {F1,F4,F7,F11,F12,F18,F19,F22}.</sub>

</div>
