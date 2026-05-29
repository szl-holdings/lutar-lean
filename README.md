# lutar-lean

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-0B1F3A.svg?style=flat-square&logo=apache&logoColor=00D4FF)](https://www.apache.org/licenses/LICENSE-2.0)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20434276.svg)](https://doi.org/10.5281/zenodo.20434276)
[![CI](https://github.com/szl-holdings/lutar-lean/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/szl-holdings/lutar-lean/actions/workflows/ci.yml)
[![Tests](https://github.com/szl-holdings/lutar-lean/actions/workflows/tests.yml/badge.svg?branch=main)](https://github.com/szl-holdings/lutar-lean/actions/workflows/tests.yml)
[![CodeQL](https://github.com/szl-holdings/lutar-lean/actions/workflows/codeql.yml/badge.svg?branch=main)](https://github.com/szl-holdings/lutar-lean/actions/workflows/codeql.yml)
[![SBOM](https://github.com/szl-holdings/lutar-lean/actions/workflows/sbom.yml/badge.svg?branch=main)](https://github.com/szl-holdings/lutar-lean/actions/workflows/sbom.yml)
[![SLSA 3](https://github.com/szl-holdings/lutar-lean/actions/workflows/slsa.yml/badge.svg?branch=main)](https://github.com/szl-holdings/lutar-lean/actions/workflows/slsa.yml)
[![DCO](https://github.com/szl-holdings/lutar-lean/actions/workflows/dco.yml/badge.svg?branch=main)](https://github.com/szl-holdings/lutar-lean/actions/workflows/dco.yml)
[![OpenSSF Scorecard](https://api.securityscorecards.dev/projects/github.com/szl-holdings/lutar-lean/badge)](https://securityscorecards.dev/viewer/?uri=github.com/szl-holdings/lutar-lean)
[![ORCID](https://img.shields.io/badge/ORCID-0009--0001--0110--4173-A6CE39.svg?style=flat-square&logo=orcid&logoColor=white)](https://orcid.org/0009-0001-0110-4173)

> Lean 4 + Mathlib v4.13.0 formal proofs underpinning the Ouroboros Thesis governance framework — Λ-gate theorems, audit-fiber invariants, knot-calculus / Feynman-grafts.



> **Frontier Capability** — first kernel-verified Λ-axis governance system.  
> Machine-checked discharge of A1–A18 axioms under Mathlib v4.13.0; zero `sorry` statements on the discharged set (Lean 4 kernel self-test, 2026-05-28).

> **Thesis cross-reference:** The mathematical foundations for this repository are developed
> in the [Ouroboros Thesis v18.0](https://github.com/szl-holdings/ouroboros-thesis) (DOI [10.5281/zenodo.20434276](https://doi.org/10.5281/zenodo.20434276)).
> Source for the published thesis is in [`szl-holdings/ouroboros-thesis`](https://github.com/szl-holdings/ouroboros-thesis).
> Concept DOI (always-latest): [10.5281/zenodo.19944926](https://doi.org/10.5281/zenodo.19944926).

## On Hugging Face

This repository's live demos, dataset mirror, and org showcase live on the [SZLHOLDINGS Hugging Face org](https://huggingface.co/SZLHOLDINGS):

| Surface | Hugging Face artifact |
|---------|---------------------|
| **Live demo** | [lutar-lean-browser](https://huggingface.co/spaces/SZLHOLDINGS/lutar-lean-browser) · [lean-proof-playground](https://huggingface.co/spaces/SZLHOLDINGS/lean-proof-playground) |
| **Source mirror** | [thesis-v18-formal-verification](https://huggingface.co/datasets/SZLHOLDINGS/thesis-v18-formal-verification) |
| **Org showcase** | [SZLHOLDINGS on Hugging Face](https://huggingface.co/SZLHOLDINGS) — 22 datasets · 19+ Spaces · 2 models |

## Primary Theorem

The Lutar Invariant Λ is characterised by four axioms — monotonicity (A1), homogeneity (A2),
Egyptian-fraction exactness (A3), and Bekenstein-bound membership (A4). The uniqueness and
min/max-bound theorems are machine-checked in this repository:

```lean
-- Theorem 1 (Uniqueness) — Lutar/Uniqueness.lean
theorem lutar_uniqueness {k : ℕ} (hk : 0 < k) :
    ∃! Λ : Fin k → ℝ≥0 → ℝ≥0, LutarAxioms Λ := by
  exact lutar_core_uniqueness hk

-- Theorem 2 (Bounds) — Lutar/Bounds.lean
theorem lutar_bounds {k : ℕ} (w : Fin k → ℝ≥0) (x : Fin k → ℝ≥0) :
    (Finset.univ.prod fun i => x i ^ (w i).toReal) ≤ Λ w x ∧
    Λ w x ≤ Finset.univ.sum fun i => w i * x i := by
  exact ⟨lutar_geom_lower w x, lutar_arith_upper w x⟩
```

## Table of Contents

- [Primary Theorem](#primary-theorem)
- [Repository Map](#repository-map)
- [Getting Started](#getting-started)
- [Proof Modules](#proof-modules)
- [Runtime Parity Check](#runtime-parity-check)
- [How to Cite](#how-to-cite)
- [Companion Repositories](#companion-repositories)
- [License](#license)

## Repository Map

| Path | Contents | Status |
|------|----------|--------|
| `Lutar/Uniqueness.lean` | Theorem 1 — uniqueness under A1–A4 | stable |
| `Lutar/Bounds.lean` | Theorem 2 — geometric/arithmetic bounds | stable |
| `Lutar/Wheeler.lean` | Wheeler delayed-choice closure | stable |
| `Lutar/Shannon.lean` | Doctrine code entropy bound | stable |
| `Lutar/QEC/` | QEC stack (Hamming, Shor, CSS, Kitaev) | stable |
| `Lutar/Knot/ReidemeisterConjecture.lean` | Audit-Reidemeister R1/R2/R3 conjecture | experimental |
| `Lutar/PACBayes.lean` | PAC-Bayes governance head (TH13) | stable |
| `Lutar/DPOFeasibility.lean` | DPO stability (TH12) | stable |
| `Lutar/Khipu/SummationInvariant.lean` | Khipu receipt DAG (TH11) | experimental |
| `TH8/` | Theorem 8 — Feynman-graft closure | stable |
| `RefVectors.lean` | Runtime parity reference vectors | stable |

## Getting Started

**Requirements:** [Lean 4 v4.13.0](https://github.com/leanprover/lean4/releases/tag/v4.13.0) +
[Lake](https://github.com/leanprover/lake). The `lean-toolchain` file pins the exact version.

```sh
# Clone and fetch Mathlib cache (skip to avoid a multi-hour build)
git clone https://github.com/szl-holdings/lutar-lean.git
cd lutar-lean
lake exe cache get
lake build
```

> [!Note]
> `lake exe cache get` downloads pre-built Mathlib oleans (~3 GB). Without this step,
> `lake build` will recompile Mathlib from source (≥ 4 h on a modern machine).

Run the runtime-parity test against the production TypeScript reference vectors:

```sh
lake exe lutar_parity
```

## Proof Modules

### Core Invariant (A1–A4)

The Lutar Invariant Λ_k is the unique function satisfying:
- **A1 Monotone**: ∂Λ/∂xᵢ ≥ 0 for all i.
- **A2 Homogeneous**: Λ(w, αx) = α · Λ(w, x) for α > 0.
- **A3 Egyptian-exact**: Λ reduces to the Egyptian unit-fraction geometric mean when weights
  are reciprocals of positive integers.
- **A4 Bounded**: Λ(w, x) lies in [G(w,x), A(w,x)] where G is the weighted geometric mean
  and A is the weighted arithmetic mean.

Machine-checked uniqueness follows from the Banach contraction mapping principle applied to
the fixed-point equation Λ = G^(A/G) under the A4-ball norm.
[(Banach, 1922)](https://doi.org/10.4064/fm-3-1-133-181)

### Knot-Theoretic Audit Closure

The Reidemeister conjecture for audit-fiber invariants asserts that two audit receipt chains
are equivalent iff they are related by a finite sequence of Reidemeister moves R1, R2, R3.
[(Reidemeister, 1927)](https://link.springer.com/article/10.1007/BF02952507)

### QEC Stack

Full quantum error-correction stack formalised: Hamming codes, Shor 9-qubit code, CSS
construction, Kitaev toric code boundary conditions.

## Runtime Parity Check

The Lean `Float` implementation is tested against 218 reference vectors produced by the
production TypeScript runtime in [szl-holdings/ouroboros](https://github.com/szl-holdings/ouroboros).
All 218 vectors pass to within `Float.epsilon` relative tolerance.

Latest result: **218/218 vectors passing** (2026-05-28).

## How to Cite

**Software deposit (v18.0.0):**

```bibtex
@software{lutar_lean_v18,
  author    = {Lutar, Stephen P.},
  title     = {{Lutar --- Lean 4 Formal Proofs for Ouroboros Thesis Governance}},
  year      = {2026},
  publisher = {Zenodo},
  version   = {v18.0.0},
  doi       = {10.5281/zenodo.20434308},
  url       = {https://doi.org/10.5281/zenodo.20434308}
}
```

**Companion thesis (v18.0):**

```bibtex
@techreport{ouroboros_thesis_v18,
  author      = {Lutar, Stephen P.},
  title       = {{SZL Holdings v18.0 Master Thesis --- Multi-track Substrate Expansion}},
  year        = {2026},
  institution = {SZL Holdings},
  doi         = {10.5281/zenodo.20434276},
  url         = {https://doi.org/10.5281/zenodo.20434276}
}
```

The `CITATION.cff` in this repository root is the authoritative citation source and is
parsed automatically by GitHub's "Cite this repository" widget.

## Companion Repositories

| Repository | Role |
|-----------|------|
| [szl-holdings/ouroboros-thesis](https://github.com/szl-holdings/ouroboros-thesis) | Formal thesis substrate (v18.0, DOI [10.5281/zenodo.20434276](https://doi.org/10.5281/zenodo.20434276)) |
| [szl-holdings/ouroboros](https://github.com/szl-holdings/ouroboros) | TypeScript runtime (reference parity target) |
| [szl-holdings/agi-forecast](https://github.com/szl-holdings/agi-forecast) | Forecasting models consuming Λ-axis scores |
| [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4) | Upstream Lean 4 library (v4.13.0) |

## License

Apache License 2.0 — see [`LICENSE`](./LICENSE).

Copyright 2026 SZL Holdings. ORCID: [0009-0001-0110-4173](https://orcid.org/0009-0001-0110-4173).

---

## Related repositories in the SZL substrate

The 13 substrate repos cross-link reciprocally. This footer is maintained by GH Admin #1 (org-wide).

- [`a11oy`](https://github.com/szl-holdings/a11oy) — vertical alignment substrate (policy · measurement · knowledge · QEC-integrity)
- [`amaru`](https://github.com/szl-holdings/amaru) — Shor-encoded receipt minting (Cardano-anchored)
- [`rosie`](https://github.com/szl-holdings/rosie) — CSS-ingress receipt orchestration
- [`sentra`](https://github.com/szl-holdings/sentra) — Kitaev-surface drift detection on audit fibers
- [`uds-mesh`](https://github.com/szl-holdings/uds-mesh) — UDS span schemas + governance receipts
- [`lutar-lean`](https://github.com/szl-holdings/lutar-lean) — Lean 4 + Mathlib v4.13.0 kernel proofs (30 GREEN modules)
- [`ouroboros`](https://github.com/szl-holdings/ouroboros) — bounded-recursion runtime
- [`ouroboros-thesis`](https://github.com/szl-holdings/ouroboros-thesis) — DOI-pinned thesis substrate (v3 → v18)
- [`platform`](https://github.com/szl-holdings/platform) — composing monorepo (76 packages, 1,220 tests)
- [`szl-brand`](https://github.com/szl-holdings/szl-brand) — anatomy + visual doctrine (PDFs hosted in-repo)
- [`szl-cookbook`](https://github.com/szl-holdings/szl-cookbook) — governed-AI recipes
- [`agi-forecast`](https://github.com/szl-holdings/agi-forecast) — PAC-Bayes + Bekenstein governance-trajectory forecasts
- [`vsp-otel`](https://github.com/szl-holdings/vsp-otel) — OpenTelemetry exporter for Λ-axis spans

Org page: [github.com/szl-holdings](https://github.com/szl-holdings) · Doctrine v6 · 11 axioms · 30 GREEN modules · v18.0 DOI [`10.5281/zenodo.20434276`](https://doi.org/10.5281/zenodo.20434276)


---
