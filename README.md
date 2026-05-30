# lutar-lean — Lean 4 Formal Proofs for the Ouroboros Thesis

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-0B1F3A.svg?style=flat-square&logo=apache&logoColor=00D4FF)](https://www.apache.org/licenses/LICENSE-2.0)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20434308.svg)](https://doi.org/10.5281/zenodo.20434308)
[![CI](https://github.com/szl-holdings/lutar-lean/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/szl-holdings/lutar-lean/actions/workflows/ci.yml)
[![Tests](https://github.com/szl-holdings/lutar-lean/actions/workflows/tests.yml/badge.svg?branch=main)](https://github.com/szl-holdings/lutar-lean/actions/workflows/tests.yml)
[![CodeQL](https://github.com/szl-holdings/lutar-lean/actions/workflows/codeql.yml/badge.svg?branch=main)](https://github.com/szl-holdings/lutar-lean/actions/workflows/codeql.yml)
[![SBOM](https://github.com/szl-holdings/lutar-lean/actions/workflows/sbom.yml/badge.svg?branch=main)](https://github.com/szl-holdings/lutar-lean/actions/workflows/sbom.yml)
[[![SLSA L1 · L2 roadmap](https://img.shields.io/badge/SLSA-L1_%E2%86%92_L2_roadmap-0B1F3A.svg?style=flat-square)](https://github.com/szl-holdings/lutar-lean/actions/workflows/slsa-provenance.yml)
[![GHAS Code Security](https://img.shields.io/badge/GHAS-Code_Security-2DA44E.svg?style=flat-square&logo=github)](https://github.com/szl-holdings/lutar-lean/security/code-scanning)
[![Secret Protection](https://img.shields.io/badge/GHAS-Secret_Protection-2DA44E.svg?style=flat-square&logo=github)](https://github.com/szl-holdings/lutar-lean/security/secret-scanning)
[![DCO](https://github.com/szl-holdings/lutar-lean/actions/workflows/dco.yml/badge.svg?branch=main)](https://github.com/szl-holdings/lutar-lean/actions/workflows/dco.yml)
[![OpenSSF Scorecard](https://api.securityscorecards.dev/projects/github.com/szl-holdings/lutar-lean/badge)](https://securityscorecards.dev/viewer/?uri=github.com/szl-holdings/lutar-lean)
[![ORCID](https://img.shields.io/badge/ORCID-0009--0001--0110--4173-A6CE39.svg?style=flat-square&logo=orcid&logoColor=white)](https://orcid.org/0009-0001-0110-4173)


> **NOTE:** SLSA Level 1 (source + build provenance documented). L2/L3 require Sigstore + isolated builders (roadmap).

> Lean 4 + Mathlib v4.13.0 formal proofs underpinning the Ouroboros Thesis — 217 declarations, 12 axioms, 5 residual sorries (all tagged with discharge routes).  
> Doctrine v6 · DOI [10.5281/zenodo.20434308](https://doi.org/10.5281/zenodo.20434308)

**lutar-lean** contains the machine-checked Lean 4 proofs for the Λ-gate theorems, audit-fiber invariants, and knot-calculus / Feynman-grafts of the [Ouroboros Thesis](https://github.com/szl-holdings/ouroboros-thesis). It provides the formal verification substrate for all SZL runtime governance claims.

> [!WARNING]
> **`lake build` is currently failing** on `main` (PRs #98–#102 open with fixes). Merge order: #98 → #99 → #100 → #101 → #102. Do not present the kernel check as passing until these are merged.

> [!NOTE]
> **5 residual `sorry` placeholders** exist in theorem bodies (not axioms). Each is tagged with a discharge route:
> - `Lutar/Uniqueness.lean:120` — CAUCHY_ND (~40h sprint)
> - `Lutar/TwoWitness.lean:163`
> - `Lutar/HUKLLA/SBOMProvenance.lean:109`
> - `Lutar/PACBayes/MadhavaBound.lean:126,145`
> > >
> The 12-axiom set is sorry-free. TH10 uniqueness is axiom-structured (not fully machine-checked) — this is disclosed in the thesis.

---

## On Hugging Face

[SZLHOLDINGS on Hugging Face](https://huggingface.co/SZLHOLDINGS) — 27 Spaces · 31 datasets · 2 models

| Surface | Artifact |
|---------|----------|
| Live demo | [lutar-lean-browser](https://huggingface.co/spaces/SZLHOLDINGS/lutar-lean-browser) · [lean-proof-playground](https://huggingface.co/spaces/SZLHOLDINGS/lean-proof-playground) |
| Source mirror | [thesis-v18-formal-verification](https://huggingface.co/datasets/SZLHOLDINGS/thesis-v18-formal-verification) |

---

## Proof statistics

| Metric | Count | Verify |
|--------|-------|--------|
| Lean declarations (theorem/lemma/def) | 217 | `grep -r "^theorem\|^lemma\|^def " Lutar/ \| wc -l` |
| Axioms | 12 | `grep -r "^axiom " Lutar/ \| wc -l` |
| Residual sorries | 5 (baseline) | `grep -rn "sorry" Lutar/ \| grep -v "-- .*sorry" \| wc -l` |
| Putnam tracked sorries | 134 (2/12 Lean-discharged · 10/12 structure) | [agi-forecast](https://github.com/szl-holdings/agi-forecast) |
| Zenodo DOIs (org) | 7 | [Zenodo community](https://zenodo.org/communities/szl-holdings) |
| HF Spaces (org) | 24 | [SZLHOLDINGS HF org](https://huggingface.co/SZLHOLDINGS) |

---

## Primary theorems

```lean
-- Theorem 1 (Uniqueness) — Lutar/Uniqueness.lean
-- Status: axiom-structured (TH10); CAUCHY_ND sorry at line 120
theorem lutar_uniqueness {k : ℕ} (hk : 0 < k) :
    ∃! Λ : Fin k → ℝ≥0 → ℝ≥0, LutarAxioms Λ := by
  exact lutar_core_uniqueness hk

-- Theorem 2 (Bounds) — Lutar/Bounds.lean
-- Status: fully machine-checked (sorry-free)
theorem lutar_bounds {k : ℕ} (w : Fin k → ℝ≥0) (x : Fin k → ℝ≥0) :
    (Finset.univ.prod fun i => x i ^ (w i).toReal) ≤ Λ w x ∧
    Λ w x ≤ Finset.univ.sup' ⟨0, Finset.mem_univ _⟩ (fun i => x i) := by
  exact lutar_bounds_proof w x
```

---

## Quick start

```bash
lake update
lake build   # currently failing — see PRs #98-#102
lake test
```

---

## Cross-references

- [ouroboros-thesis](https://github.com/szl-holdings/ouroboros-thesis) — thesis source (DOI [10.5281/zenodo.20434276](https://doi.org/10.5281/zenodo.20434276))
- [ouroboros](https://github.com/szl-holdings/ouroboros) — runtime reference implementation
- Concept DOI (always-latest): [10.5281/zenodo.19944926](https://doi.org/10.5281/zenodo.19944926)

---

## License

[Apache 2.0](https://www.apache.org/licenses/LICENSE-2.0) — SZL Holdings

---

## Citation

```
S. P. Lutar Jr., "lutar-lean — Lean 4 Formal Proofs for the Ouroboros Thesis,"
Zenodo, DOI 10.5281/zenodo.20434308, 2026.
```
ORCID: [0009-0001-0110-4173](https://orcid.org/0009-0001-0110-4173)

---

## Security

See [SECURITY.md](./SECURITY.md) for responsible-disclosure policy.

## Lineage

This component is part of the SZL Holdings governance substrate. Its mathematical patterns trace to durable, scholarly-documented historical lineages (Rhind Papyrus false position, Inka khipu summation, Liu Hui polygon π, Madhava series remainder bounds, Cauchy–Banach uniqueness). See [docs/ANCIENT_TEXTS_FORMULA_LINEAGE.md](https://github.com/szl-holdings/a11oy/blob/main/docs/ANCIENT_TEXTS_FORMULA_LINEAGE.md) for the full source → pattern → runtime map.

Doctrine v6 boundary: ancient sources inspire verifiable mathematical patterns. No secret-decoding claims. No mystical language.
