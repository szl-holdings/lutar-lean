# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

---

## [Unreleased]

### Fixed
- `tools/locked_formula_runtime.py` (runtime bridge for the locked-8 Lean statements) now admits only each statement's domain and raises `LockedDomainError` (a `ValueError` subclass) outside it: `replay_eq` accepts only JSON-canonical values (no NaN or infinities, tuples, or custom classes), the F4 edge helpers accept only `Nat × Nat` edges and read an edge iterable exactly once (a one-shot iterator could previously get a false "acyclic" result), and the F7/F18/F22 helpers reject bools, floats and negative values. The cycle search is now an iterative memoized DFS (no `RecursionError` on long chains, linear time). New `khipu_append_hypothesis` / `khipu_append_preserves_acyclic` mirror the Lean F4 append hypothesis, which does not require a fresh or maximal node. These are software checks; no Lean file, claim map or receipt changed.
- F4 append prose now states the Lean append hypothesis `hk : ∀ e ∈ newEdges, e.1 = k ∧ e.2 < k` exactly: every appended edge has source `k` and target `< k`, and `k` need not be fresh or maximal. Previously the `ProvedFormulas.lean` docstrings, `claims/locked-formulas.v1.json` (`f4_proves`, F4 `exact_mathematical_statement`, F4 `public_wording`) and `PROVEN_FORMULAS.md` described "a fresh max node", which is narrower than what Lean states; the two F4 notes in the unbuilt `PuriqFormulaLean.lean` are reworded the same way. Docstrings and prose only: no theorem statement, proof, declaration name, claim id, carrier list or count changed.

---

## [1.0.0] — 2026-06-09

### Added
- Doctrine v11 compliance — kernel commit `c7c0ba17` (749 declarations / 14 axioms / 163 sorries)
- SLSA Build Level 1 provenance — honest declaration, not overclaimed
- Section 889 attestation — exactly 5 vendors assessed (Huawei, ZTE, Hytera, Hikvision, Dahua)
- DCO `Signed-off-by:` trailers on all commits per Linux Foundation DCO policy
- OpenTelemetry `traceparent` W3C header propagated end-to-end
- `/api/health` endpoint returning structured JSON with `sovereign: true`
- SBOM (CycloneDX) generated and attached to release
- Cosign keyless OIDC signing for container images
- OpenSSF Scorecard GHA workflow
- SECURITY.md with 90-day responsible disclosure policy
- SUPPORT.md with issue triage SLAs
- CODEOWNERS covering all critical paths
- Dependabot weekly dependency updates
- Trivy/Grype container vulnerability scanning gate
- SLO documentation (p50/p95/p99 targets + error budget)
- Threat model (STRIDE format)
- CITATION.cff for academic citeability

### Security
- Section 889 — no covered telecommunications equipment from Huawei, ZTE, Hytera, Hikvision, or Dahua
- No Iron Bank, FedRAMP, CMMC, or SWFT claims (capability honesty per Anthropic RSP)
- Λ = Conjecture 1 (never a theorem) — mathematical honesty enforced

### Notes
- Warhacker June 9, 2026 release

[Unreleased]: https://github.com/szl-holdings/lutar-lean/compare/v1.0.0...HEAD
[1.0.0]: https://github.com/szl-holdings/lutar-lean/releases/tag/v1.0.0
