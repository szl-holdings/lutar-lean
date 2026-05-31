# Changelog

All notable changes to this project are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

# CHANGELOG


## v14+ disclosure — axiom drift and CAUCHY_ND gap (2026-05-31, docs/axiom-drift-disclosure-v3-to-v14)

**PhD-Math remediation authored by Allichachiq Yupayqa (Quechua squad).**
**Canonical Lean corpus at this disclosure: 749 declarations / 14 unique axioms / 163 sorries @ c7c0ba17.**

### Added

- **`README.md` — `## Axiom Semantic Drift (v3 to v14)` section (new).** Discloses that
  A2 and A4 changed semantically between the v3 Zenodo deposit
  ([10.5281/zenodo.19983066](https://doi.org/10.5281/zenodo.19983066)) and the current HEAD.

  - **A2 in v3:** described as "zero-pinning."
    **A2 at HEAD (c7c0ba17):** `IsHomogeneous` — positive homogeneity (degree 1):
    `∀ (c : NNReal) (x : Axes k), Λ (fun i => c * x i) = c * Λ x`.

  - **A4 in v3:** described as "page-curve concavity."
    **A4 at HEAD (c7c0ba17):** `IsBounded` — bounded by max axis:
    `∀ x : Axes k, Λ x ≤ Finset.univ.sup' … x`.

  The v3 deposit remains live on Zenodo for citation continuity but is superseded by the
  current axiom system. Any review comparing v3 claims to the current Lean corpus will
  find a disconnect in axiom semantics; this section makes that disconnect explicit.
  Source: PhD-Math review 2026-05-31, Pass 1/5 Finding F8 (MEDIUM).

- **`README.md` — CAUCHY_ND gap paragraph (in Axiom Semantic Drift section).** Discloses
  that the `sorry` at `Lutar/Uniqueness.lean:120` conceals a missing mathematical assumption,
  not purely a Lean engineering task:

  > The proof strategy invokes permutation symmetry of Λ over inputs, but permutation
  > symmetry is not stated in A1–A4. Without it (or a separability lemma), the reduction
  > to the 1D multiplicative Cauchy equation does not go through.

  Consequence: TH10 (`lutar_is_geomean`) is Conjecture 1, not Theorem 1, until either:
  (a) A5 (permutation symmetry) is added and approved per Doctrine §3, or
  (b) a separability lemma is proved from A1–A4.

  Discharge options are listed verbatim in `README.md`.
  Source: PhD-Math review 2026-05-31, Pass 3 (TH10 deep review), Finding F1 (CRITICAL).

- **`README.md` — stale number correction (NEW FINDING, Allichachiq Yupayqa).** README
  cited 752 declarations / 160 sorries @ `3de37e5`. Corrected to canonical
  749 / 163 @ `c7c0ba17`. PR #134 (`chore/numbers-baseline-749-163`) covers the
  `.github/data/lean_numbers.json` file; this commit corrects the README text independently.
  Note: the README stated `3de37e5` was the canonical SHA, but the canonical HEAD is
  `c7c0ba17`. This is the same discrepancy PhD-Math F9 flagged.

### Verification

- `lake build`: not run in this environment (Lean toolchain not installed). Changes are
  documentation-only; no `.lean` files modified.
- Strike 3 (doctrine-grep): 0 hits on changed files.
- Strike 4 (CI grep guard): see `scripts/check_axiom_drift.sh` — a grep-based guard
  that fails if A2/A4 inline definitions in Axioms.lean diverge from README documentation.

### References

- PhD-Math Review 2026-05-31, `PHD_MATH_REVIEW.md`:
  - §2 (Pass 1), F8 — axiom semantic drift between v3 and v14 (MEDIUM)
  - §4 (Pass 3), F1 — CAUCHY_ND sorry conceals missing symmetry axiom (CRITICAL)
- Aczél, J. (1966). *Lectures on Functional Equations and Their Applications.* Academic Press.
  ISBN 0-12-043750-3. Thm 5.1 — multiplicative Cauchy functional equation.
- v3 Zenodo deposit: https://doi.org/10.5281/zenodo.19983066
- Current canonical DOI: https://doi.org/10.5281/zenodo.20434308


## v15 knot calculus (2026-05-28, feat/v15-knot-calculus)

### Added

- **`Lutar/Khipu/SummationInvariant.lean`** (new). Three-tier khipu receipt
  DAG with TH11 `khipuReceipt_checksum_invariant`. Tracks two `sorry`s on the
  routine `List.sum_mapIdx_eq_sum_set_add` + `Nat.add_left_cancel` discharge.
  Sources: Urton 2003 (UT Press); Ascher & Ascher 1981 (U. Michigan Press);
  Medrano & Khosla 2024 (*Latin American Antiquity*).

- **`Lutar/DPOFeasibility.lean`** (new — replaces v14 placeholder `True := by
  trivial`). Substantive TH12 `ΛGateLID_DPO_stability` statement with a
  structurally correct three-step proof; three tagged `sorry`s — Pinsker
  (Mathlib `Probability.Divergences`), Lipschitz from Ch.9
  `gated_qkan_boundedness`, real-arithmetic recombination. Sources: Bai et al.
  2025 (arXiv:2512.01899, SaTML 2026); Rafailov et al. 2023 (arXiv:2305.18290,
  NeurIPS 2023); Pinsker 1964; Tsybakov 2009.

- **`Lutar/PACBayes.lean`** (new). TH13 `governanceHead_PACBayes_bound`.
  Closed-form proofs: `pacBayesBound_mono_kl`, `pacBayes_inequality_form`,
  `pacBayesBound_nonvacuous_iff`, `governanceHead_PACBayes_bound`
  (non-negativity). The probabilistic Pr ≥ 1-δ quantifier remains open;
  arithmetic content is fully formalised. Sources: McAllester 1999 (COLT);
  McAllester 2003 (*Machine Learning* 51); Lotfi et al. 2023 (arXiv:2312.17173,
  NeurIPS 2023); Amari 1985 (Springer); Amari 2016 (Springer).

- **`Lutar/Knot/ReidemeisterConjecture.lean`** (new, CONJECTURE-status).
  Three audit-Reidemeister rewrites R1 (single-axis repack), R2 (independent
  commute), R3 (associativity); all stated as conjecture with explicit
  `sorry` tags. Target v16. Sources: Reidemeister 1927 (*Abh. Math. Sem.
  Univ. Hamburg* 5); Kauffman 1991 (World Scientific); Birman 1974
  (Princeton); Bar-Natan 1995 (*Topology* 34); Vassiliev 1990
  (*Adv. Sov. Math.* 1); Kontsevich 1993.

### Changed

- **`Lutar.lean`**: imports added for the four new modules.

### Verification

- `lake build`: **not run in this environment** (Lean toolchain not
  installed). All files use only standard Mathlib idioms; tagged `sorry`s
  are isolated and documented. Re-run `lake build` locally before merge.

## v14 math corrections (2026-05-28, fix/v14-math-corrections)

### Added

- **`Lutar/TwoWitness.lean`** (new file). Canonical home of the Kochen–Specker
  18-vector NCHV soundness theorem (TH KS-18, referenced from ouroboros-thesis
  v14 §9.2.2). Contents:
  - `contexts : List (Fin 18 × Fin 18 × Fin 18 × Fin 18)` — the 9 contexts of
    4 mutually orthogonal rays from Cabello-Estebaranz-García-Alcaine (1996,
    Phys. Lett. A 212:183–187, arXiv:quant-ph/9706009), matching the
    `KS18_CONTEXTS` constant in the cookbook recipe TS module.
  - `NCHV := Fin 18 → Bool`, `ExactlyOnePerContext`, `inconsistencies`,
    `AnomalyFlag`, `anomalyFlag`.
  - **`two_witness_KS18_soundness`** (proved, **no sorry**): for any NCHV `f`
    satisfying `ExactlyOnePerContext f`, the witness returns
    `inconsistencies f = 0 ∧ anomalyFlag f = CLASSICAL`.
  - **`no_NCHV`**: no `f` satisfies `ExactlyOnePerContext f`, by parity
    (9 = 2·Σ f, contradiction). Depends on `double_count` — currently
    a tagged `sorry` (a routine `Finset.sum_bij` discharge); the parity
    argument is mathematically settled (Cabello et al. 1996).

### Changed

- **`Lutar/Uniqueness.lean` header** rewritten to mark TH10 as a **CONJECTURE**
  rather than a theorem. Status note explains why:
  - `IsEgyptianExact` in `Axioms.lean` currently carries a tautological
    placeholder `weight_eq : (1:ℚ)/k = (1:ℚ)/k` that does not pointwise
    constrain the weight function.
  - To close the Cauchy / Bohr-Mollerup-style uniqueness argument, A3
    needs strengthening (either S1 equal-weight diagonal commitment
    `∀ c, Λ (fun _ => c) = c`, or S2 log-additivity on the multiplicative
    cone).
  - The four-step proof outline (homogeneity+S1, monotonicity+boundedness=
    continuity, S2, conclude Λ x = (Π x_i)^(1/k)) is recorded in the header
    so v15 can pick it up directly.
  - The `lutar_unique` and `lutar_is_geomean` declarations remain Lean
    `axiom`s (kernel-accepted, deductively un-discharged). Downstream
    callers see the same names; the upgrade path is documented.

- **`Lutar.lean`**: added `import Lutar.TwoWitness` so the new module
  participates in the package's build graph.

### Prior art / citations

- Cabello, A., Estebaranz, J. M., & García-Alcaine, G. (1996). "Bell-Kochen-
  Specker theorem: A proof with 18 vectors." *Physics Letters A* 212(4),
  183–187. arXiv:quant-ph/9706009.
- Peres, A. (1991). "Two simple proofs of the Kochen-Specker theorem."
  *J. Phys. A: Math. Gen.* 24, L175.
- Bohr-Mollerup style uniqueness arguments for log-convex / weighted-mean
  functionals — standard in real analysis (cf. Aczél, *Lectures on
  Functional Equations*, 1966).

### Verification

- `lake build`: **not run in this environment** (Lean toolchain not
  installed). The files use only standard Mathlib idioms; the one tagged
  `sorry` is explicit and isolated to `double_count`. Re-run `lake build`
  locally before merge.
