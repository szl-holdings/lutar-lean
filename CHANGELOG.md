# Changelog

All notable changes to this project are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

# CHANGELOG

## Watunakuy fix — K10v2 vacuous proof elimination (2026-05-31, fix/k10v2-discharge-vacuous-proofs)

### Changed

- **`Lutar/PRNG/K10v2_ReplayRoot.lean`** (Watunakuy remediation). Replaced 5
  `Prop := True; proof := trivial` patterns with honest theorem statements.
  This was a Watunakuy Law of Testing violation (Forbidden Tests rule:
  `Prop := True; trivial` is explicitly listed as a forbidden test).
  PhD-Math finding F4 (PHD_MATH_REVIEW.md §7, HIGH severity) documented
  the violation.

  **Obligations discharged (Path A — real proof):**
  - `isReplayRoot_correct` — `IsReplayRoot s expected = true ↔
    generateOutputs s expected.length = expected`. Proved via
    `eq_of_beq` + `simp [beq_iff_eq]` (Lean core `LawfulBEq`).
  - `isReplayRoot_sound` — forward direction of correctness.
  - `findReplayRoot_sound` — soundness of `findReplayRoot` search.
    Proved via `List.find?_some` (Lean core).

  **Obligations downgraded to honest sorry (Path B — obligation present but hard):**
  - `xoshiroNext_injective` — injectivity of the xoshiro256** state
    transition. Requires mechanising Blackman & Vigna (2018) Theorem 1 via
    GF(2)^256 linear algebra. Estimated effort: ~20h.
  - `xoshiroOutput_distinguishes_states` — distinct initial states produce
    distinct trajectory outputs. Depends on xoshiroNext_injective.
  - `replayRoot_unique_in_list` / `prng_replay_root_deterministic` — at most
    one state in a candidate list is a replay-root for a given sequence.
  - `findReplayRoot_complete` — if a candidate satisfies the predicate, find
    returns some value. Straightforward but requires `List.find?_isSome_iff`.
    Estimated effort: ~1h.
  - `xoshiro_period_bound` — period is exactly 2^256 - 1. Requires companion
    matrix primitivity over GF(2). Estimated effort: ~40h.

  **Canonical number impact:**
  - Declarations: 749 → 749 (unchanged; replaced defs with same-count theorems)
  - Sorries (baseline, non-Putnam): 112 → 117 (+5 honest sorries)
  - Sorries (total): 163 → 168
  - The 5 prior `trivial` proofs were NOT counted as sorries but were morally
    equivalent to unverified obligations; they violated Watunakuy. The honest
    sorry count is a more accurate representation.

  **Reference:** Blackman, D., & Vigna, S. (2018). "Scrambled Linear
  Pseudorandom Number Generators." arXiv:1805.01407.

### Updated

- **`.github/data/lean_numbers.json`** — updated to canonical 749/15/14/168
  @ c7c0ba17 post-fix.
- **`README.md`** — updated proof statistics table and NOTE to 749/168.

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
