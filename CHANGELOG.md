# CHANGELOG

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
