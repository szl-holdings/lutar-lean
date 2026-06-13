# DEPENDENCY_MAP.md — Theorem U (`Lutar/Uniqueness/`)

This map records exactly what the Theorem-U pack depends on, so a reviewer can
confirm in one read that **Theorem U is a sound REDUCTION** to already-proven
in-tree results plus the Lean/Mathlib trust base — it introduces **NO new
`axiom` token** and **no proof placeholder**.

- **Scope:** `Lutar/Uniqueness/` (additive, EXPERIMENTAL; NOT in the locked
  v11 baseline 749 / 14 / 163 @ `c7c0ba17`; locked-proven stays EXACTLY 8
  {F1,F11,F12,F18,F19}).
- **Status of Λ:** the unconditional uniqueness statement
  (`Conjecture1_LambdaUnique`) ships **statement-only** and is **machine-checked
  false as stated** — Λ stays **Conjecture 1**.

---

## Module DAG

```
Lutar.Axioms ─┐
Lutar.Invariant ─┐
               ├─► Uniqueness/LambdaEquiv.lean        (≈Λ: Equivalence + Decidable + nondegeneracy)
               │        │
Round13.Lambda_Uniqueness ─┤        (Factors, maxAgg, maxAgg_ne_Lambda, lambda_unique_of_factors)
               │        ▼
               ├─► Uniqueness/Identifiability.lean    (IA / FactorAssumptions / SeparableAssumptions
               │        │                              + bridges + Conjecture1 statement-only)
Round13.LambdaSeparable ─┤        (lambda_unique_of_separable)
               │        ▼
               └─► Uniqueness/TheoremU.lean           (Theorem U + corollaries, BY REDUCTION)
                        │
                        ▼
                  Uniqueness/AxiomCheck.lean          (axiom-hygiene ledger + #print axioms)
```

`Lutar.lean` imports all four (after `Lutar.Wave23.QuorumSafety`).

---

## Per-declaration dependency table

| New declaration | File | Depends on (in-tree / Mathlib) | Adds axiom? |
|---|---|---|---|
| `InvariantΛ`, `LambdaEquiv` (`≈Λ`) | LambdaEquiv | `Aggregator`, `auditProbe` | no |
| `lambdaEquiv_equivalence` (refl/symm/trans), `Setoid` | LambdaEquiv | `Eq` equivalence | no |
| `instDecidableLambdaEquiv` | LambdaEquiv | `Classical.dec` (noncomputable) | no (kernel base) |
| `lambdaEquiv_nondegenerate` | LambdaEquiv | `Round13.maxAgg`, `maxAgg_ne_Lambda` rpow script, `Λ_def` | no |
| `FactorAssumptions` / `SeparableAssumptions` / `IdentifiabilityAssumptions` | Identifiability | `Aggregator`, `LutarAxioms`, `Factors` | no |
| `factorAssumptions_to_IA` | Identifiability | `NNReal.mul_rpow`, `NNReal.one_rpow`, `NNReal.rpow_le_rpow` | no |
| `separableAssumptions_to_IA` | Identifiability | field copy | no |
| `Anchored` / `Normalized` | Identifiability | `Λ` | no |
| `Conjecture1_LambdaUnique` | Identifiability | **statement-only `Prop`** (NO proof) | no |
| `CorollaryU2_LambdaUnique_Factors` | TheoremU | `Round13.lambda_unique_of_factors` | no |
| `CorollaryU1_LambdaUnique_Separable` | TheoremU | `Round13.lambda_unique_of_separable` | no |
| `identifiability_forces_lambda` | TheoremU | `Round13.lambda_unique_of_separable` | no (conditional only; Λ unconditional uniqueness stays Conjecture 1) |
| `TheoremU_LambdaUnique` (`≈Λ`) | TheoremU | `identifiability_forces_lambda` (reduction) | no |
| `TheoremU_LambdaUnique_eq` (strict `=`) | TheoremU | `identifiability_forces_lambda` | no |
| `lambda_equiv_to_eq_of_anchored` | TheoremU | `Anchored` (`Eq.trans`/`symm`) | no (conditional only; Λ unconditional uniqueness stays Conjecture 1) |
| `theoremU_axiom_sets_kernel_only`, `locked_count_five`, `theoremU_excluded_from_locked`, `conjecture1_still_open` | AxiomCheck | `decide` | no |

**No row introduces a declared axiom.** The only trust base is the Lean kernel
(`propext`, `funext`, `Classical.choice`, `Quot.sound`) plus Mathlib lemmas.

---

## Key reused upstream theorems (already proven, unchanged)

- `Round13.lambda_unique_of_separable` — Λ-uniqueness from {A1–A5} + separability
  + slice-multiplicativity + unit-normalization + slice-monotonicity.
- `Round13.lambda_unique_of_factors` — Λ-uniqueness from {A1–A5} + power-law
  factorization `Φ x = ∏ (x i)^(αᵢ)`.
- `Round13.maxAgg_ne_Lambda` — the proven A1–A5 counterexample at `![4,1]`
  (`maxAgg = 4`, `Λ = 2`); reused verbatim as the `≈Λ` non-degeneracy witness.

## CI enforcement

`.github/workflows/lake-build.yml` → step **"Axiom-hygiene gate (Theorem-U
pack)"**:

1. fails if any `axiom` token is declared under `Lutar/Uniqueness/`;
2. fails on any whole-word `sorry`/`admit` placeholder there;
3. compiles `Uniqueness/AxiomCheck.lean` and fails if `#print axioms` reports
   `sorryAx` for any Theorem-U declaration.

The existing **drift gate** (`check_numbers_drift.py`) continues to assert the
locked counts (declarations / axioms / sorries / axiom-name set) are unchanged,
because `Lutar/Uniqueness/` is registered under `EXPERIMENTAL_SCOPES` in
`lean_numbers.py` (consistent with Wave8–23).
