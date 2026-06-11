# Putnam Formalization Showcase

A small, **honestly labeled** showcase of Putnam (and Putnam-style) problems
formalized in Lean 4, living alongside the Lutar Invariant corpus.

Every Lean file carries one of two labels, and the label is enforced by what the
Lean kernel actually accepts — never by wishful thinking:

- **REAL** — a complete, kernel-checked proof with **zero `sorry`** whose
  `#print axioms` uses only in-policy Lean-core axioms
  (`propext`, `Classical.choice`, `Quot.sound`). REAL means the kernel checks it.
- **DEMO** — the *statement* is formalized and typechecks, but the proof is
  `sorry`. A DEMO file builds (a `sorry` is a warning, not an error) yet is
  **never** called REAL, because `#print axioms` would report `sorryAx`.

This follows the repository's honesty doctrine v11: *never label a result REAL
unless the kernel actually checks it.*

## Contents

| # | Problem | Label | Lean file | Axioms |
|---|---------|-------|-----------|--------|
| P01 | Putnam 2001 A1 — `(a*b)*a = b ⟹ a*(b*a) = b` | **REAL** | [`PutnamLean/P01.lean`](../PutnamLean/P01.lean) | none |
| P02 | Classic / Putnam-style — `n³ ≡ n (mod 6)` | **REAL** | [`PutnamLean/P02.lean`](../PutnamLean/P02.lean) | `propext` |
| P03 | Putnam 2019 A1 — `A³+B³+C³−3ABC` representability | **REAL** | [`PutnamLean/P03.lean`](../PutnamLean/P03.lean) | `propext`, `Classical.choice`, `Quot.sound` |
| P04 | Putnam 2020 A2 — `∑ 2^{k−j} C(k+j,j) = 4^k` | **REAL** | [`PutnamLean/P04.lean`](../PutnamLean/P04.lean) | `propext`, `Quot.sound` |

Per-problem writeups: [P01](P01.md) · [P02](P02.md) · [P03](P03.md) · [P04](P04.md).

## Build & verification

The Lean files are bundled as the `PutnamShowcase` library in the repository
[`lakefile.lean`](../../lakefile.lean) and built as part of the default targets:

```bash
lake build              # builds the whole library, including PutnamShowcase
lake build PutnamShowcase
```

The showcase modules are **Mathlib-free** (core Lean only) and compile against
the pinned toolchain `leanprover/lean4:v4.18.0`. CI exercises them via the
`Lake build (gate + numbers)` workflow (`.github/workflows/lake-build.yml`),
which runs `lake build` over the whole library, and via the `Lean kernel check`
workflow (`.github/workflows/lean.yml`).

The honesty labels are independently reproducible: each REAL file emits a
`#print axioms` line into the build log, and a DEMO file's `sorry` would surface
as a build warning. To check a single file locally with just the core toolchain:

```bash
export PATH="$HOME/.elan/bin:$PATH"
elan run leanprover/lean4:v4.18.0 lean Showcase/PutnamLean/P01.lean
# ⇒ 'Showcase.Putnam.putnam2001A1' does not depend on any axioms
elan run leanprover/lean4:v4.18.0 lean Showcase/PutnamLean/P02.lean
# ⇒ 'Showcase.Putnam.cube_mod_six' depends on axioms: [propext]
```

## Scope note

The showcase lives under `Showcase/` (outside `Lutar/`) and is therefore **not**
counted by the canonical corpus counter
(`.github/scripts/lean_numbers.py`, which walks only `Lutar/` + `Main.lean`).
All four proofs here are REAL (kernel-checked, zero `sorry`); the showcase does
**not** affect the locked Doctrine-v11 numbers and does **not** alter the
locked-proven formula set. This showcase is purely additive.
