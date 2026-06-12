# Frontier showcase — Topology & Information Witnesses · **EXPERIMENTAL**

Mathlib-free, bare-kernel-checked discrete witnesses of two structural facts.
Compiles against `leanprover/lean4:v4.18.0` core. Zero `sorry`, no declared axiom,
no `native_decide`. Source: [`TopoInfoWitness.lean`](TopoInfoWitness.lean).

## What is witnessed (honest scope)

1. **Euler characteristic `V − E + F = 2`** — `euler_platonic`. Checked as a closed
   integer identity on all five Platonic solids (the Euler characteristic of the
   2-sphere). `torus_euler_zero` records the contrasting torus value `0`, documenting
   that `=2` is special to the sphere. Euler (1758). `#print axioms` → **none**.

2. **Kraft–McMillan inequality (integer-cleared form)** — a binary prefix-free code on
   lengths `ℓᵢ` exists iff `Σ 2^{−ℓᵢ} ≤ 1`. Cleared by `2^L`, the test is the integer
   inequality `Σ 2^{L−ℓᵢ} ≤ 2^L`:
   - `kraft_satisfied` + `kraft_tight` — lengths `[1,2,3,3]` (`0,10,110,111`) give a
     *complete* code, sum `= 2³` (equality).
   - `kraft_violated` — lengths `[1,1,2]` give sum `5 > 4 = 2²`: no prefix-free code can
     exist. Kraft (1949), McMillan (1956). `#print axioms` → **none**.

## Honesty label: EXPERIMENTAL

- Lives outside `Lutar/`, so **NOT counted** by `.github/scripts/lean_numbers.py`.
  Locked-proven set stays **EXACTLY 8** {F1,F4,F7,F11,F12,F18,F19,F22}.
- Says **nothing** about Λ (Conjecture 1). Discrete witnesses of combinatorial shape —
  **not** the general topology/coding theorems.

## References
- Euler, "Elementa doctrinae solidorum," *Novi Comm. Acad. Sci. Petropolitanae* (1758).
- Kraft, MIT MS thesis (1949); McMillan, "Two inequalities implied by unique
  decipherability," *IRE Trans. Inf. Theory* **2**:115 (1956).
