# Frontier showcase — Celestial / Infrared Triangle  ·  **EXPERIMENTAL**

A small, self-contained, kernel-checked formalization inspired by the physics of
**Sabrina Pasterski** (Perimeter Institute) and collaborators: the
**Pasterski–Strominger–Zhiboedov infrared triangle** of celestial holography.

Lean source: [`CelestialIRTriangle.lean`](CelestialIRTriangle.lean).

## What the infrared triangle is

Three corners of infrared physics are pairwise equivalent:

```
            asymptotic symmetries
               /            \
   Ward identity            vacuum transition
             /                \
   soft theorems ---------- memory effects
              Fourier transform
```

- **asymptotic symmetries ↔ soft theorems** — Ward identity
- **asymptotic symmetries ↔ memory effects** — vacuum transition
- **memory effects ↔ soft theorems** — Fourier transform

## Honesty label: EXPERIMENTAL

- Mathlib-free; every theorem closes by `decide` over closed Bool/Int terms, so a
  bare Lean kernel checks it. **Zero `sorry`.** Compiles against
  `leanprover/lean4:v4.18.0` core.
- This file lives **outside `Lutar/`**, so it is *not* counted by
  `.github/scripts/lean_numbers.py` and does **not** touch the locked
  Doctrine-v11 baseline.

### What is proven (exact scope)

We do **not** re-derive any physics theorem and claim **no** result about
gravity or quantum field theory. The kernel checks two honest, discrete things:

1. **The triangle's graph structure.** Three corners, three pairwise relations —
   i.e. the complete graph on three nodes (`triangle_complete`,
   `triangle_counts`).
2. **The arithmetic skeleton of the "soft ↔ memory" (Fourier) edge.** Modelling
   the *news* `N_n` as integer increments of the asymptotic field:
   - the **memory** = net permanent change of the field = running sum of the news
     (the discrete analogue of `∫ N du`);
   - the **soft (zero-frequency) Fourier mode** of the news is
     `Σ_n N_n · e^{i·0·n} = Σ_n N_n · 1`, the same sum, because the kernel at zero
     frequency is `1`;
   - hence **soft-zero-mode = memory** (`soft_zero_mode_eq_memory`), and the net
     field change `h(+∞) − h(−∞)` equals the memory independently of the base
     value (`memory_eq_net_field_change_h10`, `..._hneg`).

These are honest discrete *witnesses* of the relations' shape on a frozen sample,
not the continuum physics.

## References (public arXiv)

- New Gravitational Memories — arXiv:1502.06120 (S. Pasterski, A. Strominger, A. Zhiboedov)
- Asymptotic Symmetries and Electromagnetic Memory — arXiv:1505.00716 (S. Pasterski)
- Flat Space Amplitudes and Conformal Symmetry of the Celestial Sphere — arXiv:1701.00049 (S. Pasterski, S.-H. Shao, A. Strominger)
- Celestial Holography (review) — arXiv:2111.11392 (S. Pasterski, M. Pate, A.-M. Raclariu)
