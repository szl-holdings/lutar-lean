# Frontier showcase — Quantum-Information Witnesses · **EXPERIMENTAL**

A small, self-contained, kernel-checked formalization of the **discrete arithmetic
skeletons** of three load-bearing quantum-information facts. Mathlib-free; every
theorem closes by `decide` / `omega` over closed terms, so a **bare Lean kernel**
checks it. Compiles against `leanprover/lean4:v4.18.0` core.

Lean source: [`QuantumInfoWitness.lean`](QuantumInfoWitness.lean).

## What is witnessed (honest scope — read this)

We do **NOT** re-derive quantum mechanics and claim **NO** physical theorem. We
formalize the *combinatorial shape* of three facts as closed identities a kernel checks:

1. **No-cloning as a linearity obstruction** — `nocloning_witness`. A perfect cloner
   must reproduce the *product* of amplitudes (nonlinear); quantum evolution is
   *linear*. We prove no integer-linear readout can match the product map on the four
   basis-like inputs `(0,0),(1,0),(0,1),(1,1)` — forcing `1 = 0`, a contradiction.
   This is the integer shadow of Wootters–Zurek / Dieks (1982).
   `#print axioms` → `[propext, Quot.sound]` (bounty allowlist; no `Classical.choice`).

2. **Classical CHSH ceiling from locality** — `chsh_classical_bound`. In a deterministic
   *local* model each correlation factorizes as `E(x,y) = A(x)·B(y)`. Exhaustively over
   all 16 local outcome assignments, the CHSH value lies in `[−2, 2]`. The crux is
   *locality* — four independent signs could reach 4; the product factorization is what
   caps it at 2. `tsirelson_gap` records the integer gap `2² = 4 < 8 = (2√2)²`, the
   shadow of why quantum correlations strictly exceed every classical model. We do **not**
   prove the `2√2` value itself (operator-norm analysis, out of scope).
   `#print axioms` → **no axioms** (bare kernel).

3. **Distance-3 repetition code corrects one error** — `repetition_corrects_one_error`.
   Majority decoding recovers logical `0`/`1` from `000`/`111` and any single bit-flip.
   The integer shadow of "distance-3 ⇒ corrects `⌊(3−1)/2⌋ = 1` error."
   `#print axioms` → **no axioms** (bare kernel).

## Honesty label: EXPERIMENTAL

- Mathlib-free; bare-kernel checked; **zero `sorry`**; **no declared axiom**;
  **no `native_decide`**.
- Lives outside `Lutar/`, so it is **NOT counted** by
  `.github/scripts/lean_numbers.py` and does **not** touch the locked Doctrine-v11
  baseline. Locked-proven set stays **EXACTLY 8** {F1,F4,F7,F11,F12,F18,F19,F22}.
- Says **nothing** about Λ: Λ-uniqueness stays **Conjecture 1** (machine-checked FALSE).
- These are honest discrete *witnesses* of the facts' combinatorial shape, **not** the
  physics and **not** the Hilbert-space proofs.

## References

- Wootters & Zurek, "A single quantum cannot be cloned," *Nature* **299**:802 (1982).
- Dieks, "Communication by EPR devices," *Phys. Lett. A* **92**:271 (1982).
- Clauser, Horne, Shimony, Holt, *Phys. Rev. Lett.* **23**:880 (1969).
- Cirel'son (Tsirelson), "Quantum generalizations of Bell's inequality," *Lett. Math.
  Phys.* **4**:93 (1980).
- Shor, "Scheme for reducing decoherence…," *Phys. Rev. A* **52**:R2493 (1995).
- Nielsen & Chuang, *Quantum Computation and Quantum Information*, CUP (2010).
