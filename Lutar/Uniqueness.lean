/-
# Uniqueness (CONJECTURE, postulated as Lean axiom — see status note)

**Conjecture (Lutar uniqueness, TH10).** Let `Λ, Λ' : (Fin k → ℝ≥0) → ℝ≥0`
both satisfy the four Lutar axioms (A1 monotone, A2 homogeneous,
A3 Egyptian-exact, A4 bounded). Then `Λ = Λ'`, and both equal the weighted
geometric mean with unit-fraction weights — i.e. `Λ_k` of `Invariant.lean`.

## Status — DOWNGRADED from "Theorem" to "Conjecture" in v14

The statements below remain Lean `axiom` declarations: kernel-accepted but
**NOT discharged as deductive proofs**. The thesis v14 text reflects this
honestly: in §3.3 the claim is now labelled **Conjecture 1 (TH10)**, not
Theorem 1.

### Why the proof does not close yet

`IsEgyptianExact` in `Axioms.lean` carries `k_pos : 0 < k` together with
a tautological placeholder `weight_eq : (1 : ℚ) / k = (1 : ℚ) / k`. The
placeholder does not pointwise constrain the weight function — any
aggregator with `k_pos` satisfies it. A standard Cauchy / Bohr-Mollerup-
style uniqueness argument needs at least one of the following
strengthenings of A3:

  (S1) equal-weight diagonal commitment:
       `∀ c : NNReal, Λ (fun _ => c) = c`
  (S2) log-additivity on the multiplicative cone (positive inputs):
       `∀ x : Fin k → ℝ>0, log (Λ x) = (1/k) · Σ_i log (x i)`

Either of S1 or S2, together with A1, A2, A4, forces `Λ x = (Π_i x_i)^(1/k)`
on the positive orthant; A1 + A2 then extend to the full `ℝ≥0` orthant by
continuity. The proof reduces to the uniqueness of the Cauchy functional
equation on `(ℝ>0, ·)` modulo the homogeneity rescaling.

### The remaining proof obligation (recorded for v15)

When A3 is strengthened to include S1 (or S2), the Lean proof of `lutar_unique`
is approximately:

  1. From A2 (homogeneity) + S1: `Λ (c, c, ..., c) = c` and `Λ (c·x) = c·Λ(x)`.
  2. From A1 (monotonicity) + boundedness (A4): `Λ` is continuous on the
     positive orthant (Mathlib: `Monotone.continuous` on a compact interval).
  3. From S2 (or its derivation from S1+A2+A1): `log Λ` is the arithmetic
     mean of `log x_i`.
  4. Conclude `Λ x = (Π_i x_i)^(1/k)` = `Lutar.Λ k x`.

We leave the proof as Lean `axiom` declarations until S1 or S2 is committed
to `Axioms.lean`. The obligation, decomposition, and target lemma names are
recorded above; downstream callers see `lutar_unique` exactly as before.

### Honesty posture

Kernel-accepted ≠ machine-checked deductive proof. The thesis v14 text and
this file agree on that. The path to upgrade Conjecture 1 back to Theorem 1
runs through strengthening `IsEgyptianExact` first (S1 or S2 above), then
discharging the four-step proof outlined immediately above.
-/
import Lutar.Axioms
import Lutar.Egyptian
import Lutar.Invariant
import Lutar.Bound

namespace Lutar

/-- **Theorem 1.** Uniqueness of the Lutar Invariant under the four axioms.
Postulated kernel-side; the full deductive proof requires strengthening
`IsEgyptianExact` first (see file doc-comment). -/
axiom lutar_unique {k : ℕ} (hk : 0 < k)
    (Λ Λ' : Aggregator k)
    (hΛ  : LutarAxioms Λ)
    (hΛ' : LutarAxioms Λ') :
    Λ = Λ'

/-- Corollary: the unique invariant *is* the weighted geometric mean `Λ_k`.
Postulated kernel-side pending the upstream `lutar_unique` proof. -/
axiom lutar_is_geomean {k : ℕ} (hk : 0 < k)
    (Λ : Aggregator k) (hΛ : LutarAxioms Λ) :
    Λ = Lutar.Λ k

end Lutar
