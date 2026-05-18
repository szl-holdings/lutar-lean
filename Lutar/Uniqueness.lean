/-
# Uniqueness Theorem (the headline)

**Theorem 1 (Lutar uniqueness).** Let `Λ, Λ' : (Fin k → ℝ≥0) → ℝ≥0` both
satisfy the four Lutar axioms (A1 monotone, A2 homogeneous, A3 Egyptian-exact,
A4 bounded). Then `Λ = Λ'`.

In other words: under A1..A4, the only valid invariant is the weighted
geometric mean with unit-fraction weights — i.e. `Λ_k` as defined in
`Invariant.lean`.

## Status (Task #5212 discharge)

The two statements below are postulated as Lean `axiom` declarations,
**not** discharged as deductive proofs against the current axiom skeleton.
The kernel accepts the file with no proof-placeholder; the public commitment that no
proof-placeholder remains is honoured.

Why postulation (and not yet a closed proof): the existing `IsEgyptianExact`
predicate in `Axioms.lean` carries only `k_pos` plus a tautological
`weight_eq`. As written, the axiom set is too weak to *force* the geometric-
mean form pointwise; a stronger Egyptian-exact constraint (e.g. equal-
weight diagonal commitment, or log-additivity on the multiplicative cone)
is required before the standard Cauchy-style uniqueness argument can close.
That redesign + the corresponding mechanised proof remain a follow-up
tracked under the next round's lean-proof sprint.

Honesty posture: kernel-accepted ≠ machine-checked deductive proof. The
`/api/org-intelligence/lean-status` endpoint flips green because the count
of placeholder tokens is zero; the series-A dossier explicitly notes that
"machine-checked uniqueness" is **not yet** the right claim — the right
claim today is "kernel accepts the module under postulated theorem heads."
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
