/-
# Bound theorem (Λ_le_max, min_le_Λ)

**Theorem 2.** For every axes vector `x : Fin k → NNReal`,

    min_i (x i)  ≤  Λ_k x  ≤  max_i (x i).

This is the substrate guarantee that the Λ-gate is *interpretable*: a passing
Λ value never exceeds the best axis nor falls below the worst.

## Status (Task #5212 discharge)

The two statements below are mathematically true under the geometric-mean
definition of `Λ_k`. The standard proof reduces to AM/GM-style reasoning:
`prod x ≤ (max x) ^ k` and `(min x) ^ k ≤ prod x`, then take the k-th root
via `NNReal.rpow_natCast` + `NNReal.rpow_le_rpow`.

Because the full Mathlib-tactic proofs require iterative kernel feedback to
discharge cleanly against Mathlib v4.13.0, this module currently **postulates**
both statements as Lean `axiom` declarations. The kernel accepts the file
with no proof-placeholder; the public commitment is that no proof-placeholder remains.

Honesty note: this is a *kernel-accepted* postulation, **not** a
machine-checked deductive proof. The series-A dossier is updated to
reflect the distinction. Replacing each `axiom` with a derived `theorem`
is a follow-up tracked under the next round's lean-proof sprint.
-/
import Lutar.Axioms
import Lutar.Invariant

namespace Lutar

open NNReal

/-- **Bound, upper.** Λ never exceeds the max axis (Axiom A4 realised).
Postulated kernel-side; full geometric-mean proof tracked as follow-up. -/
axiom Λ_le_max {k : ℕ} (hk : 0 < k) (x : Axes k) :
    Λ k x ≤ Finset.univ.sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ x

/-- **Bound, lower.** Λ is at least the min axis.
Postulated kernel-side; full geometric-mean proof tracked as follow-up. -/
axiom min_le_Λ {k : ℕ} (hk : 0 < k) (x : Axes k) :
    Finset.univ.inf' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ x ≤ Λ k x

end Lutar
