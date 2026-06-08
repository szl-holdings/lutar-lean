/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 15 — CF-22: KL divergence non-negativity ON THE SIMPLEX (conditional repair of DPO)

The in-tree DPO axiom `Lutar.DPOFeasibility.klDivergence_nonneg` is honestly flagged
**FALSE-as-stated**: `PolicyParam n = Fin n → ℝ` carries NO normalisation, so for general
(even negative) coordinates `∑ᵢ pᵢ · log(pᵢ / qᵢ)` is NOT non-negative. (E.g. `p = q = (2,2)`
gives `∑ = 0`, but `p = (4,0), q = (1,1)` with the `log 0 = 0` convention can be made negative;
more fundamentally negative coordinates break the log-sum proof.)

This file proves the **correctly-stated CONDITIONAL theorem**: with the explicit probability-
simplex hypotheses
  (i)   `∀ i, 0 < p i`     (strict positivity — interior of the simplex),
  (ii)  `∀ i, 0 < q i`,
  (iii) `∑ i, p i = 1`,
  (iv)  `∑ i, q i = 1`,
KL is non-negative. It is a DIRECT COROLLARY of Wave14 CF-21 `gibbs_inequality`
(Cover–Thomas Thm 2.6.3), instantiated at `s = Finset.univ`, with the equal-mass premise
`∑ p = ∑ q` discharged from `∑ p = 1 = ∑ q`.

## What is PROVEN here (no sorry / NO new axiom)
* `klDivergenceForm` — the discrete KL form `∑ᵢ pᵢ · log(pᵢ / qᵢ)`, definitionally equal to
  `Lutar.DPOFeasibility.klDivergence` (which unfolds `axisScore mu i = mu i`).
* `klDivergence_nonneg_simplex` — `0 ≤ ∑ᵢ pᵢ · log(pᵢ / qᵢ)` under (i)–(iv).
* `klDivergence_nonneg_simplex_pmf` — the same with the equal-mass form
  `∑ p = ∑ q` in place of the two `= 1` hypotheses (most general; the `=1` version is a corollary).
* `dpo_klDivergence_nonneg_on_simplex` — restated in the DPO file's OWN `klDivergence` symbol,
  showing the FALSE-as-stated axiom becomes a THEOREM once the simplex hypothesis is supplied.

## Honesty / scope (philosophers' check)
- This is a **NEW CONDITIONAL THEOREM**, NOT a closure of the unconditional axiom. The axiom
  `DPOFeasibility.klDivergence_nonneg` (no hypotheses) stays FALSE-as-stated and is UNTOUCHED in
  the baseline file (its axiom token is unchanged; this companion neither edits nor removes it).
- The hypotheses are genuine, checkable constraints (the probability simplex), not a tautological
  stub: dropping any of (i)–(iv) makes the conclusion false, and the proof genuinely consumes the
  equal-mass constraint via `gibbs_inequality`. No false-as-stated lemma is introduced.
- EXPERIMENTAL companion (`Lutar/Wave15/`). Locked-proven set unchanged. NO new axiom; NO sorry.

## References
- Gibbs, J.W. (1902). *Elementary Principles in Statistical Mechanics*, Yale Univ. Press. Ch. XI.
- Kullback, S. & Leibler, R.A. (1951). *Ann. Math. Statist.* 22(1):79–86.
- Cover, T.M. & Thomas, J.A. (2006). *Elements of Information Theory*, 2nd ed., Wiley.
  Thm 2.6.3 (Gibbs / KL ≥ 0 on the simplex). ISBN 978-0-471-24195-9.
- Wave14 CF-21: `Lutar.Wave14.gibbs_inequality` (log-sum / Gibbs core).

Signed-off-by: SZL CTO <cto@szl-holdings.com>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/
import Lutar.Wave14.LogSumInequality
import Lutar.DPOFeasibility
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Lutar.Wave15

open Real Finset BigOperators

/-- The discrete KL form `∑ᵢ pᵢ · log(pᵢ / qᵢ)` over `Fin n`. Definitionally equal to the
    DPO file's `klDivergence` (which is `∑ᵢ axisScore p i · log(axisScore p i / axisScore q i)`
    with `axisScore p i = p i`). -/
noncomputable def klDivergenceForm {n : ℕ} (p q : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, p i * Real.log (p i / q i)

/-- **CF-22 (general / equal-mass form).** Gibbs' inequality on the simplex interior, equal-mass
    premise. For strictly-positive `p, q : Fin n → ℝ` with `∑ p = ∑ q`,
      `0 ≤ ∑ᵢ pᵢ · log(pᵢ / qᵢ)`.
    Direct instantiation of Wave14 `gibbs_inequality` at `s = Finset.univ`. -/
theorem klDivergence_nonneg_simplex_pmf {n : ℕ} (p q : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hmass : ∑ i : Fin n, p i = ∑ i : Fin n, q i) :
    0 ≤ klDivergenceForm p q := by
  unfold klDivergenceForm
  exact Lutar.Wave14.gibbs_inequality Finset.univ p q
    (fun i _ => hp i) (fun i _ => hq i) hmass

/-- **CF-22 (simplex form, the DPO repair).** For probability vectors `p, q` in the interior
    of the simplex (`0 < pᵢ`, `0 < qᵢ`, `∑ p = 1`, `∑ q = 1`),
      `0 ≤ ∑ᵢ pᵢ · log(pᵢ / qᵢ)`.
    Corollary of `klDivergence_nonneg_simplex_pmf` with `∑ p = 1 = ∑ q`. -/
theorem klDivergence_nonneg_simplex {n : ℕ} (p q : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hpsum : ∑ i : Fin n, p i = 1) (hqsum : ∑ i : Fin n, q i = 1) :
    0 ≤ klDivergenceForm p q :=
  klDivergence_nonneg_simplex_pmf p q hp hq (by rw [hpsum, hqsum])

/-- **CF-22 stated in the DPO file's OWN symbol.** The in-tree axiom
    `Lutar.DPOFeasibility.klDivergence_nonneg` (no hypotheses, FALSE-as-stated) becomes a genuine
    THEOREM once the probability-simplex hypothesis is supplied. This does NOT edit or discharge
    the baseline axiom; it exhibits the conditional repair. -/
theorem dpo_klDivergence_nonneg_on_simplex {n : ℕ}
    (p q : Lutar.DPOFeasibility.PolicyParam n)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hpsum : ∑ i : Fin n, p i = 1) (hqsum : ∑ i : Fin n, q i = 1) :
    0 ≤ Lutar.DPOFeasibility.klDivergence p q := by
  have h := klDivergence_nonneg_simplex p q hp hq hpsum hqsum
  unfold klDivergenceForm at h
  -- klDivergence unfolds to the same sum (axisScore p i = p i definitionally)
  unfold Lutar.DPOFeasibility.klDivergence Lutar.DPOFeasibility.axisScore
  exact h

end Lutar.Wave15
