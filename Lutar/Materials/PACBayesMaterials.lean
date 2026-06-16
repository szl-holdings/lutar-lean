/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Materials/PACBayesMaterials.lean

ROADMAP — McAllester PAC-Bayes bound specialized to a MATERIALS regression
risk. McAllester is PROVEN-on-paper [McAllester 1999/2003]; the LEAN proof of
this specialized statement is an OPEN `sorry`, consistent with the
`pac_bayes_mcallester` docstring in szl_formulas.py (PROOF-STATUS: bound
COMPUTATION exact/correct; machine-checked Lean proof of the bound itself is a
tracked SORRY). NOT in locked-8. Backs /api/a11oy/v1/materials/certify.

-------------------------------------------------------------------------------
## Honesty verdict first (doctrine v11)

  * McAllester's PAC-Bayes theorem is a PUBLISHED, peer-reviewed result with a
    human-written proof. What is OPEN here is the MACHINE-CHECKED Lean proof of
    the bound, specialized to a bounded materials-regression loss. That is the
    `sorry` below.
  * The live endpoint /api/a11oy/v1/materials/certify imports the EXISTING
    `pac_bayes_mcallester` from szl_formulas.py and returns the EXACT numeric
    bound + a signed Khipu certificate. The COMPUTATION is correct; only the
    in-Lean proof is roadmap.
  * NOT folded into the locked-8 {F1,F4,F7,F11,F12,F18,F19,F22} @ c7c0ba17.
  * NOT imported by `Lutar.lean` (not in `lake build`); tracked-`sorry` only,
    disclosed in SORRIES.md. Λ = Conjecture 1; Khipu = Conjecture 2.
  * A related but DISTINCT in-corpus statement, `Lutar/PACBayes/PACBayes.lean`
    (TH13, Λ-gate head), is Mathlib-conditional with its own tracked
    obligations. THIS file is the MATERIALS-regression specialization and is
    intentionally minimal and standalone.

## The bound (McAllester form, materials regression)

For a posterior `Q` over predictors of a bounded materials-property risk, with
prior `P`, `n` i.i.d. samples and confidence `δ ∈ (0,1)`, McAllester's bound
states that with probability ≥ 1 − δ over the sample draw:

  R(Q) ≤ Rhat(Q) + sqrt( (KL(Q‖P) + ln(2·sqrt(n)/δ)) / (2·n) )

We package the right-hand side as `mcallesterBound empiricalRisk kl n δ` and
state the (conjectural-in-Lean) bound `populationRisk ≤ mcallesterBound …`.
The slack term is exactly the quantity computed by `pac_bayes_mcallester` in
szl_formulas.py.

## References (real)

  McAllester, D.A. (1999). PAC-Bayesian model averaging. COLT 1999, 164-170.
  McAllester, D.A. (2003). PAC-Bayesian stochastic model selection.
    Machine Learning 51(1), 5-21. DOI: 10.1023/A:1021840411064.
  Catoni, O. (2007). PAC-Bayesian Supervised Classification. IMS Lecture
    Notes Monograph Series 56, Institute of Mathematical Statistics.
  Alquier, P. (2024). User-friendly introduction to PAC-Bayes bounds.
    Foundations and Trends in Machine Learning 17(2), 174-303.
  SZL Materials Frontier Brief (2026): certified-prediction-bound gap #2;
    szl_formulas.py `pac_bayes_mcallester` docstring (proof-status honesty).

Signed-off-by: SZL CTO <cto@szl-holdings.com>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Lutar
namespace Materials

open Real

/-- The McAllester PAC-Bayes upper bound on population risk for a materials
regression problem: empirical risk plus the canonical complexity slack
`sqrt((KL + ln(2√n/δ)) / (2n))`. This is exactly the quantity the live
`pac_bayes_mcallester` computes; it is a closed-form, exactly-computable real. -/
noncomputable def mcallesterBound
    (empiricalRisk kl n delta : ℝ) : ℝ :=
  empiricalRisk + Real.sqrt ((kl + Real.log (2 * Real.sqrt n / delta)) / (2 * n))

/-- **McAllester PAC-Bayes bound, materials-regression specialization.
PROVEN-on-paper; LEAN proof is an OPEN `sorry` — ROADMAP, NOT in locked-8.**

If `populationRisk` is the true (population) materials-property risk of the
posterior `Q`, `empiricalRisk` its empirical risk on `n` i.i.d. samples, `kl`
the KL divergence `KL(Q‖P)` to the prior, and `delta ∈ (0,1)` the confidence
parameter, then (on the high-probability event of measure ≥ 1 − δ) the
population risk is bounded by `mcallesterBound`.

The hypotheses below are the standard regularity assumptions (positive sample
count, confidence in range, non-negative KL, bounded risks in [0,1]); under
them the inequality is McAllester's theorem. The Lean PROOF is tracked-`sorry`:
it requires a sub-Gaussian MGF / Hoeffding step not yet in the pinned Mathlib
(see the `MomentSubGaussian` discussion in Lutar/PACBayes.lean). The bound
COMPUTATION (`mcallesterBound`) is exact and is what the endpoint returns. -/
theorem pac_bayes_materials_bound
    (populationRisk empiricalRisk kl n delta : ℝ)
    (hn : 1 ≤ n)
    (hdelta : 0 < delta ∧ delta < 1)
    (hkl : 0 ≤ kl)
    (hR : 0 ≤ empiricalRisk ∧ empiricalRisk ≤ 1)
    (hPop : 0 ≤ populationRisk ∧ populationRisk ≤ 1) :
    populationRisk ≤ mcallesterBound empiricalRisk kl n delta := by
  -- ROADMAP. McAllester (2003) holds on paper; the machine-checked Lean proof
  -- needs the sub-Gaussian/Hoeffding step absent from pinned Mathlib v4.18.0.
  -- Tracked-`sorry` (NOT in locked-8, NOT in `lake build`). The bound
  -- COMPUTATION `mcallesterBound` is exact and used by /materials/certify.
  sorry

end Materials
end Lutar
