/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave9/TimeUniformPACBayes.lean — PB1: time-uniform PAC-Bayes via Ville

The "unified recipe" of Chugg–Wang–Ramdas (arXiv:2302.03421) derives PAC-Bayes
generalization bounds that hold at ALL stopping times by combining a NONNEGATIVE
SUPERMARTINGALE (an e-process), a mixture / Donsker–Varadhan change-of-measure
step, and VILLE'S INEQUALITY. We machine-check the FINAL ASSEMBLY step of that
recipe over the Ville bound we proved in `Lutar/Wave9/Ville.lean`:

  if the PAC-Bayes "evidence process" `Eₜ` is a nonnegative supermartingale with
  `𝔼[E₀] ≤ 1`, then with probability `≥ 1 - δ` the evidence stays below `1/δ`
  AT A FIXED TIME (and, under the maximal-inequality ROADMAP extension, at all
  times), which — re-expressed through the Donsker–Varadhan / Gibbs inequality —
  is exactly the statement that the posterior risk stays within the empirical
  risk plus the PAC-Bayes complexity term.

We prove the assembly (Ville ⟹ confidence ⟹ risk envelope) RIGOROUSLY and leave
the analytic Donsker–Varadhan variational equality and the supremum-over-time
upgrade as the documented ROADMAP (Mathlib lacks both the DV identity and a
supermartingale maximal inequality). We do NOT fabricate those steps.

## What is proven
- `pac_bayes_confidence` — Ville assembly: a nonnegative PAC-Bayes evidence
  supermartingale `E` with `∫ E 0 ≤ 1` satisfies, at fixed time `n` and level
  `δ ∈ (0,1]`, `(μ {ω | 1/δ ≤ E n ω}).toReal ≤ δ`: the bad ("evidence too large")
  event has probability `≤ δ`.
- `pac_bayes_risk_envelope` — re-expression: GIVEN the change-of-measure bridge
  `riskGap ≤ complexity` on the good event (the Donsker–Varadhan / Gibbs step,
  taken as the hypothesis `hbridge` exactly as the recipe's modeling
  obligation), the posterior risk obeys the PAC-Bayes envelope
  `risk ≤ empiricalRisk + complexity` off a probability-`≤ δ` set.

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave9`) — NOT in the LOCKED v11 baseline. Locked-proven
  stays exactly 5 {F1,F11,F12,F18,F19}. Λ untouched (Conjecture 1).
- Known-theorem formalization (Chugg–Wang–Ramdas unified PAC-Bayes recipe). We
  prove the VILLE-ASSEMBLY core; the Donsker–Varadhan variational identity and
  the supremum-over-all-time (true time-uniform) step are ROADMAP, taken as
  explicit hypotheses where used. This matches the PB1 risk note: the guarantee
  is a high-probability inequality UNDER the stated boundedness/process
  assumptions.
- Reuses `Lutar.Wave9.Ville` (no new declared axiom, no sorry).

## Citations
- Chugg, Wang, Ramdas, "A unified recipe for deriving (time-uniform) PAC-Bayes
  bounds", arXiv:2302.03421: https://arxiv.org/abs/2302.03421
- Ville's inequality / nonnegative supermartingales (see Lutar/Wave9/Ville.lean).

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/
import Lutar.Wave9.Ville

open MeasureTheory ProbabilityTheory

namespace Lutar.Wave9.TimeUniformPACBayes

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
variable {ℱ : Filtration ℕ m0}

/-- **PB1 confidence (Ville assembly).** If the PAC-Bayes evidence process `E` is
a nonnegative supermartingale normalized by `∫ E 0 ∂μ ≤ 1`, then for confidence
level `δ ∈ (0,1]` the event "evidence reaches `1/δ`" at fixed time `n` has
probability at most `δ`. Direct from `Lutar.Wave9.Ville.ville_fixed_time`. -/
theorem pac_bayes_confidence [SigmaFiniteFiltration μ ℱ]
    {E : ℕ → Ω → ℝ} (hE : Supermartingale E ℱ μ)
    (h0 : ∫ ω, E 0 ω ∂μ ≤ 1) (n : ℕ) (hnonneg : 0 ≤ᵐ[μ] E n)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (μ {ω | 1 / δ ≤ E n ω}).toReal ≤ δ :=
  Lutar.Wave9.Ville.ville_fixed_time hE h0 n hnonneg hδ0

/-- **PB1 risk envelope.** Packaged time-uniform-style PAC-Bayes statement. The
posterior `risk`, `empiricalRisk`, and PAC-Bayes `complexity` are real-valued
summaries; `E` is the evidence supermartingale. GIVEN the Donsker–Varadhan /
Gibbs change-of-measure BRIDGE `hbridge` (the recipe's modeling step: on the
"evidence small" good event the risk gap is controlled by the complexity term),
the PAC-Bayes envelope `risk ≤ empiricalRisk + complexity` holds OFF a set of
probability at most `δ`. -/
theorem pac_bayes_risk_envelope [SigmaFiniteFiltration μ ℱ]
    {E : ℕ → Ω → ℝ} (hE : Supermartingale E ℱ μ)
    (h0 : ∫ ω, E 0 ω ∂μ ≤ 1) (n : ℕ) (hnonneg : 0 ≤ᵐ[μ] E n)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (risk empiricalRisk complexity : Ω → ℝ)
    (hbridge : ∀ ω, E n ω < 1 / δ →
      risk ω ≤ empiricalRisk ω + complexity ω) :
    (μ {ω | 1 / δ ≤ E n ω}).toReal ≤ δ ∧
    (∀ ω, ω ∉ {ω | 1 / δ ≤ E n ω} →
      risk ω ≤ empiricalRisk ω + complexity ω) := by
  refine ⟨pac_bayes_confidence hE h0 n hnonneg hδ0 hδ1, ?_⟩
  intro ω hω
  -- ω is in the GOOD event: ¬ (1/δ ≤ E n ω), i.e. E n ω < 1/δ.
  have hlt : E n ω < 1 / δ := by
    simp only [Set.mem_setOf_eq, not_le] at hω
    exact hω
  exact hbridge ω hlt

#print axioms pac_bayes_confidence
#print axioms pac_bayes_risk_envelope

/-
## ROADMAP (intentionally NOT stated as proven theorems)

1. `donsker_varadhan` : the variational identity
       𝔼_Q[f] - KL(Q‖P) ≤ log 𝔼_P[exp f]
   that turns the `hbridge` hypothesis above into a DERIVED fact. Mathlib has no
   Donsker–Varadhan / Gibbs variational principle for general measures yet.
2. `pac_bayes_time_uniform` : the SUPREMUM-over-all-time form
       μ {ω | ∃ n, 1/δ ≤ E n ω} ≤ δ ,
   the genuine anytime-valid guarantee, needing a supermartingale maximal
   inequality (see the ROADMAP note in Lutar/Wave9/Ville.lean).
-/

end Lutar.Wave9.TimeUniformPACBayes
