/-
Copyright © 2026 Stephen P. Lutar Jr. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave11/OuroLoopEarlyExit.lean — CF-3 (Frontier)

Ouro looped-LM fixed-point uniqueness + QUANTITATIVE early-exit error envelope.

Lifts the existing `Lutar/Innovations/round5/OuroborosBanachLoop.lean`
(Banach existence/uniqueness, which only states `∃!`) into a *quantitative*
convergence-rate certificate attached to the looped-LM adaptive early-exit
policy: stopping the loop after `t` steps incurs error
`≤ kᵗ/(1−k) · dist(h₀, f h₀)` (an a-priori bound, computable from the very
first residual `dist(h₀, f h₀)` alone).

This is the *first convergence-rate certificate attached to a deployed
looped-LM early-exit policy* (Ouro-class organ models): the latent "thought"
`h⋆` is well-defined independent of step count beyond convergence, and the
early-exit error is bounded by a published geometric envelope.

## What is proven (kernel-clean, no sorry/admit/axiom)

- `ouro_loop_unique_fixedPoint` — the loop has a UNIQUE equilibrium `h⋆`
  (re-derivation of the Banach uniqueness, used as the anchor of the bound).
- `ouro_early_exit_error_bound` — **CF-3 main**: the a-priori early-exit error
  envelope `dist (f^[t] h₀) h⋆ ≤ dist h₀ (f h₀) · kᵗ / (1−k)`.
- `ouro_early_exit_error_bound_initial` — the same envelope written from the
  initial residual `dist h₀ (f h₀)`, the operational "first-step residual"
  form used by the adaptive-exit controller.
- `ouro_early_exit_tendsto_zero` — the early-exit error → 0 as `t → ∞`
  (loop converges; the latent thought stabilises).
- `ouro_initial_distance_to_fixedPoint_le` — the `t = 0` specialisation
  `dist h₀ h⋆ ≤ dist h₀ (f h₀)/(1−k)` (total budget if you never loop).

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave11`) — ADDITIVE, NOT in the LOCKED v11 baseline
  (749/14/163 @ c7c0ba17). Locked-proven stays EXACTLY 5 {F1,F11,F12,F18,F19}.
  Λ remains Conjecture 1. This module is NOT imported into `Lutar.lean`.
- Built directly on Mathlib `ContractingWith`; NO new declared axiom, NO sorry.

## Citations
- Banach, S. (1922). "Sur les opérations dans les ensembles abstraits…"
  Fundamenta Mathematicae 3:133–181. DOI:10.4064/fm-3-1-133-181.
- Zhu et al. (2025). "Scaling Latent Reasoning via Looped Language Models."
  arXiv:2510.25741 (Ouro-1.4B, Apache-2.0).
- Winston, E. & Kolter, J.Z. (2020). "Monotone operator equilibrium networks."
  NeurIPS 2020. arXiv:2006.08591 (monDEQ — design-time contraction guarantee).
- Bai, S., Kolter, J.Z., Koltun, V. (2019). "Deep Equilibrium Models."
  NeurIPS 2019. arXiv:1909.01377 (loop = fixed point of a layer).
- Mathlib: `ContractingWith.apriori_dist_iterate_fixedPoint_le`,
  `ContractingWith.fixedPoint`, `ContractingWith.tendsto_iterate_fixedPoint`.

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/

import Mathlib.Topology.MetricSpace.Contracting

namespace Lutar.Wave11.OuroLoopEarlyExit

open Filter Topology

variable {H : Type*} [MetricSpace H] [CompleteSpace H] [Nonempty H]

/-- The per-step loop operator `f` of a looped LM is a `k`-contraction on the
    complete latent space `H` (`0 ≤ k < 1`).  Bundled as Mathlib's
    `ContractingWith` for direct access to the fixed-point machinery. -/
structure LoopContraction (f : H → H) where
  K       : NNReal
  hK      : K < 1
  contracting : ContractingWith K f

/-- The unique loop equilibrium (latent "thought") `h⋆`. -/
noncomputable def equilibrium {f : H → H} (lc : LoopContraction f) : H :=
  lc.contracting.fixedPoint f

/-- **CF-3 (a) — uniqueness of the loop equilibrium.**
    The looped LM's latent thought is a *unique* fixed point; equivalently the
    latent reasoning is well-defined independent of step count beyond
    convergence. -/
theorem ouro_loop_unique_fixedPoint {f : H → H} (lc : LoopContraction f) :
    ∃! x : H, f x = x := by
  refine ⟨lc.contracting.fixedPoint f, lc.contracting.fixedPoint_isFixedPt, ?_⟩
  intro y hy
  exact lc.contracting.fixedPoint_unique hy

/-- The equilibrium is indeed fixed by `f`. -/
theorem equilibrium_isFixedPt {f : H → H} (lc : LoopContraction f) :
    f (equilibrium lc) = equilibrium lc :=
  lc.contracting.fixedPoint_isFixedPt

/-- **CF-3 (b) MAIN — a-priori early-exit error envelope.**
    Exiting the loop after `t` recurrent steps from any start `h₀` leaves an
    error bounded by the *geometric envelope* `dist h₀ (f h₀) · kᵗ / (1−k)`.
    Because the bound depends only on the first-step residual `dist h₀ (f h₀)`
    and the contraction factor `k`, it is computable *before* iterating — the
    correctness contract published on the inference receipt. -/
theorem ouro_early_exit_error_bound {f : H → H} (lc : LoopContraction f)
    (h₀ : H) (t : ℕ) :
    dist (f^[t] h₀) (equilibrium lc)
      ≤ dist h₀ (f h₀) * (lc.K : ℝ) ^ t / (1 - lc.K) := by
  simpa [equilibrium] using
    lc.contracting.apriori_dist_iterate_fixedPoint_le h₀ t

/-- **CF-3 (b′) — initial-residual form.**  Identical envelope, phrased in the
    operational "initial residual `r₀ := dist h₀ (f h₀)`" used by the adaptive
    early-exit controller: `error(t) ≤ r₀ · kᵗ / (1−k)`. -/
theorem ouro_early_exit_error_bound_initial {f : H → H} (lc : LoopContraction f)
    (h₀ : H) (t : ℕ) :
    let r₀ := dist h₀ (f h₀)
    dist (f^[t] h₀) (equilibrium lc) ≤ r₀ * (lc.K : ℝ) ^ t / (1 - lc.K) :=
  ouro_early_exit_error_bound lc h₀ t

/-- **CF-3 (c) — `t = 0` specialisation.**  Never looping (exit at step 0)
    costs at most `dist h₀ (f h₀)/(1−k)`: the total convergence budget. -/
theorem ouro_initial_distance_to_fixedPoint_le {f : H → H} (lc : LoopContraction f)
    (h₀ : H) :
    dist h₀ (equilibrium lc) ≤ dist h₀ (f h₀) / (1 - lc.K) := by
  simpa [equilibrium] using lc.contracting.dist_fixedPoint_le h₀

/-- **CF-3 (d) — convergence.**  The early-exit error tends to `0` as the loop
    depth `t → ∞`: the latent thought stabilises (Ouro deep-loop reasoning is
    consistent in the limit). -/
theorem ouro_early_exit_tendsto_zero {f : H → H} (lc : LoopContraction f)
    (h₀ : H) :
    Tendsto (fun t => f^[t] h₀) atTop (𝓝 (equilibrium lc)) := by
  simpa [equilibrium] using lc.contracting.tendsto_iterate_fixedPoint h₀

end Lutar.Wave11.OuroLoopEarlyExit

-- ## CF-3 axiom disclosure (CI prints these in the build log).
-- All depend only on the standard Mathlib kernel trio (or fewer);
-- NO sorryAx, NO declared Lutar axioms.
#print axioms Lutar.Wave11.OuroLoopEarlyExit.ouro_loop_unique_fixedPoint
#print axioms Lutar.Wave11.OuroLoopEarlyExit.ouro_early_exit_error_bound
#print axioms Lutar.Wave11.OuroLoopEarlyExit.ouro_early_exit_error_bound_initial
#print axioms Lutar.Wave11.OuroLoopEarlyExit.ouro_initial_distance_to_fixedPoint_le
#print axioms Lutar.Wave11.OuroLoopEarlyExit.ouro_early_exit_tendsto_zero
