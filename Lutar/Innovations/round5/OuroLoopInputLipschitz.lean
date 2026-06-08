/-
Copyright © 2026 Stephen P. Lutar Jr. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Innovations/round5/OuroLoopInputLipschitz.lean — CF-13 (Frontier)

DEQ / Ouro fixed-point well-posedness margin: the equilibrium map
`x ↦ z⋆(x)` of a looped/DEQ layer is globally `Lₓ/(1−k)`-Lipschitz in the
input.

This is the orthogonal, stronger companion to the Wave11 CF-3 early-exit
envelope (`Lutar/Wave11/OuroLoopEarlyExit.lean`), which bounds the error in
the *iteration index*. Here we bound the dependence of the equilibrium on the
*input*: for a layer `f : X → H → H` whose per-input slice `f x : H → H` is a
uniform `k`-contraction in the latent state and whose state-wise dependence on
the input is `Lₓ`-Lipschitz, the implicit equilibrium

  `z⋆(x) = f x (z⋆(x))`        (deep-equilibrium / looped-LM fixed point)

exists, is unique, and satisfies

  `dist (z⋆ x) (z⋆ y) ≤ Lₓ / (1 − k) · dist x y`.

So two nearby prompts produce equilibria within `Lₓ/(1−k)·‖Δx‖` — a published
input-sensitivity / well-posedness certificate for latent reasoning.

## What is proven (kernel-clean, no open obligations / no admit / no axiom)

- `equilibrium_isFixedPt` — `z⋆(x)` is a genuine fixed point of `f x`.
- `equilibrium_unique` — uniqueness of the equilibrium per input.
- `equilibrium_dist_le` — **CF-13 main pointwise**: the two-input equilibrium
  bound `dist (z⋆ x) (z⋆ y) ≤ Lₓ/(1−k) · dist x y`.
- `equilibrium_lipschitz` — the global statement `LipschitzWith (Lₓ/(1−k))`
  of the equilibrium map `x ↦ z⋆(x)` (the deployable well-posedness badge).

## Honesty / scope
- EXPERIMENTAL. ADDITIVE, NOT part of the LOCKED v11 baseline (749/14/163 @
  c7c0ba17). Locked-proven stays EXACTLY 5 {F1,F11,F12,F18,F19}. Λ (F23)
  remains Conjecture 1 unconditionally. This module is NOT a Λ-uniqueness claim.
- Built directly on Mathlib `ContractingWith`; NO new declared axiom, no open
  obligation. `#print axioms` (below) shows only the standard Mathlib kernel.

## Citations
- Banach, S. (1922). "Sur les opérations dans les ensembles abstraits…"
  Fundamenta Mathematicae 3:133–181. DOI:10.4064/fm-3-1-133-181.
- Bai, S., Kolter, J.Z., Koltun, V. (2019). "Deep Equilibrium Models."
  NeurIPS 2019. arXiv:1909.01377 (loop = fixed point of a layer).
- Winston, E. & Kolter, J.Z. (2020). "Monotone operator equilibrium networks."
  NeurIPS 2020. arXiv:2006.08591 (design-time contraction guarantee; concepts
  only, no vendored code).
- Zhu et al. (2025). "Scaling Latent Reasoning via Looped Language Models."
  arXiv:2510.25741 (Ouro-1.4B, Apache-2.0).
- Mathlib: `ContractingWith.fixedPoint`, `ContractingWith.fixedPoint_isFixedPt`,
  `ContractingWith.fixedPoint_unique`,
  `ContractingWith.dist_fixedPoint_fixedPoint_of_dist_le'`, `LipschitzWith`.

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/

import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Lipschitz

namespace Lutar.Innovations.Round5.InputLipschitz

open Function

variable {X : Type*} [MetricSpace X]
variable {H : Type*} [MetricSpace H] [CompleteSpace H] [Nonempty H]

/-- A parametric looped/DEQ layer `f : X → H → H` whose per-input slice `f x`
    is a uniform `K`-contraction in the latent state, and whose state-wise
    dependence on the input is globally `Lx`-Lipschitz. -/
structure InputContraction (f : X → H → H) where
  /-- contraction factor `k`, shared across inputs. -/
  K  : NNReal
  /-- input-Lipschitz constant `Lₓ`. -/
  Lx : NNReal
  /-- strict contraction `k < 1`. -/
  hK : K < 1
  /-- each input slice `f x` is `K`-Lipschitz in the latent state. -/
  hcontract : ∀ x : X, LipschitzWith K (f x)
  /-- the layer is `Lₓ`-Lipschitz in the input, uniformly over latent states. -/
  hinput : ∀ (x y : X) (z : H), dist (f x z) (f y z) ≤ (Lx : ℝ) * dist x y

/-- The per-input slice bundled as Mathlib `ContractingWith`. -/
theorem InputContraction.contractingWith {f : X → H → H} (ic : InputContraction f)
    (x : X) : ContractingWith ic.K (f x) :=
  ⟨ic.hK, ic.hcontract x⟩

/-- The unique latent equilibrium for input `x`: `z⋆(x) = f x (z⋆(x))`. -/
noncomputable def equilibrium {f : X → H → H} (ic : InputContraction f) (x : X) : H :=
  ContractingWith.fixedPoint (f x) (ic.contractingWith x)

/-- **CF-13 (a) — the equilibrium is a genuine fixed point.** -/
theorem equilibrium_isFixedPt {f : X → H → H} (ic : InputContraction f) (x : X) :
    f x (equilibrium ic x) = equilibrium ic x :=
  ContractingWith.fixedPoint_isFixedPt (ic.contractingWith x)

/-- **CF-13 (b) — uniqueness of the equilibrium per input.** -/
theorem equilibrium_unique {f : X → H → H} (ic : InputContraction f) (x : X)
    {y : H} (hy : f x y = y) : y = equilibrium ic x :=
  ContractingWith.fixedPoint_unique (ic.contractingWith x) hy

/-- **CF-13 (c) MAIN (pointwise) — input-Lipschitz well-posedness margin.**
    Two inputs `x, y` yield equilibria within `Lₓ/(1−k)·dist x y`:

      `dist (z⋆ x) (z⋆ y) ≤ Lₓ/(1−k) · dist x y`.

    The constant `Lₓ/(1−k)` blows up as `k → 1` (the loop loses its margin) and
    shrinks with a tighter input-Lipschitz constant — the quantitative
    "small prompt change ⇒ bounded latent change" certificate. -/
theorem equilibrium_dist_le {f : X → H → H} (ic : InputContraction f) (x y : X) :
    dist (equilibrium ic x) (equilibrium ic y)
      ≤ ((ic.Lx : ℝ) / (1 - ic.K)) * dist x y := by
  -- `f x` and `f y` are uniformly `C`-close with `C = Lₓ · dist x y`, both
  -- contractions; Mathlib's two-map fixed-point bound gives `dist ≤ C/(1−k)`.
  have hbound :=
    ContractingWith.dist_fixedPoint_fixedPoint_of_dist_le'
      (ic.contractingWith x) (f y)
      (ContractingWith.fixedPoint_isFixedPt (ic.contractingWith x))
      (ContractingWith.fixedPoint_isFixedPt (ic.contractingWith y))
      (fun z => ic.hinput x y z)
  -- rewrite the abstract fixed points as `equilibrium` and the constant `C/(1−k)`.
  have hrw : dist (equilibrium ic x) (equilibrium ic y)
      ≤ ((ic.Lx : ℝ) * dist x y) / (1 - ic.K) := by
    simpa [equilibrium] using hbound
  -- `(Lₓ·d)/(1−k) = (Lₓ/(1−k))·d`.
  calc dist (equilibrium ic x) (equilibrium ic y)
      ≤ ((ic.Lx : ℝ) * dist x y) / (1 - ic.K) := hrw
    _ = ((ic.Lx : ℝ) / (1 - ic.K)) * dist x y := by ring

/-- **CF-13 (d) GLOBAL — the equilibrium map is `Lₓ/(1−k)`-Lipschitz.**
    The deployable well-posedness badge on the inference receipt:
    `x ↦ z⋆(x)` is globally Lipschitz with the published constant. -/
theorem equilibrium_lipschitz {f : X → H → H} (ic : InputContraction f) :
    LipschitzWith (ic.Lx / (1 - ic.K)) (equilibrium ic) := by
  -- `1 - K` as a nonneg real with `0 < 1 - K` from `K < 1`.
  have hK1 : (ic.K : ℝ) < 1 := by exact_mod_cast ic.hK
  have hden : (0 : ℝ) < 1 - (ic.K : ℝ) := by linarith
  -- the real Lipschitz constant `Lₓ/(1−K)` matches the NNReal coercion.
  have hcoe : ((ic.Lx / (1 - ic.K) : NNReal) : ℝ) = (ic.Lx : ℝ) / (1 - (ic.K : ℝ)) := by
    rw [NNReal.coe_div, NNReal.coe_sub ic.hK.le, NNReal.coe_one]
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [hcoe]
  exact equilibrium_dist_le ic x y

end Lutar.Innovations.Round5.InputLipschitz

-- ## CF-13 axiom disclosure (CI prints these in the build log).
-- All depend only on the standard Mathlib kernel; NO declared Lutar axioms,
-- no open obligations.
#print axioms Lutar.Innovations.Round5.InputLipschitz.equilibrium_isFixedPt
#print axioms Lutar.Innovations.Round5.InputLipschitz.equilibrium_unique
#print axioms Lutar.Innovations.Round5.InputLipschitz.equilibrium_dist_le
#print axioms Lutar.Innovations.Round5.InputLipschitz.equilibrium_lipschitz
