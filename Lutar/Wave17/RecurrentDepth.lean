/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 17 — CF-28: recurrent-depth contraction amplification (axiom-free)

## Provenance / license doctrine (binding)

Concept mined from **mcleish7/retrofitting-recurrence** ("Teaching Pretrained Language Models to
Think Deeper with Retrofitted Recurrence", McLeish et al. 2025, arXiv:2511.07384), repository
license **Apache-2.0** (verified live via GitHub API).  ADOPT-eligible (permissive); adoption is
**concept-only** — NO code copied; the Lean statements are original facts about iterating a
Lipschitz recurrent block.  NOTICE attribution recorded in this header.

## What recurrent-depth amplification is, mathematically

A recurrent-depth ("looped") model applies a *single shared block* `f` for `r` recurrence steps:
`z ↦ f^[r] z`.  "Thinking deeper" = larger `r`.  The well-posedness/stability fact that justifies
deeper recurrence is that a `K`-Lipschitz block, iterated `r` times, is `Kʳ`-Lipschitz — so for a
*contractive* block (`K < 1`) more recurrence steps **exponentially tighten** the coupling between
trajectories (hence convergence toward the fixed point), and **never loosen** it.  This file
proves exactly that, distinct from the in-tree CF-13 input-Lipschitz equilibrium result.

* `recurrentDepthLipschitz`     — `f` is `K`-Lipschitz ⇒ `f^[r]` is `Kʳ`-Lipschitz.
* `recurrentDepthDistBound`     — `dist (f^[r] x) (f^[r] y) ≤ Kʳ · dist x y`.
* `recurrentDepthEdistBound`    — the extended-distance form (`PseudoEMetricSpace`).
* `recurrentDepthConst_antitone`— for a contraction `K ≤ 1`, the depth-`r` constant `Kʳ` is
                                   **non-increasing** in `r` (more depth ⇒ tighter, never looser).
* `recurrentDepthConst_lt_of_lt`— for a strict contraction `K < 1` and `r ≥ 1`, `Kʳ < 1`
                                   (depth preserves strict contractivity).

## Honesty / scope
- EXPERIMENTAL companion (`Lutar/Wave17/`). NO new axiom; NO sorry. Locked-proven set unchanged.
- This is the contraction-amplification fact, NOT a claim about the trained model's accuracy or a
  convergence rate to a *specific* solution; existence/uniqueness of the recurrent fixed point is
  the separate CF-13 (DEQ) result and the CF-27 monotone-operator result. Distinct content.
- Concept-only adoption; paper cited; SPDX Apache-2.0 verified live.

## References
- McLeish, S., Li, A., Kirchenbauer, J., et al. (2025). *Teaching Pretrained Language Models to
  Think Deeper with Retrofitted Recurrence*. arXiv:2511.07384.  Repo `mcleish7/retrofitting-
  recurrence` (Apache-2.0) — concept-only, no code used.

Signed-off-by: SZL CTO <cto@szl-holdings.com>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Positivity

namespace Lutar.Wave17

open Function

variable {X : Type*}

/-- **Recurrent-depth Lipschitz amplification.** A `K`-Lipschitz recurrent block `f`, iterated
    `r` times, is `Kʳ`-Lipschitz. -/
theorem recurrentDepthLipschitz [PseudoEMetricSpace X] {K : NNReal} {f : X → X}
    (hf : LipschitzWith K f) (r : ℕ) : LipschitzWith (K ^ r) f^[r] :=
  hf.iterate r

/-- **Recurrent-depth distance bound** (metric form):
    `dist (f^[r] x) (f^[r] y) ≤ Kʳ · dist x y`. -/
theorem recurrentDepthDistBound [PseudoMetricSpace X] {K : NNReal} {f : X → X}
    (hf : LipschitzWith K f) (r : ℕ) (x y : X) :
    dist (f^[r] x) (f^[r] y) ≤ (K ^ r : NNReal) * dist x y :=
  (hf.iterate r).dist_le_mul x y

/-- **Recurrent-depth extended-distance bound** (`PseudoEMetricSpace` form). -/
theorem recurrentDepthEdistBound [PseudoEMetricSpace X] {K : NNReal} {f : X → X}
    (hf : LipschitzWith K f) (r : ℕ) (x y : X) :
    edist (f^[r] x) (f^[r] y) ≤ ((K ^ r : NNReal) : ENNReal) * edist x y :=
  (hf.iterate r).edist_le_mul x y

/-- For a contraction `K ≤ 1`, the depth-`r` Lipschitz constant `Kʳ` is **non-increasing** in `r`:
    more recurrence steps never loosen the coupling. -/
theorem recurrentDepthConst_antitone {K : NNReal} (hK : K ≤ 1) :
    Antitone (fun r : ℕ => K ^ r) :=
  fun _ _ hmn => pow_le_pow_of_le_one (zero_le K) hK hmn

/-- For a **strict** contraction `K < 1` and at least one recurrence step (`1 ≤ r`),
    the depth-`r` constant satisfies `Kʳ < 1` — deeper recurrence preserves strict contractivity. -/
theorem recurrentDepthConst_lt_of_lt {K : NNReal} (hK : K < 1) {r : ℕ} (hr : 1 ≤ r) :
    K ^ r < 1 := by
  calc K ^ r ≤ K ^ 1 := pow_le_pow_of_le_one (zero_le K) (le_of_lt hK) hr
    _ = K := pow_one K
    _ < 1 := hK

end Lutar.Wave17
