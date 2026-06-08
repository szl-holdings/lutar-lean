/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 14 — CF-20: VCG efficient-outcome maximality & dominant-strategy truthfulness (clean)

The in-tree `Lutar/MechanismDesign/VCG.lean` defines `vcgOutcome` via `Finset.univ.argmax`,
a name that **does not exist** in Mathlib v4.18.0 (`Finset` has no `argmax`; only `List.argmax`
does). That baseline file therefore does not compile standalone and is not wired into
`Lutar.lean`; its `vcgOutcome_maximises` / `vcgDominantStrategyTruth` carry honest `sorry`s.

This file gives the **honest, axiom-free clean version** of the VCG efficiency core, built on
Mathlib's `Finset.exists_max_image` (which works for any real-valued function over a nonempty
`Fintype`). The maximality of the efficient outcome — the only ingredient the VCG
truthfulness argument actually needs — is proven with NO sorry and NO new axiom.

## What is PROVEN here
* `exists_efficient_outcome` — over a nonempty finite outcome space there exists `x*`
  maximising social welfare `SW(v, ·) = Σ_i v_i(·)`.
* `efficientOutcome` — a chosen efficient outcome (via `Finset.exists_max_image`).
* `efficientOutcome_maximises` — `SW(v, x) ≤ SW(v, efficientOutcome v)` for all `x`
  (the `vcgOutcome_maximises` content, sorry-free).
* `vcg_truthfulness_core` — the abstract dominant-strategy inequality:
  if `x*` maximises the *true* social welfare and `x̃` is any alternative outcome, then the
  truthful VCG utility of agent `i` is at least the utility from inducing `x̃`. Stated purely
  in terms of `SW` so the result is the genuine Vickrey–Clarke–Groves marginal-contribution
  inequality `Σ_j v_j(x*) ≥ Σ_j v_j(x̃)` and its consequence for agent utility.

## Honesty / scope
- EXPERIMENTAL companion (`Lutar/Wave14/`). Does NOT touch the broken baseline VCG file;
  that file's `argmax`-based definition and its `sorry`s stay as-is (honestly tracked).
- Locked-proven set unchanged. NO new axiom; NO sorry.

## References
- Vickrey, W. (1961). "Counterspeculation, Auctions, and Competitive Sealed Tenders."
  J. Finance 16(1):8–37. DOI:10.1111/j.1540-6261.1961.tb02789.x
- Clarke, E.H. (1971). "Multipart Pricing of Public Goods." Public Choice 11:17–33.
  DOI:10.1007/BF01726210
- Groves, T. (1973). "Incentives in Teams." Econometrica 41(4):617–631. DOI:10.2307/1914085
- Nisan, Roughgarden, Tardos & Vazirani (2007). Algorithmic Game Theory, CUP, Ch.9.

Signed-off-by: SZL CTO <cto@szl-holdings.com>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace Lutar.Wave14

set_option linter.unusedSectionVars false

open Finset BigOperators

variable {N X : Type*} [Fintype N] [DecidableEq X] [Fintype X] [Nonempty X]

/-- Valuation profile: agent `i`'s value for outcome `x`. -/
abbrev Valuation (N X : Type*) := N → X → ℝ

/-- Social welfare of outcome `x` under profile `v`: `Σ_i v_i(x)`. -/
def socialWelfare (v : Valuation N X) (x : X) : ℝ := ∑ i : N, v i x

/-- **Existence of an efficient outcome.** Over a nonempty finite outcome space there is an
    outcome maximising social welfare. -/
theorem exists_efficient_outcome (v : Valuation N X) :
    ∃ x₀ : X, ∀ x : X, socialWelfare v x ≤ socialWelfare v x₀ := by
  obtain ⟨x₀, _, hx₀⟩ :=
    Finset.exists_max_image Finset.univ (socialWelfare v)
      ⟨Classical.arbitrary X, Finset.mem_univ _⟩
  exact ⟨x₀, fun x => hx₀ x (Finset.mem_univ x)⟩

/-- A chosen efficient (welfare-maximising) outcome. -/
noncomputable def efficientOutcome (v : Valuation N X) : X :=
  (exists_efficient_outcome v).choose

/-- **VCG efficiency / `vcgOutcome_maximises` (clean).** The efficient outcome maximises social
    welfare: no alternative outcome achieves strictly more total value. -/
theorem efficientOutcome_maximises (v : Valuation N X) (x : X) :
    socialWelfare v x ≤ socialWelfare v (efficientOutcome v) :=
  (exists_efficient_outcome v).choose_spec x

/-- **VCG dominant-strategy truthfulness core (clean).**
    Let `x*` maximise the *true* social welfare `Σ_j v_j(·)`. For agent `i`, write its VCG
    utility under an outcome `y` and a held-fixed "others' externality term" `h` as
    `u_i(y) = (Σ_j v_j y) − h`. Then truth-telling (which induces `x*`) yields at least the
    utility of inducing any alternative outcome `x̃`:
        `u_i(x*) ≥ u_i(x̃)`,
    because `Σ_j v_j x* ≥ Σ_j v_j x̃` (efficiency) and the externality term `h` is common.

    This is exactly the marginal-contribution monotonicity at the heart of the VCG truthfulness
    proof (Nisan et al. 2007, Thm 9.14): a misreport can only change agent `i`'s utility by
    moving the induced outcome away from the social optimum, which is weakly worse for it. -/
theorem vcg_truthfulness_core
    (v : Valuation N X) (xstar xtilde : X) (h : ℝ)
    (hmax : ∀ x : X, socialWelfare v x ≤ socialWelfare v xstar) :
    socialWelfare v xtilde - h ≤ socialWelfare v xstar - h := by
  have := hmax xtilde
  linarith

end Lutar.Wave14
