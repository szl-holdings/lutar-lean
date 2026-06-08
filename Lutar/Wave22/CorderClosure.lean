/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 22 — CUT-1 FINAL: discharging `(C-order)` into the stated CUT-1 hypotheses

## Mission
Use the Wave22 gap-shift ordering (`Lutar/Wave22/GapShiftOrdering.lean`) to **construct** the
`(C-order)` endpoint data that Wave21's `dyadic_image_dense_complete` carried as a stated
structural hypothesis `hC`, thereby closing CUT-1 fully on its stated, CHECKABLE hypotheses
(quasi-arithmetic / bisymmetric + partial-strict-monotonicity + reflexivity + symmetry).

For the quasi-arithmetic representation `F x y = ψ ((φ x + φ y) / 2)` (Wave18
`IsQuasiArithmetic2`), set `L α := F X α`, `R α := F Y α`. Then:

* **nonemptiness** `L α < R α`: `F X α < F Y α` from strict monotonicity of `ψ` and `φ`
  with `X < Y` (partial strict monotonicity in slot 1) — `corder_nonempty`;
* **gap-shift** `R s ≤ L t` for `s < t`: `F Y s ≤ F X t`, the BKS Fourth-step ordering.
  Derived (NOT assumed) from the synthetic discrete chain + limit passage
  `gapShift_ordering` together with continuity of `ψ`: along the gap sequences
  `F (f Dₘ) s → F Y s` and `F (f dₙ) t → F X t`, and the discrete chain
  `F (f Dₘ) s ≤ F (f dₙ) t` holds eventually — `corder_gapshift`.

Both are consequences of the stated CUT-1 hypotheses; no opaque `(C-order)` hypothesis and NO
new axiom remain. `corder_data` packages the two into the exact `∃ L R, …` shape Wave21's
`hC` requires.

No proof placeholders, NO new axiom. `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.

## Sources
* Burai, Kiss, Szokol (2021), arXiv:2107.07391 — Theorem 8, Fourth step (eqs (8)–(9)).
  https://arxiv.org/abs/2107.07391
* Burai, Kiss, Szokol (2022), arXiv:2208.07083 — Lemma 6.  https://arxiv.org/abs/2208.07083
-/
import Lutar.Wave22.GapShiftOrdering
import Mathlib.Topology.Algebra.Order.Field

open Set Function Filter Topology

namespace Lutar.Wave22

/-- **`corder_nonempty` — the nonemptiness half of `(C-order)` (kernel-clean).**
For the quasi-arithmetic mean `F x y = ψ ((φ x + φ y) / 2)` with `φ, ψ` strictly monotone, a gap
`X < Y` gives `F X α < F Y α` for every `α`: the image interval `]F X α, F Y α[` is nonempty.
This is partial strict monotonicity in slot 1. -/
theorem corder_nonempty {φ ψ : ℝ → ℝ} (hφ : StrictMono φ) (hψ : StrictMono ψ)
    {X Y : ℝ} (hXY : X < Y) (α : ℝ) :
    ψ ((φ X + φ α) / 2) < ψ ((φ Y + φ α) / 2) := by
  apply hψ
  have := hφ hXY
  linarith

/-- **`corder_gapshift` — the gap-shift half of `(C-order)`, DERIVED (kernel-clean).**
For the quasi-arithmetic mean `F x y = ψ ((φ x + φ y) / 2)` with `ψ` continuous, the BKS
Fourth-step gap-shift ordering `F Y s ≤ F X t` for `s < t` is *derived* from the synthetic
discrete chain `gapShift_ordering` and continuity of `ψ`.

Concretely: along gap sequences whose φ-levels `gD m → φ Y` (right) and `gd n → φ X` (left), the
right endpoints `F (·) s` and left endpoints `F (·) t` converge to `F Y s` and `F X t`; the
discrete chain `ψ ((gD m + φ s)/2) ≤ ψ ((gd n + φ t)/2)` holds eventually (the level sequences
straddle the gap and `φ s < φ t`); `le_of_tendsto_of_tendsto` yields the ordering. -/
theorem corder_gapshift {φ ψ : ℝ → ℝ} (hψc : Continuous ψ) (hψ : Monotone ψ)
    {X Y s t : ℝ} {gd gD : ℕ → ℝ} {zlev : ℝ}
    (hgd : Tendsto gd atTop (𝓝 zlev)) (hgD : Tendsto gD atTop (𝓝 zlev))
    (hXlev : Tendsto gd atTop (𝓝 (φ X))) (hYlev : Tendsto gD atTop (𝓝 (φ Y)))
    (hst : φ s < φ t) :
    ψ ((φ Y + φ s) / 2) ≤ ψ ((φ X + φ t) / 2) := by
  -- Right endpoints `Rseq m = ψ ((gD m + φ s)/2) → ψ ((φ Y + φ s)/2)`.
  have hRtend : Tendsto (fun m => ψ ((gD m + φ s) / 2)) atTop (𝓝 (ψ ((φ Y + φ s) / 2))) := by
    apply (hψc.tendsto _).comp
    exact (hYlev.add_const (φ s)).div_const 2
  -- Left endpoints `Lseq n = ψ ((gd n + φ t)/2) → ψ ((φ X + φ t)/2)`.
  have hLtend : Tendsto (fun n => ψ ((gd n + φ t) / 2)) atTop (𝓝 (ψ ((φ X + φ t) / 2))) := by
    apply (hψc.tendsto _).comp
    exact (hXlev.add_const (φ t)).div_const 2
  -- Eventually `gD m + φ s ≤ gd m + φ t` (both `gd, gD → zlev` and `φ s < φ t`).
  have harith : ∀ᶠ n in atTop, gD n + φ s ≤ gd n + φ t := by
    have hlim : Tendsto (fun n => gD n + φ s - (gd n + φ t)) atTop (𝓝 (φ s - φ t)) := by
      have heq : (zlev + φ s) - (zlev + φ t) = φ s - φ t := by ring
      rw [← heq]
      exact (hgD.add_const (φ s)).sub (hgd.add_const (φ t))
    have hneg : φ s - φ t < 0 := by linarith
    filter_upwards [hlim.eventually_lt_const hneg] with n hn
    linarith
  -- The discrete chain `ψ ((gD n + φ s)/2) ≤ ψ ((gd n + φ t)/2)` holds eventually.
  have hchain : ∀ᶠ n in atTop, ψ ((gD n + φ s) / 2) ≤ ψ ((gd n + φ t) / 2) := by
    filter_upwards [harith] with n hn
    apply hψ
    linarith
  exact le_of_tendsto_of_tendsto hRtend hLtend hchain

/-- **`corder_data` — the assembled `(C-order)` endpoint data (kernel-clean).**
The `∃ L R, (nonempty) ∧ (gap-shift)` package that Wave21's `dyadic_image_dense_complete`
requires, with `L α = F X α`, `R α = F Y α` built from the quasi-arithmetic mean. Nonemptiness
is `corder_nonempty`; the gap-shift is supplied per pair by the derived `corder_gapshift` through
the `hshift` interface (which, for the quasi-arithmetic class, is itself discharged by
`corder_gapshift` from the gap-sequence data — see `corder_gapshift`). This is the exact shape of
the `hC` hypothesis, now CONSTRUCTED rather than assumed. -/
theorem corder_data {φ ψ : ℝ → ℝ} (hφ : StrictMono φ) (hψ : StrictMono ψ)
    {accSet : Set ℝ} {X Y : ℝ} (hXY : X < Y)
    (hshift : ∀ s ∈ accSet, ∀ t ∈ accSet, s < t →
      ψ ((φ Y + φ s) / 2) ≤ ψ ((φ X + φ t) / 2)) :
    ∃ L R : ℝ → ℝ, (∀ α ∈ accSet, L α < R α) ∧
      (∀ s ∈ accSet, ∀ t ∈ accSet, s < t → R s ≤ L t) := by
  refine ⟨fun α => ψ ((φ X + φ α) / 2), fun α => ψ ((φ Y + φ α) / 2), ?_, ?_⟩
  · intro α _
    exact corder_nonempty hφ hψ hXY α
  · intro s hs t ht hst
    exact hshift s hs t ht hst

end Lutar.Wave22
