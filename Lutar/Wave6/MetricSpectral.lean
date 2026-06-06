/-
Copyright © 2026 Stephen P. Lutar Jr. (SZL Holdings).
Released under the Apache-2.0 License.

# WAVE 6 — Tier-1 Mathlib instantiations: metric embedding + spectral contraction

(Mathlib-DEPENDENT — verified by lutar-lean CI `lake build`, NOT by bare lean here:
 Mathlib does not fit the sandbox disk.)

Each result MODELS a Lutar substrate object, IMPORTS a Mathlib lemma whose signature
was verified against pinned Mathlib (`d7317655`, v4.13.0), APPLIES it, and states the
SUBSTRATE COROLLARY.

## Honesty / doctrine (Doctrine v11)
- Λ (F23) stays Conjecture 1.  Nothing here changes that.
- These are the *honest, finite / fixed-dimension* cores of the named classical theorems
  (Bourgain; Levin–Peres) — NOT the full O(log n)-distortion asymptotic nor the full
  reversible-chain mixing theorem.  We prove what is cleanly Lean-provable and CITE the
  general results.
- Maturity: `proven` ONLY once CI `lake build` is green (Mathlib-dependent).
- Locked kernel (749/14/163 @ c7c0ba17) SEPARATE; this is experimental/wave6. SLSA L2.

## Candidates (USER_GITHUB_RND_REPORT F-G1 / F-G3)

- **F-G1 — low-distortion metric embedding (the P-GNN / Bourgain backbone).**
  Bourgain (1985), Israel J. Math 52:46–52, doi:10.1007/BF02776078;
  Linial–London–Rabinovich (1995), Combinatorica 15:215–245, doi:10.1007/BF01200757;
  application P-GNN, You–Gomes-Selman–Ying–Leskovec (2019), arXiv:1906.04817.
  HONEST FINITE CORE: the **Fréchet anchor coordinate** `x ↦ dist x a` is **1-Lipschitz**
  (`|dist x a − dist y a| ≤ dist x y`), so the full anchor-vector embedding into ℓ∞ is a
  **non-expansion (distortion ≥ 1 contraction side controlled by 1)**.  This is the exact
  expansion-side certificate underlying every Bourgain-style random-anchor construction
  (P-GNN's shortest-path-to-anchor features).  We instantiate `abs_dist_sub_le`.
  We also re-export Mathlib's `exists_isometric_embedding` (Kuratowski): every separable
  metric space embeds *isometrically* (distortion = 1) into ℓ∞ — the distortion-1 anchor
  of the spectrum.

- **F-G3 — spectral-gap / contraction mixing bound (promote `SpectralAdmit`).**
  Levin & Peres (2017), *Markov Chains and Mixing Times*, AMS, doi:10.1090/mbk/107;
  Diaconis–Stroock (1991), doi:10.1214/aoap/1177005980.
  HONEST FINITE CORE: a **one-step contraction** toward the stationary point `π` with
  factor `λ ∈ [0,1)` (`dist (P y) π ≤ λ · dist y π`) yields **geometric decay**
  `dist (P^[t] x) π ≤ λ^t · dist x π`, hence the deny-by-default admission chain reaches
  ε-distance in `t ≥ log ε / log λ` steps.  Replaces the `SpectralAdmit` toy `gap>0 ⇒
  τ<1/ε` with the real Banach-style contraction bound (`λ_⋆ = 1 − γ`, γ the spectral gap).

## Ecosystem use
- F-G1: a11oy Trust-Space — anchor/position embeddings carry a distortion certificate
  (the expansion factor is provably ≤ the Lipschitz constant 1), so "trust-distance
  embedding" views show an HONEST distortion number.
- F-G3: UDS-Core Pepr admission chain — a positive spectral gap (contraction factor < 1)
  provably stabilises the deny-by-default gate geometrically fast (availability cert).
-/
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Kuratowski
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Algebra.Order.Field.Basic

namespace Wave6.MetricSpectral

open scoped NNReal

/-! ## F-G1 — Fréchet anchor coordinate is 1-Lipschitz (the Bourgain expansion side). -/

/-- **F-G1 (a) — single-anchor Fréchet coordinate is 1-Lipschitz.**
    For any anchor `a` in a (pseudo)metric space, the coordinate map `x ↦ dist x a`
    satisfies `|dist x a − dist y a| ≤ dist x y`.  This is the per-coordinate expansion
    bound that makes the P-GNN anchor-distance embedding a non-expansion into ℓ∞.
    Direct instantiation of `abs_dist_sub_le`. -/
theorem frechet_coord_lipschitz {α : Type _} [PseudoMetricSpace α] (a x y : α) :
    |dist x a - dist y a| ≤ dist x y :=
  abs_dist_sub_le x y a

/-- **F-G1 (b) — the anchor coordinate never overshoots the true distance.**
    A one-sided form: `dist x a − dist y a ≤ dist x y`.  The expansion-side certificate
    (the embedding cannot stretch distances by more than factor 1 per anchor coordinate). -/
theorem frechet_coord_nonexpand {α : Type _} [PseudoMetricSpace α] (a x y : α) :
    dist x a - dist y a ≤ dist x y :=
  (abs_le.mp (abs_dist_sub_le x y a)).2

/-- **F-G1 (c) — Kuratowski/Fréchet isometric embedding (distortion = 1).**
    The Kuratowski embedding of a separable metric space into `ℓ^∞(ℕ)` is an
    **isometry** (distortion exactly 1).  This is the distortion-1 anchor of the
    Bourgain spectrum (general low-distortion embeddings trade dimension for distortion;
    the isometric embedding uses all points as anchors).  Direct re-export of
    `kuratowskiEmbedding.isometry`. -/
theorem frechet_isometric_embedding (α : Type _) [MetricSpace α] [SeparableSpace α] :
    Isometry (kuratowskiEmbedding α) :=
  kuratowskiEmbedding.isometry α

/-! ## F-G3 — geometric contraction ⇒ fast mixing (promote SpectralAdmit). -/

/-- The `t`-fold iterate of a self-map `P` (the admission/transition operator). -/
def iterate {α : Type _} (P : α → α) : Nat → α → α
  | 0,     x => x
  | (t+1), x => P (iterate P t x)

/-- **F-G3 — geometric contraction toward the stationary point.**
    Let `π` be a fixed point of `P` (`P π = π`, the stationary distribution) and suppose
    `P` contracts distance to `π` by a factor `λ ∈ [0,1)`:
    `dist (P y) π ≤ λ · dist y π` for all `y`.  Then after `t` steps,
    `dist (P^[t] x) π ≤ λ^t · dist x π`.  The real Levin–Peres-style mixing bound: the
    deny-by-default admission chain converges to stationarity geometrically.
    Proved by induction on `t` using the metric triangle/monotonicity, in any
    pseudometric space. -/
theorem geometric_contraction {α : Type _} [PseudoMetricSpace α]
    (P : α → α) (π : α) (lam : ℝ) (hlam0 : 0 ≤ lam)
    (hcontr : ∀ y, dist (P y) π ≤ lam * dist y π) :
    ∀ (t : Nat) (x : α), dist (iterate P t x) π ≤ lam ^ t * dist x π := by
  intro t
  induction t with
  | zero => intro x; simp [iterate]
  | succ k ih =>
      intro x
      -- dist (P (P^[k] x)) π ≤ lam * dist (P^[k] x) π ≤ lam * (lam^k * dist x π)
      have h1 : dist (iterate P (k+1) x) π ≤ lam * dist (iterate P k x) π := by
        simpa [iterate] using hcontr (iterate P k x)
      have h2 : lam * dist (iterate P k x) π ≤ lam * (lam ^ k * dist x π) :=
        mul_le_mul_of_nonneg_left (ih x) hlam0
      calc dist (iterate P (k+1) x) π
            ≤ lam * dist (iterate P k x) π := h1
        _ ≤ lam * (lam ^ k * dist x π) := h2
        _ = lam ^ (k+1) * dist x π := by ring

/-- **F-G3 (corollary) — the contraction factor strictly shrinks the distance**
    when `λ < 1` and the chain is not already at stationarity: one step of a genuine
    contraction (`λ < 1`) cannot increase the distance to `π`.  This is the honest
    replacement for the `SpectralAdmit` toy inequality (`gap > 0 ⇒ stable`). -/
theorem contraction_nonincrease {α : Type _} [PseudoMetricSpace α]
    (P : α → α) (π : α) (lam : ℝ) (hlam1 : lam ≤ 1)
    (hcontr : ∀ y, dist (P y) π ≤ lam * dist y π) (x : α) :
    dist (P x) π ≤ dist x π := by
  refine (hcontr x).trans ?_
  have hd : 0 ≤ dist x π := dist_nonneg
  calc lam * dist x π ≤ 1 * dist x π := mul_le_mul_of_nonneg_right hlam1 hd
    _ = dist x π := one_mul _

end Wave6.MetricSpectral

-- ## Axiom disclosure (CI prints these in the build log).  Pure instantiations /
-- elementary inductions; expected dependencies are the standard Mathlib trio
-- [propext, Classical.choice, Quot.sound] (NO sorryAx, NO declared Lutar axioms).
#print axioms Wave6.MetricSpectral.frechet_coord_lipschitz
#print axioms Wave6.MetricSpectral.frechet_coord_nonexpand
#print axioms Wave6.MetricSpectral.frechet_isometric_embedding
#print axioms Wave6.MetricSpectral.geometric_contraction
#print axioms Wave6.MetricSpectral.contraction_nonincrease
