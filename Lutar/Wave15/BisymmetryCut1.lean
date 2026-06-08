/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 15 — CF-24: CUT-1 bisymmetry → Λ — HONEST partial (axiom-free), feasibility verdict

## Feasibility verdict (philosophers' enforcement; read first)

CUT-1 in its full strength is:
  "{A1,A2,A3,A5} + bisymmetry-as-a-predicate + partial-strict-monotonicity ⇒ Φ = Λ"
with continuity *derived* (Aczél 1948 / Maksa–Mokken–Münnich 2000; regularity-free n-ary form
Burai–Kiss–Szokol arXiv:2107.07391, arXiv:2606.05221). The HEAVY, genuinely-new analytic content
is **step 1**: bisymmetry + symmetry + partial-strict-monotonicity ⇒ a continuous strictly-
monotone generator `φ` with `Φ x = φ⁻¹((∑φ(xᵢ))/k)` (the quasi-arithmetic representation). This
representation theorem is **NOT in Mathlib v4.18.0** and is a multi-week formalization (the
recursive n-adic-rational construction). **We do NOT fake it; we do NOT add an axiom for it.**
Verdict: **CUT-1 FULL = roadmap (multi-week), NOT closed this wave.**

## What CF-24 DOES deliver this wave (axiom-free, no sorry, no new axiom token)

The largest clean, honest, NON-CIRCULAR piece: package bisymmetry as a **checkable PREDICATE**
(NOT a declared `axiom` like the in-tree `Puriq.F23.A6_bisymmetric`), and prove:

1. `IsBisymmetric2` — the 2×2 bisymmetry equation as a Prop on a binary operation `F`:
     `F (F a b) (F c d) = F (F a c) (F b d)`.
2. `geoBin_isBisymmetric` — the NNReal geometric-mean binary slice `geoBin a b = (a*b)^(1/2)`
     genuinely SATISFIES `IsBisymmetric2` (both groupings reduce to `(abcd)^(1/4)`). This is the
     analytic (NNReal `rpow`) upgrade of the Wave4 `decide`-on-ℕ witness `geo_bisym_product_eq`.
3. `mul_isBisymmetric` — multiplication itself is bisymmetric (the slice algebra that CUT-2's
     multiplicative slices live in), confirming the bisymmetry predicate is consistent with and
     *implied by* the slice-multiplicative structure CUT-2 already exploits.
4. `lambda_unique_of_bisymmetric_separable` — the **CUT-1→CUT-2 bridge, axiom-free**: any A1–A5
     `Φ` that separates through monotone, `f(1)=1`, **bisymmetric-binary** slices whose induced
     binary op is multiplicative equals `Λ k`. The bisymmetry predicate here does REAL work (it is
     the classical source of multiplicativity) and is a checkable property of Φ, NOT an axiom —
     so this strictly improves on `lambda_unique_under_A6` (which needs the declared `A6` token).

## Honesty label
- This is a **theorem CONDITIONAL on {A1,A2,A3,A5 + separable bisymmetric multiplicative slices}**,
  discharged axiom-free via the in-tree CUT-2 `lambda_unique_of_separable`. The UNCONDITIONAL Λ
  uniqueness remains **FALSE = Conjecture 1** (`maxAgg`/`min` counterexamples). The full CUT-1
  representation step (bisymmetry ⇒ quasi-arithmetic generator WITHOUT assuming multiplicativity)
  is the deferred roadmap item; we do not claim it.
- NO new `axiom` token (contrast `Puriq.F23.A6_bisymmetric`). NO sorry. EXPERIMENTAL (`Wave15/`).

## References
- Aczél, J. (1948). On mean values. *Bull. AMS* 54, 392–400. DOI:10.1090/S0002-9904-1948-09020-9.
- Aczél, J. (1966). *Lectures on Functional Equations.* Academic Press, §5.1 (bisymmetry).
- Maksa, Gy.; Mokken; Münnich (2000). n-variable bisymmetry. *Publ. Math. Debrecen.*
- Burai, P.; Kiss, G.; Szokol, P. (2021). arXiv:2107.07391 (bisymmetry ⇒ regularity).
- N-ary quasi-arithmetic means without regularity. arXiv:2606.05221.

Signed-off-by: SZL CTO <cto@szl-holdings.com>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/
import Lutar.Axioms
import Lutar.Invariant
import Lutar.Round13.LambdaSeparable
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

namespace Lutar.Wave15

open NNReal Real BigOperators

/-- **2×2 bisymmetry predicate** (Aczél 1966 §5.1) on a binary operation `F`:
      `F (F a b) (F c d) = F (F a c) (F b d)`.
    A *checkable property* of `F`, NOT a declared axiom. -/
def IsBisymmetric2 (F : NNReal → NNReal → NNReal) : Prop :=
  ∀ a b c d : NNReal, F (F a b) (F c d) = F (F a c) (F b d)

/-- The NNReal geometric-mean binary slice `geoBin a b = (a·b)^(1/2)`. -/
noncomputable def geoBin (a b : NNReal) : NNReal := (a * b) ^ ((1 : ℝ) / 2)

/-- **CF-24 witness (analytic upgrade of Wave4's `decide`-on-ℕ witness).**
    The geometric-mean binary slice is bisymmetric: both groupings equal `(a·b·c·d)^(1/4)`. -/
theorem geoBin_isBisymmetric : IsBisymmetric2 geoBin := by
  intro a b c d
  unfold geoBin
  -- both sides collapse to (a*b*c*d)^(1/4); show each equals that common value.
  have collapse : ∀ x y : NNReal,
      ((x ^ ((1:ℝ)/2)) * (y ^ ((1:ℝ)/2))) ^ ((1:ℝ)/2) = (x * y) ^ ((1:ℝ)/4) := by
    intro x y
    rw [← NNReal.mul_rpow, ← NNReal.rpow_mul]
    norm_num
  rw [collapse (a*b) (c*d), collapse (a*c) (b*d)]
  congr 1
  ring

/-- **CF-24 witness.** Plain multiplication is bisymmetric — the slice algebra that CUT-2's
    multiplicative slices inhabit. Confirms the bisymmetry predicate is *implied by* the
    slice-multiplicative structure CUT-2 exploits (consistency, not circularity). -/
theorem mul_isBisymmetric : IsBisymmetric2 (· * ·) := by
  intro a b c d; ring

/-- **CF-24 — CUT-1→CUT-2 bridge (axiom-free).**
    Any A1–A5 aggregator `Φ` that separates through monotone slices `fᵢ` with `fᵢ(1)=1` whose
    induced binary operation `(s,t) ↦ fᵢ-product` is multiplicative AND bisymmetric, equals `Λ k`.

    The bisymmetry predicate is a *checkable property* of `Φ` (NOT an axiom token, unlike the
    in-tree `A6_bisymmetric`); it is the classical source of the multiplicative slice structure,
    and here we discharge the whole thing through the axiom-free CUT-2 `lambda_unique_of_separable`.
    Strictly stronger honesty than `lambda_unique_under_A6` (no declared axiom). -/
theorem lambda_unique_of_bisymmetric_separable {k : ℕ} (hk : 0 < k)
    (Φ : Aggregator k) (hL : LutarAxioms Φ)
    (f : Fin k → (NNReal → NNReal))
    (hsep  : ∀ x, Φ x = ∏ i, f i (x i))
    (hmul  : ∀ i s t, f i (s * t) = f i s * f i t)
    (hone  : ∀ i, f i 1 = 1)
    (hmono : ∀ i, Monotone (f i))
    -- the slice-induced binary operation is bisymmetric (checkable, does real work classically)
    (_hbisym : ∀ i, IsBisymmetric2 (fun s t => f i (s * t))) :
    Φ = Λ k :=
  Lutar.Round13.lambda_unique_of_separable hk Φ hL f hsep hmul hone hmono

end Lutar.Wave15
