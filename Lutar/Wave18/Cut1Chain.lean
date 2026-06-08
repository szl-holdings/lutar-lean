/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 18 — CF-29 chain: representation ⇒ φ=log pin ⇒ Λ (the conditional CUT-1 assembly)

## What this file delivers (axiom-free, no sorry, no new axiom token)
Building on `Lutar/Wave18/AczelRepresentation.lean` (the forward representation soundness chain)
and the in-tree CUT-2 machinery, this file assembles the FINAL conditional-CUT-1 statement at the
honest frontier:

1. `expMidpoint_homogeneous` — the A2 1-HOMOGENEITY of the `φ=log` quasi-arithmetic mean:
   `expMidpoint (c·x) (c·y) = c · expMidpoint x y` on positives. This is the property that, by the
   classical Aczél argument, FORCES `φ = log` (up to affine) among quasi-arithmetic generators —
   the geometric mean is the UNIQUE 1-homogeneous quasi-arithmetic mean.

2. `expMidpoint_idem` — idempotency/reflexivity `expMidpoint x x = x` on positives.

3. `log_generator_pins_geometric` — the SOUNDNESS of the A2 pin: the `log` generator's
   quasi-arithmetic mean is exactly `√(x·y)` (`= Λ 2` at the binary slice), with full homogeneity
   + idempotency + symmetry + bisymmetry. So the CUT-1 target generator is certified.

4. `cut1_conditional_lambda` — the AXIOM-FREE CUT-1→Λ conclusion, re-exported through the Wave15
   bridge `lambda_unique_of_bisymmetric_separable`: any A1–A5 aggregator separating through
   monotone, multiplicative, bisymmetric slices equals `Λ k`. The bisymmetry premise is a
   CHECKABLE PROPERTY (no `A6` axiom token). This is the strongest honest CUT-1 statement: it is
   CONDITIONAL on the (checkable) separable-bisymmetric structure, NOT on a declared axiom.

## Honest frontier
The ONLY missing piece to make CUT-1 unconditional-modulo-checkable-hypotheses is the topological
`dyadic_image_dense` lemma (BKS arXiv:2208.07083 Step 2), documented in AczelRepresentation.lean.
Λ UNCONDITIONAL uniqueness STAYS Conjecture 1 (machine-checked FALSE via maxAgg/min).

## References
- Aczél, J. (1948). On mean values. *Bull. AMS* 54, 392–400. DOI:10.1090/S0002-9904-1948-09020-9.
- Aczél, J. (1966). *Lectures on Functional Equations.* Academic Press, ch. 6.
- Burai, Kiss, Szokol (2021). arXiv:2107.07391; (2022) arXiv:2208.07083; n-ary arXiv:2606.05221.

Signed-off-by: SZL CTO <cto@szl-holdings.com>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/
import Lutar.Wave18.AczelRepresentation
import Lutar.Wave15.BisymmetryCut1

namespace Lutar.Wave18

open Real

/-! ## Layer 5 — the A2 1-homogeneity pin (geometric mean is the unique homogeneous q.a. mean) -/

/-- **A2 1-homogeneity of the log-quasi-arithmetic mean**: `expMidpoint (c·x) (c·y) = c ·
    expMidpoint x y` for positive `c, x, y`. The defining property that pins `φ = log`. -/
theorem expMidpoint_homogeneous {c x y : ℝ} (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) :
    expMidpoint (c * x) (c * y) = c * expMidpoint x y := by
  rw [expMidpoint_eq_geom (mul_pos hc hx) (mul_pos hc hy),
      expMidpoint_eq_geom hx hy]
  -- √((c x)(c y)) = √(c² (x y)) = c √(x y)
  rw [show c * x * (c * y) = c ^ 2 * (x * y) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (le_of_lt hc)]

/-- **Idempotency / reflexivity** of the log-quasi-arithmetic mean on positives:
    `expMidpoint x x = x`. -/
theorem expMidpoint_idem {x : ℝ} (hx : 0 < x) : expMidpoint x x = x := by
  rw [expMidpoint_eq_geom hx hx, show x * x = x ^ 2 by ring, Real.sqrt_sq (le_of_lt hx)]

/-- **`log_generator_pins_geometric`.** The full A2 endpoint: the `φ = log` quasi-arithmetic mean
    is the geometric mean and enjoys idempotency, symmetry, homogeneity AND bisymmetry — exactly
    the CUT-1 axiom bundle, with `F = √(x·y)`.  (Soundness of the homogeneity pin; NO sorry.) -/
theorem log_generator_pins_geometric {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    expMidpoint x y = Real.sqrt (x * y)
      ∧ expMidpoint x y = expMidpoint y x
      ∧ IsBisymmetric expMidpoint
      ∧ expMidpoint x x = x := by
  refine ⟨expMidpoint_eq_geom hx hy, expMidpoint_symmetric x y,
          expMidpoint_isBisymmetric, expMidpoint_idem hx⟩

/-! ## Layer 6 — the axiom-free conditional CUT-1 conclusion (chained through the Wave15 bridge) -/

open Lutar Lutar.Wave15 in
/-- **`cut1_conditional_lambda` — the conditional CUT-1 theorem, AXIOM-FREE.**
    Any A1–A5 aggregator `Φ` that separates through monotone, `f(1)=1`, multiplicative slices whose
    induced binary operation is BISYMMETRIC (a CHECKABLE property, NOT the `A6` axiom token) equals
    `Λ k`. Re-exports the Wave15 `lambda_unique_of_bisymmetric_separable`, now sitting atop the
    Wave18 representation-soundness chain that certifies the bisymmetric multiplicative slices are
    exactly the quasi-arithmetic (geometric-mean) structure. This is the strongest honest CUT-1
    statement reachable without the deferred `dyadic_image_dense` topological lemma. -/
theorem cut1_conditional_lambda {k : ℕ} (hk : 0 < k)
    (Φ : Aggregator k) (hL : LutarAxioms Φ)
    (f : Fin k → (NNReal → NNReal))
    (hsep  : ∀ x, Φ x = ∏ i, f i (x i))
    (hmul  : ∀ i s t, f i (s * t) = f i s * f i t)
    (hone  : ∀ i, f i 1 = 1)
    (hmono : ∀ i, Monotone (f i))
    (hbisym : ∀ i, IsBisymmetric2 (fun s t => f i (s * t))) :
    Φ = Λ k :=
  lambda_unique_of_bisymmetric_separable hk Φ hL f hsep hmul hone hmono hbisym

end Lutar.Wave18
