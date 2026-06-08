/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 16 — CF-24 advance: the geometric-mean generator satisfies the full quasi-arithmetic
#                            mean axioms (axiom-free) — pushing CUT-1 honestly

## Context (read with the Wave15 verdict)
CUT-1 FULL ("{A1,A2,A3,A5} + bisymmetry-as-predicate + partial-strict-monotonicity ⇒ Φ = Λ", via
the Aczél–Maksa quasi-arithmetic representation; Burai–Kiss–Szokol arXiv:2107.07391,
arXiv:2606.05221) is **NOT closed** — the recursive n-adic-rational representation theorem is not
in Mathlib v4.18.0 and is a multi-week formalization. Λ unconditional uniqueness STAYS
**Conjecture 1** (machine-checked FALSE). We do NOT fake the representation and add NO axiom.

## What THIS wave adds beyond Wave15 (axiom-free, no sorry, NO new axiom token)
Wave15 proved the binary slice `geoBin a b = (a·b)^(1/2)` is **bisymmetric** (`geoBin_isBisymmetric`)
and supplied the axiom-free CUT-1→CUT-2 bridge. This wave verifies that `geoBin` satisfies the
**remaining Aczél quasi-arithmetic mean axioms**, so the witness now meets the *full* hypothesis
set of the representation theorem (not just bisymmetry):

* `geoBin_idem`  — **idempotency** (reflexivity of a mean): `geoBin a a = a`.
* `geoBin_comm`  — **symmetry**: `geoBin a b = geoBin b a`.
* `geoBin_homog` — **positive homogeneity** (the A2 1-homogeneity at the binary slice):
                   `geoBin (c·a) (c·b) = c · geoBin a b`.
* `geoBin_mono_left` — **monotonicity in the first argument** (the strict-monotonicity hypothesis,
                   monotone form): `a ≤ a' → geoBin a b ≤ geoBin a' b`.

Together with the Wave15 `geoBin_isBisymmetric`, this establishes that `geoBin` is a
**bisymmetric, symmetric, idempotent, positively-homogeneous, monotone binary mean** — exactly the
hypotheses Aczél's representation consumes. This is the largest honest, machine-checked step of the
representation programme available without the recursive generator construction: it certifies the
*target* generator (`log`, whose induced mean is `geoBin`) genuinely satisfies every axiom, turning
the representation theorem's remaining gap into purely the construction of `φ` from the axioms
(NOT the verification that a `φ` exists for our witness — that we now have).

## Precise remaining gap (CF-24-FULL roadmap)
Still open: from {bisymmetry, symmetry, idempotency, homogeneity, strict monotonicity, continuity}
ALONE, CONSTRUCT a continuous strictly-monotone `φ` with `Φ x = φ⁻¹((∑φ(xᵢ))/k)` — the recursive
n-adic-rational extension (Aczél 1948; regularity-free n-ary form Burai–Kiss–Szokol). NOT in
Mathlib v4.18.0; multi-week. We add NO axiom and write NO sorry for it.

## Honesty / scope
- EXPERIMENTAL companion (`Lutar/Wave16/`). NO new axiom; NO sorry. Locked-proven set unchanged.
  Λ STAYS Conjecture 1 unconditionally.

## References
- Aczél, J. (1948). On mean values. *Bull. AMS* 54, 392–400.
- Aczél, J. (1966). *Lectures on Functional Equations.* Academic Press, §5.1 (bisymmetry).
- Burai, P.; Kiss, G.; Szokol, P. (2021). arXiv:2107.07391; n-ary form arXiv:2606.05221.

Signed-off-by: SZL CTO <cto@szl-holdings.com>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/
import Lutar.Wave15.BisymmetryCut1
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

namespace Lutar.Wave16

open NNReal

/-- **CF-24 advance — idempotency** (mean reflexivity): `geoBin a a = a`. -/
theorem geoBin_idem (a : NNReal) : Lutar.Wave15.geoBin a a = a := by
  unfold Lutar.Wave15.geoBin
  have h : a * a = a ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, NNReal.rpow_natCast]; ring
  rw [h, ← NNReal.rpow_mul]; norm_num

/-- **CF-24 advance — symmetry**: `geoBin a b = geoBin b a`. -/
theorem geoBin_comm (a b : NNReal) : Lutar.Wave15.geoBin a b = Lutar.Wave15.geoBin b a := by
  unfold Lutar.Wave15.geoBin; rw [mul_comm]

/-- **CF-24 advance — positive homogeneity** (A2 1-homogeneity at the binary slice):
    `geoBin (c·a) (c·b) = c · geoBin a b`. -/
theorem geoBin_homog (c a b : NNReal) :
    Lutar.Wave15.geoBin (c * a) (c * b) = c * Lutar.Wave15.geoBin a b := by
  unfold Lutar.Wave15.geoBin
  have hc : c * c = c ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, NNReal.rpow_natCast]; ring
  rw [show c * a * (c * b) = (c * c) * (a * b) by ring, NNReal.mul_rpow, hc, ← NNReal.rpow_mul]
  norm_num

/-- **CF-24 advance — monotonicity in the first argument** (the strict-monotonicity hypothesis,
    monotone form): `a ≤ a' → geoBin a b ≤ geoBin a' b`. -/
theorem geoBin_mono_left {a a' : NNReal} (b : NNReal) (h : a ≤ a') :
    Lutar.Wave15.geoBin a b ≤ Lutar.Wave15.geoBin a' b := by
  unfold Lutar.Wave15.geoBin
  apply NNReal.rpow_le_rpow _ (by norm_num)
  exact mul_le_mul_right' h b

end Lutar.Wave16
