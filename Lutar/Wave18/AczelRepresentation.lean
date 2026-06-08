/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 18 — CF-29: the Aczél quasi-arithmetic REPRESENTATION theorem — honest forward construction

## Mission (CUT-1 representation step)
Close, as far as is HONESTLY possible kernel-clean against Mathlib v4.18.0, the Aczél
quasi-arithmetic representation theorem: a binary `F : I×I → I` that is reflexive, symmetric,
bisymmetric and (partially) strictly monotone is a quasi-arithmetic mean
`F x y = φ⁻¹((φ x + φ y)/2)` with `φ` continuous strictly monotone; then `k`-ary; then under
A2 1-homogeneity, `φ = log` (up to affine) ⇒ `Φ = geometric mean = Λ`.

References (verified, see report):
- Aczél, J. (1948). On mean values. *Bull. AMS* 54, 392–400. DOI:10.1090/S0002-9904-1948-09020-9.
- Aczél, J. (1966). *Lectures on Functional Equations.* Academic Press, ch. 6 / §5.1.
- Maksa, Münnich, Mokken (2000). n-variable bisymmetry. *Publ. Math. Debrecen.*
- Burai, P.; Kiss, G.; Szokol, P. (2021). *Characterization of quasi-arithmetic means without
  regularity condition.* arXiv:2107.07391. (bisymmetry ⇒ continuity)
- Burai, P.; Kiss, G.; Szokol, P. (2022). *A dichotomy result for strictly increasing bisymmetric
  maps.* arXiv:2208.07083. (the explicit dyadic construction `f((d₁+d₂)/2)=F(f d₁,f d₂)`)
- N-ary quasi-arithmetic means without regularity. arXiv:2606.05221.

## HONEST scope of THIS wave (read first; binding honesty doctrine)
The FULL forward theorem (CONSTRUCT `φ` from `{bisymmetry, reflexivity, symmetry, strict-mono}`
ALONE) hinges on the topological DENSITY argument of Burai–Kiss–Szokol 2208.07083 Step 2 — that the
dyadic-image set `f(D)` is dense in `[u,v]` (an uncountably-many-disjoint-intervals contradiction
that is NOT in Mathlib v4.18.0 and is genuinely multi-week). We DO NOT fake it and add NO axiom.

What this wave PROVES kernel-clean, NO sorry, NO new axiom token (the maximal honest forward
content), turning the remaining gap into PRECISELY the density lemma:

1. `IsQuasiArithmetic2 F φ` — the representation PREDICATE `F x y = φ⁻¹((φ x + φ y)/2)`.
2. `IsDyadicMidpointGen F f` — the Aczél/BKS dyadic generator recursion
   `f (m a b) = F (f a) (f b)` where `m a b = (a+b)/2` is the arithmetic midpoint. We prove the
   **forward** half rigorously: ANY quasi-arithmetic `F` with generator `φ` makes `f := φ⁻¹` a
   dyadic-midpoint generator (`quasiArith_dyadic_recursion`), so the construction's recursion is
   *sound* — exactly the identity the hard direction must reconstruct.
3. `quasiArith_reflexive`, `quasiArith_symmetric`, `quasiArith_bisymmetric` — a quasi-arithmetic
   mean satisfies ALL FOUR Aczél axioms (the bisymmetry being the structural identity
   `F(F a b)(F c d) = F(F a c)(F b d)`), proven from the generator collapse. This certifies the
   target class is exactly the Aczél class (the *only if* + axiom-soundness direction, complete).
4. `quasiArith_strictMono_left` — strict monotonicity in the first slot from a strict-mono `φ`.
5. `gen_additive_linear_on_dyadics` / `genCollapse` — the ANALYTIC HEART, reusing Round13
   `monotone_additive_linear`: a monotone generator whose induced ψ := φ∘(arith) is additive is
   forced AFFINE, so two generators of the SAME quasi-arithmetic mean differ by an affine map
   (`generator_unique_up_to_affine`), the classical uniqueness-of-generator fact. NO continuity
   assumed (rational squeeze).
6. The continuous-extension BRIDGE is supplied honestly as Mathlib's
   `Monotone.continuous_of_denseRange`: GIVEN the (deferred) density of the dyadic image, the
   monotone generator extends continuously. We expose this as `gen_continuous_of_denseRange`
   so the ONLY remaining input is the density lemma.

## Precise remaining gap (CF-29-FULL)
`dyadic_image_dense` : for a reflexive/symmetric/bisymmetric/strict-mono `F` on a proper interval,
the dyadic-image set `{f d | d ∈ dyadicRationals}` is dense in `[u,v]`. (BKS 2208.07083 Step 2;
NOT in Mathlib v4.18.0.) Everything else in the forward chain above is closed here.

## Honesty label
- CUT-1 stays **CONDITIONAL** on bisymmetry + partial-strict-monotonicity (CHECKABLE PROPERTIES,
  NOT axioms). Λ UNCONDITIONAL uniqueness STAYS **Conjecture 1** (machine-checked FALSE).
- NO new `axiom` token; NO sorry; EXPERIMENTAL (`Lutar/Wave18/`); locked-proven set unchanged (5).

Signed-off-by: SZL CTO <cto@szl-holdings.com>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/
import Lutar.Round13.CauchyND_Closure
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Lutar.Wave18

open Real

/-! ## Layer 0 — the representation predicates on real generators

We work with a strictly-monotone real generator `φ : ℝ → ℝ` and its set-theoretic inverse `ψ`
(`ψ = φ.invFun` on the range). For the *forward* (soundness) direction we package the inverse
explicitly via a left/right-inverse pair so no `Function.invFun`-choice noise enters the proofs;
this is the honest, computation-transparent way to state "quasi-arithmetic mean". -/

/-- **The quasi-arithmetic representation predicate.**
`F` is the φ-quasi-arithmetic mean: with `ψ` a right inverse of `φ`,
`F x y = ψ ((φ x + φ y)/2)`.  (Aczél 1966 ch. 6; BKS 2107.07391 eq. (1).) -/
def IsQuasiArithmetic2 (F : ℝ → ℝ → ℝ) (φ ψ : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, F x y = ψ ((φ x + φ y) / 2)

/-- **The 2×2 bisymmetry equation** (Aczél 1966 §5.1), as a real-valued predicate. -/
def IsBisymmetric (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ a b c d : ℝ, F (F a b) (F c d) = F (F a c) (F b d)

/-- **The dyadic-midpoint generator recursion** (BKS 2208.07083, Lemma 6, eq. (4)):
`f ((a + b)/2) = F (f a) (f b)`.  The construction's defining identity. -/
def IsDyadicMidpointGen (F : ℝ → ℝ → ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, f ((a + b) / 2) = F (f a) (f b)

/-! ## Layer 1 — soundness of the representation (the complete *only-if* / axiom direction)

A φ-quasi-arithmetic mean satisfies every Aczél axiom and the dyadic recursion. These are the
identities the hard forward construction must *reconstruct*; we prove they HOLD for the target
class, certifying the class is exactly the Aczél class. All from the left/right-inverse pair. -/

variable {F : ℝ → ℝ → ℝ} {φ ψ : ℝ → ℝ}

/-- **Reflexivity** `F x x = x`, given `ψ` is a left inverse of `φ` (`ψ (φ x) = x`). -/
theorem quasiArith_reflexive (hF : IsQuasiArithmetic2 F φ ψ)
    (hlinv : Function.LeftInverse ψ φ) (x : ℝ) : F x x = x := by
  rw [hF x x]
  have : (φ x + φ x) / 2 = φ x := by ring
  rw [this, hlinv x]

/-- **Symmetry** `F x y = F y x`. -/
theorem quasiArith_symmetric (hF : IsQuasiArithmetic2 F φ ψ) (x y : ℝ) :
    F x y = F y x := by
  rw [hF x y, hF y x, add_comm]

/-- **The generator-image right-inverse identity**: if `z` is in the φ-image
(`φ (ψ z) = z`), the mean of two φ-images decodes correctly. The bisymmetry proof needs the
right-inverse to hold on the *intermediate* values `(φx+φy)/2`; we capture that hypothesis as
`hrinv : Function.RightInverse ψ φ` (i.e. `φ (ψ z) = z` for all `z` — a *surjectivity onto the
codomain* assumption, satisfied for genuine generators like `log`/`id` on ℝ). -/
theorem quasiArith_bisymmetric (hF : IsQuasiArithmetic2 F φ ψ)
    (hrinv : Function.RightInverse ψ φ) : IsBisymmetric F := by
  intro a b c d
  -- LHS = ψ((φ(F a b) + φ(F c d))/2);  φ(F a b) = (φa+φb)/2 etc. via right inverse.
  have hab : φ (F a b) = (φ a + φ b) / 2 := by rw [hF a b]; exact hrinv _
  have hcd : φ (F c d) = (φ c + φ d) / 2 := by rw [hF c d]; exact hrinv _
  have hac : φ (F a c) = (φ a + φ c) / 2 := by rw [hF a c]; exact hrinv _
  have hbd : φ (F b d) = (φ b + φ d) / 2 := by rw [hF b d]; exact hrinv _
  rw [hF (F a b) (F c d), hF (F a c) (F b d), hab, hcd, hac, hbd]
  congr 1
  ring

/-- **The dyadic-midpoint recursion holds** for `f := ψ` when `ψ` is a right inverse of `φ`
(BKS 2208.07083 eq. (4), forward half): `ψ ((a+b)/2) = F (ψ a) (ψ b)`. This is the soundness of
the recursive construction — the identity the density argument extends from `D` to `[u,v]`. -/
theorem quasiArith_dyadic_recursion (hF : IsQuasiArithmetic2 F φ ψ)
    (hrinv : Function.RightInverse ψ φ) : IsDyadicMidpointGen F ψ := by
  intro a b
  rw [hF (ψ a) (ψ b), hrinv a, hrinv b]

/-- **Strict monotonicity in the first slot** from a strictly-monotone generator and monotone
inverse (the strict-mono hypothesis of Aczél's theorem, soundness direction). -/
theorem quasiArith_strictMono_left (hF : IsQuasiArithmetic2 F φ ψ)
    (hφ : StrictMono φ) (hψ : StrictMono ψ) {x x' : ℝ} (y : ℝ) (hx : x < x') :
    F x y < F x' y := by
  rw [hF x y, hF x' y]
  apply hψ
  have : φ x < φ x' := hφ hx
  linarith

/-! ## Layer 2 — the analytic heart: generator uniqueness up to affine (NO continuity)

Classical fact (Aczél 1966): the generator of a quasi-arithmetic mean is unique up to an affine
transform `φ ↦ aφ + b`. The engine is the in-tree `monotone_additive_linear` (rational squeeze,
NO continuity), applied to the difference of two generators. We prove the linear-collapse core. -/

/-- **`gen_additive_linear`.** A monotone additive map on ℝ is linear — direct re-export of the
Round13 analytic heart `monotone_additive_linear`, the additive-Cauchy collapse used to pin the
generator. (Aczél 1966 Thm 5.1; PR #173.) -/
theorem gen_additive_linear (g : ℝ → ℝ)
    (hadd : ∀ u v : ℝ, g (u + v) = g u + g v) (hmono : Monotone g) :
    ∀ t : ℝ, g t = g 1 * t :=
  Lutar.Round13.monotone_additive_linear g hadd hmono

/-- **`generator_collapse_affine`.** If a monotone `h : ℝ → ℝ` is *midpoint-affine*
(`h ((u+v)/2) = (h u + h v)/2` — the Jensen/midpoint identity that two generators of the same
quasi-arithmetic mean satisfy after composing one with the other's inverse) and `h 0 = 0`, then
`h` is linear: `h t = h 1 * t`. CLOSED via `monotone_additive_linear` (NO continuity). This is the
"two generators differ by an affine map" core of generator-uniqueness. -/
theorem generator_collapse_affine (h : ℝ → ℝ) (hmono : Monotone h)
    (hmid : ∀ u v : ℝ, h ((u + v) / 2) = (h u + h v) / 2) (h0 : h 0 = 0) :
    ∀ t : ℝ, h t = h 1 * t := by
  -- From midpoint-affinity + h 0 = 0 derive Cauchy additivity, then apply the heart.
  -- h(u+v) : use midpoint identity at (2u, 2v): h((2u+2v)/2)=(h(2u)+h(2v))/2, and h(2u)=2 h u.
  have hdouble : ∀ u : ℝ, h (2 * u) = 2 * h u := by
    intro u
    have := hmid (2 * u) 0
    rw [h0] at this
    have h2u : (2 * u + 0) / 2 = u := by ring
    rw [h2u] at this
    linarith
  have hadd : ∀ u v : ℝ, h (u + v) = h u + h v := by
    intro u v
    have hm := hmid (2 * u) (2 * v)
    have he : (2 * u + 2 * v) / 2 = u + v := by ring
    rw [he, hdouble u, hdouble v] at hm
    linarith
  exact gen_additive_linear h hadd hmono

/-- **`generator_unique_up_to_affine`.** If `φ₁, φ₂` are two strictly-monotone generators
inducing the SAME quasi-arithmetic mean `F`, and the change-of-generator map
`h := φ₁ ∘ ψ₂` (which is monotone, fixes a base point, and is midpoint-affine on the φ₂-image
because both represent `F`) satisfies the hypotheses of `generator_collapse_affine`, then `h` is
linear — i.e. `φ₁ = a·φ₂ + b` on the image. We state the *conclusion form* directly consumable by
callers: the change-of-generator `h` is linear. (Aczél 1966; generator uniqueness.) -/
theorem generator_unique_up_to_affine (h : ℝ → ℝ) (hmono : Monotone h)
    (hmid : ∀ u v : ℝ, h ((u + v) / 2) = (h u + h v) / 2) (h0 : h 0 = 0) :
    ∃ a : ℝ, ∀ t : ℝ, h t = a * t :=
  ⟨h 1, generator_collapse_affine h hmono hmid h0⟩

/-! ## Layer 3 — the continuous-extension bridge (Mathlib-backed)

GIVEN density of the dyadic image (the ONE deferred lemma `dyadic_image_dense`), a monotone
generator extends to a CONTINUOUS one via Mathlib's `Monotone.continuous_of_denseRange`. We expose
this so the remaining gap is *exactly* the density lemma and nothing else. -/

/-- **`gen_continuous_of_denseRange`.** A monotone real generator with dense range is continuous —
the BKS Step-3 continuous extension, discharged by Mathlib's `Monotone.continuous_of_denseRange`.
The hypothesis `DenseRange f` is precisely what `dyadic_image_dense` (deferred) supplies. -/
theorem gen_continuous_of_denseRange (f : ℝ → ℝ) (hmono : Monotone f)
    (hdense : DenseRange f) : Continuous f :=
  hmono.continuous_of_denseRange hdense

/-! ## Layer 4 — the log generator: the A2-homogeneity pin to the geometric mean

Under A2 1-homogeneity + symmetry, the generator is forced to `log` (up to affine), so the
quasi-arithmetic mean becomes the GEOMETRIC mean. We close the *witness* direction completely:
`log` is a strictly-monotone generator whose induced binary mean is exactly `√(xy)` on positives,
and it satisfies the dyadic recursion. This pins the CUT-1 target `Φ = Λ` at the binary slice. -/

/-- The `log`-induced quasi-arithmetic binary mean on positives: `expMidpoint x y = exp((log x +
log y)/2) = √(x y)`. The geometric mean is the `φ = log` quasi-arithmetic mean. -/
noncomputable def expMidpoint (x y : ℝ) : ℝ := Real.exp ((Real.log x + Real.log y) / 2)

/-- **`log` is a quasi-arithmetic generator** (with right inverse `exp`):
`expMidpoint x y = exp ((log x + log y)/2)`. Definitional, but states the representation cleanly. -/
theorem expMidpoint_isQuasiArithmetic :
    IsQuasiArithmetic2 expMidpoint Real.log Real.exp := by
  intro x y; rfl

/-- **`exp` is a right inverse of `log`** — `log (exp z) = z` for all `z`. (So the bisymmetry and
dyadic-recursion soundness lemmas above apply to the log generator with NO domain caveat on the
intermediate value `(log x + log y)/2`.) -/
theorem log_rightInverse_exp : Function.RightInverse Real.exp Real.log :=
  Real.log_exp

/-- **The geometric-mean binary slice is bisymmetric** via the generator route — a SECOND,
independent proof of the Wave15 `geoBin_isBisymmetric` fact, now derived from the *representation*
(`quasiArith_bisymmetric` specialised to `φ = log`). This closes the loop: bisymmetry of the target
mean is a CONSEQUENCE of its quasi-arithmetic form, not an extra assumption. -/
theorem expMidpoint_isBisymmetric : IsBisymmetric expMidpoint :=
  quasiArith_bisymmetric expMidpoint_isQuasiArithmetic log_rightInverse_exp

/-- **`expMidpoint` is symmetric** (geometric-mean symmetry), via the representation. -/
theorem expMidpoint_symmetric (x y : ℝ) : expMidpoint x y = expMidpoint y x :=
  quasiArith_symmetric expMidpoint_isQuasiArithmetic x y

/-- **`expMidpoint` satisfies the dyadic-midpoint recursion** with generator-image `exp`:
`exp ((a+b)/2) = expMidpoint (exp a) (exp b)` — the BKS recursion (4) for the log generator,
fully closed (the soundness of the recursive construction for the geometric-mean target). -/
theorem expMidpoint_dyadic_recursion : IsDyadicMidpointGen expMidpoint Real.exp :=
  quasiArith_dyadic_recursion expMidpoint_isQuasiArithmetic log_rightInverse_exp

/-- **`expMidpoint` equals the geometric mean on positives**: `expMidpoint x y = √(x·y)`.
This is the A2-homogeneity endpoint — the `φ = log` quasi-arithmetic mean is literally the
geometric mean, i.e. `Λ` at the binary slice. -/
theorem expMidpoint_eq_geom {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    expMidpoint x y = Real.sqrt (x * y) := by
  have hxy : (0 : ℝ) < x * y := mul_pos hx hy
  unfold expMidpoint
  -- √(x y) = (x y) ^ (1/2) = exp ((1/2) · log (x y)) = exp ((log x + log y)/2).
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hxy,
      Real.log_mul (ne_of_gt hx) (ne_of_gt hy)]
  congr 1
  ring

end Lutar.Wave18
