/-
# WAVE 3 — TIER 1 (in-Mathlib, instantiation only): C1, C2, C6
  (Mathlib-DEPENDENT — verified by lutar-lean CI `lake build`, NOT by bare lean
   here: Mathlib does not fit the sandbox disk.)

For each candidate we (a) MODEL the Lutar substrate object, (b) IMPORT the Mathlib
lemma, (c) APPLY it, (d) state the SUBSTRATE COROLLARY. Zero new mathematical risk:
the math is machine-checked in standard Mathlib; we only instantiate.

## WAVE-5 re-wire note (minimal surface)
Wave-4 isolated `Lutar/Wave3/Tier1Mathlib.lean` as the module that red-lit `lake build`
when wired into the kernel-check root, despite every signature being verified verbatim
against pinned Mathlib (`d7317655`). Wave-5 follows the wave-4 recommendation and
re-wires a MINIMAL version: only the three pure re-exports `c1/c2/c6` whose statements
are byte-identical to the Mathlib theorems they instantiate. The non-load-bearing
numeric remark `c1a_tsirelson_constant` (and its two extra `SpecialFunctions` imports,
which were only needed by `c1a`) are DROPPED. The remaining imports
(`Algebra.Star.CHSH`, `Analysis.Convex.Jensen`) are exactly the modules that define the
instantiated theorems, so the build graph is the minimal closure required.

## Honesty / doctrine (Doctrine v11)
- Λ (F23) stays Conjecture 1; nothing here touches it.
- Maturity: `proven` once CI `lake build` is green (Mathlib-dependent). The interpretive
  caveats (C1/C2: "quantum" is an algebra ANALOGY; C6: convexity/integrability side-
  conditions) are stated as HYPOTHESES, never hidden.
- Locked kernel (749/14/163 @ c7c0ba17) SEPARATE; this is experimental/wave3. SLSA L2.

## Citations & Mathlib paths
- C1 Tsirelson 2√2: Tsirelson 1980, Lett. Math. Phys. 4 93-100, doi:10.1007/BF00417500.
  Mathlib: `tsirelson_inequality` in Mathlib.Algebra.Star.CHSH.
- C2 CHSH ≤ 2: Clauser-Horne-Shimony-Holt, PRL 23 (1969) 880,
  doi:10.1103/PhysRevLett.23.880. Mathlib: `CHSH_inequality_of_comm` in Mathlib.Algebra.Star.CHSH.
- C6 Jensen ⇒ ELBO: Jensen 1906. Mathlib: `ConvexOn.map_sum_le` in Mathlib.Analysis.Convex.Jensen.

## Substrate use
- C1/C2: Lutar-Omega EPR-Bell governance diagnostic (classical ceiling 2 vs operator
  ceiling 2√2 separating "classically-explainable" vs entangled agent agreement).
- C6: active-inference free-energy core (ELBO ≤ log-evidence direction = finite Jensen).
-/
import Mathlib.Algebra.Star.CHSH
import Mathlib.Analysis.Convex.Jensen

namespace Wave3.Tier1

/-! ## C1 / C2 — Lutar-Omega EPR–Bell governance diagnostic.
    We MODEL the four Lutar-Omega agent observables as a Mathlib `IsCHSHTuple` over
    an abstract ordered `*`-algebra `R` over ℝ, then APPLY the Mathlib bounds. -/

section LutarOmega
variable {R : Type*}

/-- **C2 — classical (commutative) ceiling = 2.** If the four Lutar-Omega
    observables `A₀ A₁ B₀ B₁` form a CHSH tuple in a COMMUTATIVE ordered `*`-algebra
    over ℝ (the "local hidden-variable" / independent-prior agent model), their
    Bell-CHSH agreement score is ≤ 2. Direct instantiation of `CHSH_inequality_of_comm`. -/
theorem c2_lutar_omega_classical_ceiling
    [OrderedCommRing R] [StarRing R] [StarOrderedRing R] [Algebra ℝ R] [OrderedSMul ℝ R]
    (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2 :=
  CHSH_inequality_of_comm A₀ A₁ B₀ B₁ T

/-- **C1 — operator (Tsirelson) ceiling = 2√2.** In a (possibly NONcommutative)
    ordered `*`-algebra over ℝ — the "entangled agent" model — the Lutar-Omega
    Bell-CHSH score is bounded by `√2³ • 1 = 2√2 • 1`. Direct instantiation of
    `tsirelson_inequality`. Together with C2 this pins the 2 vs 2√2 separation:
    a governed-AI agreement score exceeding 2 cannot arise from independent
    (commuting/local) agent priors. -/
theorem c1_lutar_omega_tsirelson_ceiling
    [OrderedRing R] [StarRing R] [StarOrderedRing R] [Algebra ℝ R] [OrderedSMul ℝ R]
    [StarModule ℝ R]
    (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ √2 ^ 3 • (1 : R) :=
  tsirelson_inequality A₀ A₁ B₀ B₁ T

end LutarOmega

/-! ## C6 — Jensen ⇒ honestly-conservative forecaster (ELBO direction).
    Mathlib `ConvexOn.map_sum_le` (finite Jensen). We instantiate the convexity of
    a trust/forecast objective to certify the aggregate never overstates the per-item
    objective — the discrete ELBO-direction inequality on a finite support. -/

/-- **C6 — finite Jensen for a convex forecasting objective.** For a convex `φ` on a
    convex set `s`, weights `w ≥ 0` summing to 1, and points `p i ∈ s`,
    `φ (Σ wᵢ pᵢ) ≤ Σ wᵢ φ(pᵢ)`. This is the honestly-conservative direction the
    active-inference forecaster relies on (the convex surrogate upper-bounds the
    mixed objective). Direct instantiation of `ConvexOn.map_sum_le`. -/
theorem c6_jensen_forecaster
    {ι : Type*} (t : Finset ι) (φ : ℝ → ℝ) (s : Set ℝ)
    (hφ : ConvexOn ℝ s φ) (w : ι → ℝ) (p : ι → ℝ)
    (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : ∑ i ∈ t, w i = 1)
    (hp : ∀ i ∈ t, p i ∈ s) :
    φ (∑ i ∈ t, w i • p i) ≤ ∑ i ∈ t, w i • φ (p i) :=
  hφ.map_sum_le hw₀ hw₁ hp

end Wave3.Tier1

-- ## Axiom disclosure (CI prints these in the build log). Pure instantiations of
-- Mathlib theorems; expected deps are the standard [propext, Classical.choice,
-- Quot.sound] trio (NO sorryAx, NO declared Lutar axioms).
#print axioms Wave3.Tier1.c1_lutar_omega_tsirelson_ceiling
#print axioms Wave3.Tier1.c2_lutar_omega_classical_ceiling
#print axioms Wave3.Tier1.c6_jensen_forecaster
