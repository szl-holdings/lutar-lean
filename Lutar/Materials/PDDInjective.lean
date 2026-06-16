/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Materials/PDDInjective.lean

ROADMAP — Conjecture (fingerprint injectivity). NOT proven, NOT in locked-8.
Backs /api/a11oy/v1/materials/novelty.

-------------------------------------------------------------------------------
## Honesty verdict first (doctrine v11)

This module STATES a conjecture; it does NOT prove it. The single obligation
`pdd_injective_on_isometry_classes` is an HONEST `sorry`. This file is a
ROADMAP scaffold:

  * It is NOT folded into the locked-8 proven set
    {F1,F4,F7,F11,F12,F18,F19,F22} @ kernel c7c0ba17.
  * It is NOT imported by the library root `Lutar.lean`, so it does not enter
    `lake build`; it is tracked-`sorry` only (sorry-gate baseline bump,
    disclosed in SORRIES.md — nothing hidden).
  * Λ stays Conjecture 1; Khipu stays Conjecture 2. PDD-injectivity is a
    SEPARATE conjecture, stated here for the first time as a Lean obligation.

## Axiom disclosure (B2 discipline, lutar-lean axiom-disclosure convention)

The geometry is kept opaque: `CrystalIsometryClass`, `PDDFingerprint`, and the
fingerprint map `pdd` are introduced as uninterpreted symbols (Lean `axiom`
bindings) so the conjecture is stated abstractly without committing to a
concrete encoding. These are SIGNATURE-LEVEL declarations (a nonempty domain,
a nonempty codomain, and a total map), NOT a logical assumption that closes the
conjecture — `pdd_injective_on_isometry_classes` itself remains an HONEST
`sorry`. No proof is derived from these declarations.

The novelty endpoint /api/a11oy/v1/materials/novelty computes a REAL,
deterministic, isometry-invariant Pointwise Distance Distribution (PDD)
fingerprint and a SIGNED Khipu receipt. Those are REAL. The claim that the
fingerprint is *injective on isometry-classes* (distinct crystals up to
isometry ⇒ distinct PDD) is the CONJECTURE below — it must NOT be presented
as proven.

## Background

A periodic crystal structure is, up to isometry, an equivalence class of
point sets in ℝ³ under the Euclidean group E(3) = O(3) ⋉ ℝ³ together with
lattice periodicity. The Pointwise Distance Distribution (PDD) of Widdowson
& Kurlin is a continuous, isometry-invariant descriptor built from sorted
matrices of inter-point distances within an expanding neighbourhood; the
Average Minimum Distance (AMD) is its collapsed vector form.

Widdowson, Mosca, Pulido, Cooper & Kurlin (2022) prove the PDD is a
CONTINUOUS isometry invariant and report it distinguishes all (then) ~660k
periodic structures in the CSD with no false coincidences — strong EMPIRICAL
evidence, but NOT a completeness/injectivity proof in full generality.
Generic-completeness results (Widdowson & Kurlin 2023, NeurIPS) hold under
genericity / finite-radius hypotheses. The UNCONDITIONAL injectivity of the
PDD fingerprint over ALL isometry-classes of crystal structures remains
OPEN. That open statement is what we formalise here as a conjecture.

## References (real)

  Widdowson, D., Mosca, M.M., Pulido, A., Cooper, A.I., Kurlin, V. (2022).
    Average minimum distances of periodic point sets — foundational
    invariants for mapping periodic crystals. MATCH Commun. Math. Comput.
    Chem. 87(3), 529-559. DOI: 10.46793/match.87-3.529W.
  Widdowson, D., Kurlin, V. (2023). Recognizing rigid patterns of unlabeled
    point clouds by complete and continuous isometry invariants. CVPR /
    NeurIPS line; complete-invariant results under genericity.
  Kurlin, V. (2024). Continuous crystal invariants and the duplicate-entry
    audit of GNoME / Materials Project crystallographic databases
    (>1,200 exact-duplicate pairs detected; >10% near-duplicates).
  SZL Materials Frontier Brief (2026): novelty certificate gap #1.

Signed-off-by: SZL CTO <cto@szl-holdings.com>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/
import Mathlib.Logic.Function.Basic

namespace Lutar
namespace Materials

/-- An abstract isometry-class of a (periodic) crystal structure. We keep the
geometry opaque (a signature-level, uninterpreted nonempty type): all that
matters for the conjecture statement is that there is a well-defined notion of
equality of isometry-classes. In the running system this corresponds to a
periodic point set in ℝ³ taken modulo the Euclidean group E(3) together with
lattice periodicity. -/
axiom CrystalIsometryClass : Type

/-- The fingerprint codomain — an abstract, uninterpreted nonempty type. In the
running system this is the space of Pointwise-Distance-Distribution descriptors
(sorted distance matrices / AMD vectors) produced by the live endpoint. -/
axiom PDDFingerprint : Type

/-- The Pointwise-Distance-Distribution fingerprint map: a deterministic,
isometry-invariant total map from isometry-classes to fingerprints. This
mirrors the REAL, isometry-invariant descriptor computed by the live endpoint
/api/a11oy/v1/materials/novelty. Declared as an uninterpreted total map so the
conjecture below is a clean injectivity statement (no concrete encoding
assumed). -/
axiom pdd : CrystalIsometryClass → PDDFingerprint

/-- **CONJECTURE (PDD fingerprint injectivity). NOT PROVEN — ROADMAP.**

The PDD fingerprint is injective on isometry-classes of crystal structures:
distinct crystals up to isometry have distinct PDD fingerprints. Equivalently,
equal fingerprints force equal isometry-classes (no false coincidences /
no collisions over the full space of crystals).

This is the formal backing target for /api/a11oy/v1/materials/novelty's
`novel` verdict. It is a CONJECTURE: empirically supported on ~660k CSD
structures (Widdowson–Kurlin) and provable under genericity hypotheses, but
UNPROVEN unconditionally. It is NOT in the locked-8 and must never be claimed
as proven. -/
theorem pdd_injective_on_isometry_classes :
    Function.Injective pdd := by
  -- ROADMAP / OPEN. The deployed descriptor is real and isometry-invariant;
  -- its UNCONDITIONAL injectivity over all crystal isometry-classes is open.
  -- Tracked-`sorry` (NOT in locked-8, NOT in `lake build`).
  sorry

end Materials
end Lutar
