import Lutar.Axioms
import Lutar.Egyptian
import Lutar.Invariant
import Lutar.Bound
import Lutar.Uniqueness
-- λ-green-strike: discoverable index of zero-sorry, Lake-verified Λ lemmas (NOT a theorem for Λ-uniqueness — Conjecture 1)
import Lutar.GreenTheorems
import Lutar.TwoWitness
import Lutar.DoctrineV3.MoralGrounding
import Lutar.DoctrineV3.MeasurabilityHonesty
import Lutar.Khipu.SummationInvariant
import Lutar.DPOFeasibility
import Lutar.PACBayes
import Lutar.Knot.ReidemeisterConjecture
-- v16 ancient-foundations grafts (b4_rosie_amaru_ancient)
import Lutar.Egyptian.HorusEye
import Lutar.Brahmi.AxisOption
import Lutar.Crt.WeightChunking
-- v16 ancient-foundations grafts (b3_a11oy_ancient)
import Lutar.Calibration.FalsePosition
import Lutar.Egyptian.AkhmimTable
import Lutar.Thresholds.QuadraticCompletion
import Lutar.PACBayes.MadhavaBound
import Lutar.Lambda.CompositionRing
-- v16 ancient-foundations grafts (b5_ouroboros_foundations)
import Lutar.Banach.BabylonianContraction
import Lutar.Banach.LiuHuiPi
import Lutar.Precision.SexagesimalRegular
import Lutar.Propagation.RelayChain
import Lutar.Transduction.ReceiptInvariant
-- v16 Feynman grafts (PR #41)
import Lutar.Feynman.FeynmanLineage
import Lutar.Feynman.PathIntegralAuditSum
-- integrity-remediation 2026-05-28: three publicly-claimed theorems + doctrine evolution
import Lutar.HUKLLA.HaltEligibility
import Lutar.OVERWATCH.ReadOnly
import Lutar.DPI.DPIBound
import Lutar.Doctrine.PublicClaims
import Lutar.Doctrine.CrossComponentInvariant
-- phd-math: R1/R2/A15/K10 (45 theorems, 0 sorry, 0 axiom)
import Lutar.Composition.TH1_Composition
import Lutar.Composition.CompositionOverhead
import Lutar.Composition.AdversarialRobustness
import Lutar.Composition.R1Tests
import Lutar.DPI.TH6_DPI_Soundness
import Lutar.DPI.MerkleDAGBuild
import Lutar.DPI.SCITTMaskEntropy
import Lutar.Topology.PersistentHomologyChain
import Lutar.PRNG.K10v2_ReplayRoot
-- v17 Wheeler delayed-choice graft
import Lutar.Wheeler.DelayedChoiceClosure
import Lutar.Shannon.DoctrineEntropy
-- khipu-consensus-roadmap: BFT 3-of-4 multi-organ signed agreement (additive,
-- 2 proof-deferred conjectures, 0 new axioms; Doctrine v12 781/14/194 -> 783/14/196)
import Lutar.KhipuConsensus
-- v17 Quantum-error-correction lineage grafts
import Lutar.QEC.HammingFoundations
import Lutar.QEC.ShorReceiptCode
import Lutar.QEC.CSSBridge
import Lutar.QEC.KitaevSurface
import Lutar.Correlator.MatchedFilter
-- v17 Gleason + Schur modules (§XVII open obligations)
import Lutar.Lambda.SchurConcave
import Lutar.Gates.Adinkra
import Lutar.Gates.GleasonMod8
-- v17.2 GraphLambda + PositionAware (GNN substrate, feat/v17-graph-lambda-substrate)
import Lutar.GraphLambda
import Lutar.PositionAware
-- phd-math-frontier: TH-V18-11 Pareto archive finite stabilization (PROVED, 0 sorry, 0 new axiom)
import Lutar.Thesis.TH_V18_11_ParetoFiniteStabilization
import Lutar.LambdaPermInvariant
-- Round 13 Λ-closure (Cauchy_ND): closable sub-lemmas (sorry-free) + terminal CONDITIONAL
-- uniqueness theorem (sorry-free) + counterexample fragment. The UNCONDITIONAL uniqueness
-- carries ONE honest, tagged open obligation (FACTORIZATION_AXIOM_GAP / needs A6 bisymmetry).
-- Λ stays Conjecture 1; no public claim flipped; axioms_unique stays 14.
import Lutar.Round13.CauchyND_Closure
import Lutar.Round13.Lambda_Uniqueness
-- PURIQ proved-formula pack (zero sorry, Mathlib-free): F1/F11/F12/F18/F19
-- (original sprint) + F4/F7/F22 (append-only/DAG/FIFO sprint 2026-06-04). Wiring
-- this into `lake build` makes CI kernel-check every PROVED PURIQ formula. The 15
-- still-open PURIQ formulas remain in Lutar/Puriq/Formulas/PuriqFormulaLean.lean
-- (NOT imported — it carries honest `sorry` placeholders). No new axiom; the
-- locked v11 count (749/14/163) is unchanged (this scope is counter-excluded).
import Lutar.Puriq.Formulas.ProvedFormulas
-- prove-wave-3 campaign: C1-C20 research candidates (sorry-free; wiring into
-- `lake build` makes CI kernel-check every Wave3 theorem). Mathlib-free modules
-- (Consensus C10-C12, MerkleKraft C8/C13/C14, InfoEstim C9/C17/C20) were ALSO
-- bare-`lean` verified locally; Tier1Mathlib (C1 Tsirelson, C2 CHSH, C6 Jensen)
-- is CI-only (Mathlib does not fit sandbox disk). Lambda (F23) stays Conjecture 1
-- (C7 conditional only, in F23_Uniqueness.lean, NOT imported). Experimental/wave3
-- scope is counter-excluded from the locked v11 count (749/14/163 @ c7c0ba17).
import Lutar.Wave3.Consensus
import Lutar.Wave3.MerkleKraft
import Lutar.Wave3.InfoEstim
-- prove-wave-4: the two Wave-4 modules below are CI-VERIFIED GREEN (lake build).
--   * LambdaBisymmetryWitness — bare-`lean` verified, Lean-core axioms only.
--   * LambdaBlockConsistency  — conditional Λ uniqueness under the WEAKER, more
--     governance-natural block-consistency axiom A6' (declared/disclosed; NOT in
--     the locked v11 kernel). Λ (F23) STAYS Conjecture 1 unconditionally.
import Lutar.Wave4.LambdaBisymmetryWitness  -- A6 discrimination witness (bare-`lean` verified, Lean-core axioms only)
import Lutar.Wave4.LambdaBlockConsistency   -- conditional Λ uniqueness on the WEAKER block-consistency axiom A6' (Mathlib-dep, CI-verified GREEN)
-- prove-wave-5: re-wire the MINIMAL Tier1Mathlib (C1 Tsirelson / C2 CHSH / C6 Jensen)
-- after dropping the non-load-bearing `c1a_tsirelson_constant` numeric remark and its
-- two extra SpecialFunctions imports (wave-4 isolated this module as the lake-build
-- culprit; wave-5 minimizes its build closure to exactly the two modules that DEFINE the
-- instantiated theorems). Signatures verified verbatim vs pinned Mathlib d7317655.
import Lutar.Wave3.Tier1Mathlib             -- C1/C2/C6 (Mathlib-dep) — wave-5 re-wire, CI-gated
-- prove-wave-5: substrate-relevant Mathlib instantiations (AM-GM dominates Λ; Cauchy–Schwarz
-- trust-vector bound). Signatures verified verbatim vs pinned Mathlib d7317655.
import Lutar.Wave5.MathlibCore
-- prove-wave-5: Mathlib-FREE discrete substrate guarantees (bare `lean` 4.13.0 verified
-- sorry-free; #print axioms shows Lean-core deps only). Conformal-coverage count law,
-- UDS collision pigeonhole, monotone optional-stopping (anti-deflation), threshold mono.
import Lutar.Wave5.DiscreteSubstrate
-- prove-wave-6: graph-substrate guarantees from the founder's favorited graph-ML repos.
-- Mathlib-FREE bare-lean cores (F-G2 GNN≤1-WL upper bound, F-G5 bounded-frontier DAG
-- termination, F-G6 relabeling-invariant graph functionals) + Mathlib-dep (F-G1 Fréchet/
-- Bourgain finite distortion, F-G3 geometric-contraction mixing promoting SpectralAdmit).
-- F-G4 Λ-graph isomorphism invariance is closed inside Lutar.GraphLambda (above).
import Lutar.Wave6.GraphSubstrate
import Lutar.Wave6.MetricSpectral
-- prove-wave-6: Mathlib-FREE info/concentration discrete cores (DPI deterministic
-- post-processing, Fano collision-forces-error, conformal-coverage conservation). The
-- analytic KL/sub-Gaussian Mathlib modules are 404 at pin d7317655 (C3/C4/C5 deferred).
import Lutar.Wave6.InfoSubstrate
-- prove-wave-6 (Mathlib bump v4.13.0 -> v4.18.0): C3 Hoeffding / C4 Azuma-Hoeffding /
-- C5 Gibbs (KL >= 0). These were honestly BLOCKED at d7317655 because
-- Mathlib.Probability.Moments.SubGaussian and Mathlib.InformationTheory.KullbackLeibler.Basic
-- were HTTP 404 there. The bump to Mathlib v4.18.0 (aa936c36, Lean v4.18.0) makes both
-- present (earliest tagged release with BOTH files). Pure term-mode re-exports; signatures
-- verified verbatim vs v4.18.0. Experimental/wave6 scope; locked v11 kernel 749/14/163 @
-- c7c0ba17 UNCHANGED; Lambda stays Conjecture 1.
import Lutar.Wave6.SubGaussianKL
-- prove-wave-7: Mathlib-FREE discrete substrate (bare `lean` verified, sorry-free;
-- #print axioms = Lean-core only). W7-4 conformal rank-count calibration/antitone backbone
-- (Vovk-Gammerman-Shafer 2005); W7-6 Doob two-sided audit envelope (Doob 1953). Disjoint
-- from wave-5/wave-6 (which closed coverage-conservation + bounded-frontier termination).
import Lutar.Wave7.DiscreteSubstrate
-- prove-wave-7: Mathlib-DEP kernel-checked. W7-1 vertex-summed graph functional iso-
-- invariance / F-G6 additive companion (Equiv.sum_comp; graph2nn You et al. ICML 2020);
-- W7-5 PAC-Bayes min<=avg<=max routing envelope (Finset.sum_le_card_nsmul /
-- card_nsmul_le_sum; McAllester COLT 1999). Signatures verified vs Mathlib v4.18.0.
import Lutar.Wave7.MathlibCore


/-!
# Lutar — root module

Re-exports the verified theorems on the Lutar Invariant Λ_k
and the Doctrine V3 §6/§7 theorems (zero sorry), plus the v16
ancient-foundations grafts: Horus-Eye dyadic encoding, Brahmi
AxisValue option type, CRT weight chunking (b4_rosie_amaru_ancient);
Egyptian false-position calibration, Akhmim/RMP 2/n threshold table,
BM 13901 completing-the-square solver, Mādhava arctan-bound for
TH14 PAC-Bayes refinement, Brahmagupta–Fibonacci 2-square
composition identity (b3_a11oy_ancient);
Babylonian (YBC 7289) sqrt iteration as Banach contraction,
Liu Hui polygon-doubling π, sexagesimal regular-number criterion,
Qhapaq Ñan chasqui relay-chain latency bound, receipt
transduction invariant (b5_ouroboros_foundations).

v16 Feynman additions (PR #41):
- `Lutar.Feynman.FeynmanLineage` — citation chain as compilable data (0 sorries, 0 axioms)
- `Lutar.Feynman.PathIntegralAuditSum` — Z_Λ over audit fiber (4 SORRY_v16_OPEN)
- `Lutar.Knot.ReidemeisterConjecture` — R1/R2 axiom; R3 proved at flat-segment level
-/

