import Lutar.Axioms
import Lutar.Egyptian
import Lutar.Invariant
import Lutar.Bound
import Lutar.Uniqueness
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

-- v17 Quantum-error-correction lineage grafts
import Lutar.QEC.HammingFoundations
import Lutar.QEC.ShorReceiptCode
import Lutar.QEC.CSSBridge
import Lutar.QEC.KitaevSurface

import Lutar.Correlator.MatchedFilter

-- v17 Gleason + Schur modules (§XVII open obligations)
import Lutar.Lambda.SchurConcave
import Lutar.Gates.GleasonMod8
