# Sorry inventory (comment/string-aware)

| Metric | Value |
|---|---|
| Raw text matches (previous scan) | 566 |
| Code occurrences (comments/strings stripped) | 72 |
| Unique declarations containing sorry | 66 |
| Declared tracked (doctrine) | 163 |

## By top-level directory

| Dir | Code occurrences |
|---|---|
| Lutar | 67 |
| proposals | 5 |

## Where 163 is declared

- BOUNTY.md:12 - **Doctrine:** v11 — 749 declarations · 14 unique axioms · 163 sorries · `locked_at c7c0ba17`
- CHANGELOG.md:17 - Doctrine v11 compliance — kernel commit `c7c0ba17` (749 declarations / 14 axioms / 163 sorries)
- PROVEN_FORMULAS.md:4 Source of truth: lutar-lean@main (kernel c7c0ba17, 749 declarations / 14 unique axioms / 163 sorries).
- PROVEN_FORMULAS.md:13 **Locked kernel:** `c7c0ba17` · **749** declarations / **14** unique axioms / **163** tracked sorries · `lake build` clean
- PROVEN_FORMULAS.md:135 / Locked kernel / `749` declarations / `14` unique axioms / `163` tracked sorries · Lean `v4.13.0` · `lake build` clean /
- SECURITY.md:52 - Doctrine v11 LOCKED — kernel commit `c7c0ba17` (749 declarations / 14 axioms / 163 sorries)
- STATUS.md:11 - **Canonical numbers** — 749 declarations · 14 unique axioms (15 raw, 1 duplicate) · 163 tracked sorries (112 baseline + 51 Putnam)
- Lutar/Puriq/Formulas/README.md:5 **749 declarations · 14 unique axioms · 163 sorries**.
- platform/docs/doctrine/v12-roadmap.md:4 > **749 declarations · 14 unique axioms · 163 sorries**. Nothing in this document
- platform/docs/doctrine/v12-roadmap.md:28 > `749 → 781` declarations, `168 → 193` raw sorries (`163` public → ~`188`).

## Occurrences

| # | File | Line | Declaration | Status |
|---|---|---|---|---|
| 1 | Lutar/KhipuConsensus.lean | 179 | khipu_consensus_safety | UNCLASSIFIED |
| 2 | Lutar/KhipuConsensus.lean | 196 | khipu_consensus_liveness | UNCLASSIFIED |
| 3 | Lutar/PACBayes.lean | 270 | chernoff_bad_event_le_delta | UNCLASSIFIED |
| 4 | Lutar/PACBayes.lean | 286 | chernoff_bad_event_le_delta | UNCLASSIFIED |
| 5 | Lutar/TwoWitness.lean | 163 | double_count | UNCLASSIFIED |
| 6 | Lutar/Uniqueness.lean | 215 | lutar_is_geomean | UNCLASSIFIED |
| 7 | Lutar/CodingTheory/ReedSolomonSingleton.lean | 101 | singletonBound_upper | UNCLASSIFIED |
| 8 | Lutar/CodingTheory/ReedSolomonSingleton.lean | 163 | reedSolomonIsMDS | UNCLASSIFIED |
| 9 | Lutar/DPI/TH6_DPI_Soundness.lean | 115 | dpi_receipt_chain_entropy_bound | UNCLASSIFIED |
| 10 | Lutar/Innovations/round10/PhysicsGaugeSymmetry.lean | 158 | A5_not_forced_by_A1_A4 | UNCLASSIFIED |
| 11 | Lutar/Innovations/round12/Honest_Sorry_Brouwer.lean | 133 | honest_sorry_is_undecided | UNCLASSIFIED |
| 12 | Lutar/Innovations/round12/Identity_Ayni_Quorum.lean | 120 | ubuntu_quorum_safety | UNCLASSIFIED |
| 13 | Lutar/Innovations/round12/Pachakuti_Lineage_Cohomology.lean | 116 | H0_vanishes_iff_consistent | UNCLASSIFIED |
| 14 | Lutar/Innovations/round5/CodonK4Compress.lean | 32 | canonicalCodon | UNCLASSIFIED |
| 15 | Lutar/Innovations/round5/CodonRoundTrip.lean | 22 | geneticCode | UNCLASSIFIED |
| 16 | Lutar/Innovations/round5/CodonRoundTrip.lean | 25 | canonicalSection | UNCLASSIFIED |
| 17 | Lutar/Innovations/round5/CodonRoundTrip.lean | 31 | codon_roundtrip_lossless | UNCLASSIFIED |
| 18 | Lutar/Innovations/round5/HermesMoranIFS.lean | 17 | hermes_moran_ifs_dimension | UNCLASSIFIED |
| 19 | Lutar/Innovations/round5/TetractysHMBottleneck.lean | 22 | tetractys_hm_bottleneck | UNCLASSIFIED |
| 20 | Lutar/Innovations/round5/TetractysHMBound.lean | 22 | tetractys_hm_le_gm_le_am | UNCLASSIFIED |
| 21 | Lutar/Innovations/round5/TetractysHMBound.lean | 23 | tetractys_hm_le_gm_le_am | UNCLASSIFIED |
| 22 | Lutar/Innovations/round6/EulerFleetTopology.lean | 38 | euler_fleet_invariant | UNCLASSIFIED |
| 23 | Lutar/Innovations/round9/CauchyMultMono.lean | 321 | multiplicative_monotone_isPow | UNCLASSIFIED |
| 24 | Lutar/Innovations/round9/CauchyNDClosure.lean | 93 | lutar_is_geomean_proved | UNCLASSIFIED |
| 25 | Lutar/Materials/PACBayesMaterials.lean | 105 | pac_bayes_materials_bound | UNCLASSIFIED |
| 26 | Lutar/Materials/PDDInjective.lean | 121 | pdd_injective_on_isometry_classes | UNCLASSIFIED |
| 27 | Lutar/MechanismDesign/VCG.lean | 126 | vcgOutcome_maximises | UNCLASSIFIED |
| 28 | Lutar/MechanismDesign/VCG.lean | 159 | vcgDominantStrategyTruth | UNCLASSIFIED |
| 29 | Lutar/PACBayes/CapabilityImprovementRate.lean | 318 | capability_improvement_rate_bound | UNCLASSIFIED |
| 30 | Lutar/PACBayes/CapabilityImprovementRate.lean | 414 | kl_monotone_under_subset | UNCLASSIFIED |
| 31 | Lutar/PACBayes/MadhavaBound.lean | 131 | madhava_alt_series_bound | UNCLASSIFIED |
| 32 | Lutar/PACBayes/MadhavaBound.lean | 150 | madhava_arctan_remainder | UNCLASSIFIED |
| 33 | Lutar/PRNG/K10v2_ReplayRoot.lean | 178 | xoshiroNext_injective | UNCLASSIFIED |
| 34 | Lutar/PRNG/K10v2_ReplayRoot.lean | 189 | xoshiroOutput_distinguishes_states | UNCLASSIFIED |
| 35 | Lutar/PRNG/K10v2_ReplayRoot.lean | 202 | replayRoot_unique_in_list | UNCLASSIFIED |
| 36 | Lutar/PRNG/K10v2_ReplayRoot.lean | 288 | xoshiro_period_bound | UNCLASSIFIED |
| 37 | Lutar/Puriq/Formulas/F23_Uniqueness.lean | 128 | monotone_additive_linear | UNCLASSIFIED |
| 38 | Lutar/Puriq/Formulas/PuriqFormulaLean.lean | 993 | f23_lambda_aggregator_sound | UNCLASSIFIED |
| 39 | Lutar/Putnam/BekensteinBound.lean | 56 | bekenstein_bound_conjecture | UNCLASSIFIED |
| 40 | Lutar/Putnam/BekensteinBousso.lean | 83 | bousso_bound_conjecture | UNCLASSIFIED |
| 41 | Lutar/Putnam/P_A2.lean | 100 | putnam_A2_correct | UNCLASSIFIED |
| 42 | Lutar/Putnam/P_A2.lean | 106 | sin_ge_a_mul_parabola | UNCLASSIFIED |
| 43 | Lutar/Putnam/P_A2.lean | 111 | sin_le_b_mul_parabola | UNCLASSIFIED |
| 44 | Lutar/Putnam/P_A2.lean | 126 | ratio_limit_at_zero | UNCLASSIFIED |
| 45 | Lutar/Putnam/P_A4.lean | 66 | k_eq_one_impossible | UNCLASSIFIED |
| 46 | Lutar/Putnam/P_A4.lean | 88 | putnam_A4_correct | UNCLASSIFIED |
| 47 | Lutar/Putnam/P_A4.lean | 90 | putnam_A4_correct | UNCLASSIFIED |
| 48 | Lutar/Putnam/P_A5.lean | 55 | putnam_A5_correct | UNCLASSIFIED |
| 49 | Lutar/Putnam/P_A5.lean | 62 | f_n2_up | UNCLASSIFIED |
| 50 | Lutar/Putnam/P_A5.lean | 83 | non_alt_strictly_smaller | UNCLASSIFIED |
| 51 | Lutar/Putnam/P_A6.lean | 123 | putnam_A6_correct_pow | UNCLASSIFIED |
| 52 | Lutar/Putnam/P_B1.lean | 74 | putnam_B1_correct | UNCLASSIFIED |
| 53 | Lutar/Putnam/P_B1.lean | 87 | at_most_two_opposite_on_circle | UNCLASSIFIED |
| 54 | Lutar/Putnam/P_B1.lean | 96 | circumcenter_of_circle_points | UNCLASSIFIED |
| 55 | Lutar/Putnam/P_B2.lean | 70 | key_double_integral_pos | UNCLASSIFIED |
| 56 | Lutar/Putnam/P_B2.lean | 78 | centroid_ineq_via_double_integral | UNCLASSIFIED |
| 57 | Lutar/Putnam/P_B3.lean | 105 | putnam_B3_correct | UNCLASSIFIED |
| 58 | Lutar/Putnam/P_B3.lean | 126 | all_primes_eventually_in_S | UNCLASSIFIED |
| 59 | Lutar/Putnam/P_B4.lean | 71 | entry_bound | UNCLASSIFIED |
| 60 | Lutar/Putnam/P_B4.lean | 76 | putnam_B4_correct | UNCLASSIFIED |
| 61 | Lutar/Putnam/P_B4.lean | 90 | n2_base_case | UNCLASSIFIED |
| 62 | Lutar/Putnam/P_B5.lean | 66 | putnam_B5_correct | UNCLASSIFIED |
| 63 | Lutar/Putnam/P_B5.lean | 85 | inv_neg_one | UNCLASSIFIED |
| 64 | Lutar/Putnam/P_B5.lean | 95 | ascent_plus_descent | UNCLASSIFIED |
| 65 | Lutar/Putnam/P_B6.lean | 66 | putnam_B6_correct | UNCLASSIFIED |
| 66 | Lutar/Putnam/P_B6.lean | 68 | putnam_B6_correct | UNCLASSIFIED |
| 67 | Lutar/Round13/Lambda_Uniqueness.lean | 239 | lambda_unique | UNCLASSIFIED |
| 68 | proposals/Lutar/Innovations/round5/HermesMoranIFS.lean | 30 | hermes_moran_ifs_dimension | UNCLASSIFIED |
| 69 | proposals/Lutar/Innovations/round5/HermesMoranIFS.lean | 43 | hermes_moran_ifs_dimension | UNCLASSIFIED |
| 70 | proposals/Lutar/Innovations/round5/TetractysHMBottleneck.lean | 60 | tetractys_hm_bottleneck | UNCLASSIFIED |
| 71 | proposals/Lutar/Innovations/round5/TetractysHMBound.lean | 32 | tetractys_hm_le_gm_le_am | UNCLASSIFIED |
| 72 | proposals/Lutar/Innovations/round5/TetractysHMBound.lean | 36 | tetractys_hm_le_gm_le_am | UNCLASSIFIED |

Classes: PROOF_CANDIDATE / COUNTEREXAMPLE / ADVISORY / BLOCKED. Every closure needs a CI receipt.
