# Frontier Attack Map — lutar-lean sorry census (2026-11-17)

Status artifact for owner review. Maps all 430 raw sorry sites found by
`sorry_digest.json` into a prioritized attack plan. Nothing here changes the
lake build; this is review-only scratch unless promoted via PR.

## Current state

- SORRY_BASELINE: 60 (after #370 retires F23 STEP2)
- Locked-proven (do not touch): {F1,F4,F7,F11,F12,F18,F19,F22}
- Conjecture 1 (Lambda): machine-checked FALSE under A1-A5 (maxAgg_ne_Lambda).
  A6 bisymmetry path drafted in PR #366 (merged 980f5cf): Conjecture 1'.

## Priority spine (highest leverage first)

1. **Round13 lambda_unique (FACTORIZATION_AXIOM_GAP)** — needs only
   factorization_from_A1_A6 -> lambda_unique_of_factors (closed machinery).
   Founder-decision gate: A6 admission.
2. **Wave18 Aczel representation** — reduced to ONE lemma dyadic_image_dense
   (BKS 2208.07083 Step 2). Multi-week, NOT in Mathlib. Candidate for a
   dedicated round with a paper plan.
3. **Uniqueness.lean lutar_is_geomean** — FALSE under A1-A5. Undischargeable;
   founder decision only (documented).

## Deprecation sweep candidates

TODO on next pass: cross-reference 430 raw sites vs SORRIES.md 60-pinned set;
sites outside the pin that are dead code should be flagged for deletion
(cuts review surface without touching the gate).


## Deprecation sweep data (from sorry_digest.json, 430 sites / 163 files)

Top concentrations:
- 15 Honest_Srouwer_Brouwer.lean (round12)
- 14 CauchyNDClosure.lean (round9) + 14 PuriqFormulaLean.lean
- 13 Uniqueness.lean
- 10 PACBayes.lean
- 9 each: PhysicsGaugeSymmetry (round10), CauchyMultMono (round9), VCG.lean
- 8 each: PathIntegralAuditSum, Pachakuti_Lineage_Cohomology (round12), P_A2 (Putnam)
- 7 each: ReedSolomonSingleton, PACBayesMaterials, PACBayes/PACBayes

Sweep plan: cross-ref these 430 raw sites vs the SORRIES.md 60-pinned set;
unpinned dead-code sites get flagged for deletion PRs (cuts review surface,
gate untouched). CauchyNDClosure round9 (14 sites) is the natural first target
given Round13's sorry-free CauchyND_Closure.lean overlap.
