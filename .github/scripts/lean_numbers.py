#!/usr/bin/env python3
"""Canonical Lean corpus counter for szl-holdings/lutar-lean.

Trust Tier 1 reproducibility script (TRUST.md TODO). Clones (or reads) the
lutar-lean repo at its current `main` HEAD and emits a single canonical JSON of
declaration / axiom / sorry counts so that public surfaces stop drifting.

The methods here are *fixed and documented* so any agent or reviewer gets the
same numbers from the same SHA. This file is the source of truth for the
"Live numbers" line, replacing hand-maintained figures.

Usage:
  python lean_numbers.py --repo-path /path/to/lutar-lean [--out lean_numbers.json]
  python lean_numbers.py --clone --out .github/data/lean_numbers.json

Counting methods (documented, stable):
  - declarations: lines in Lutar/ and Main.lean whose initial token is one of
    {theorem, lemma, def, abbrev, instance, structure, inductive, class},
    optionally preceded by the `noncomputable` and/or `private` modifier.
  - axioms_raw: lines whose initial token is `axiom` (after optional modifiers).
  - axioms_unique: distinct axiom names among those.
  - sorries_raw: total `\\bsorry\\b` token occurrences across all .lean files.
  - sorries_noncomment: occurrences excluding lines that are pure line-comments
    (leading `--`) — i.e. `sorry` that is live proof text.
  - sorries_putnam / sorries_baseline: split by whether the file is under Putnam/.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from datetime import datetime, timezone

LUTAR_LEAN_URL = "https://github.com/szl-holdings/lutar-lean.git"

# Experimental scopes that are NOT part of the LOCKED Doctrine v11 baseline
# (749 declarations / 14 unique axioms / 163 sorries).
#
# These directories host additive, experimental work that is explicitly NOT
# folded into the v11 numbers cited verbatim across 32+ repos, the org README,
# every /healthz surface, and the published Ouroboros Thesis v20. The proofs in
# them are real and valuable; they are simply staged for a future planned
# Doctrine v12 release (see platform/docs/doctrine/v12-roadmap.md) rather than
# counted against the locked v11 baseline.
#
# Path fragments are matched os.sep-bounded against each .lean file path. To
# graduate a scope into the baseline, remove it here in the SAME PR that bumps
# .github/data/lean_numbers.json (an explicit, reviewable Doctrine release).
EXPERIMENTAL_SCOPES = (
    # PURIQ-OS agentic formula pack (Ouroboros Thesis v21) — 5 PROVED + 18 open.
    os.path.join("Lutar", "Puriq", "Formulas") + os.sep,
    # Bekenstein-bound scaffold (additive, Putnam) — 1 proved anchor + tracking sorry.
    os.path.join("Lutar", "Putnam", "BekensteinBound.lean"),
    # Agentic-loop end-to-end system proofs (prove-agentic) — additive, NOT wired
    # into Lutar.lean; new namespace Lutar.Agentic.Pipeline. P1–P6 RAG→MCP→kernel
    # pipeline theorems (Mathlib-free, sorry-free) + one declared crypto axiom
    # (hashFn_collision_resistant, disclosed like F13′). Staged for Doctrine v12.
    os.path.join("Lutar", "Agentic") + os.sep,
    # prove-coder INNOVATE pack (a11oy Code governed coder) — Mathlib-FREE bare-lean
    # verified: 26 theorems Lean-core-only + 1 collision-resistance-axiom-gated tamper
    # theorem. Additive, EXPERIMENTAL, NOT folded into the locked v11 baseline.
    os.path.join("Lutar", "Coder") + os.sep,
    # Unify layer (unify/governance-substrate-meta-theorem) — additive, NOT wired
    # into Lutar.lean; new namespace Lutar.Unify. Bundles the proven agentic-loop
    # P1-P6 guarantees into ONE governance-substrate soundness meta-theorem via a
    # monoid-action spine (Mathlib-free, no open obligations). Headline
    # governed_run_sound is fully Lean-core; P5 tamper-evidence is exposed
    # separately and reuses Agentic's single declared crypto axiom.
    os.path.join("Lutar", "Unify") + os.sep,
    # Wave8 PROVE-NOW experimental pack (prove-next10) — 10 additive theorems
    # across two PR groups: kernel-only Lean-core proofs (Ph1 axiom-disclosure,
    # M2 hash-chain, L2 min-gate deny-by-default, B1 Byzantine n=3/f=1, S2
    # Simplex/RTA safety invariant, CP1 split-conformal coverage) and Mathlib
    # proofs (Q1 density-matrix mixture PSD, Q2 Gershgorin governance bound,
    # G1 CPA minimality, L3 geometric-mean trust strict monotonicity). EXPERIMENTAL,
    # CI-green only, NOT folded into the locked v11 baseline (stays 5). Λ remains
    # Conjecture 1 (L3 asserts no uniqueness). No sorry / no open obligation.
    os.path.join("Lutar", "Wave8") + os.sep,
    # Wave9 candidate-theorem pack (wave9-experimental) — 8 additive known-theorem
    # formalizations: MA1 Gershgorin zero-eigenvalue exclusion (spectral form),
    # CP-1 Merkle/transparency-log soundness (abstract collision-resistance),
    # MC-4 Ville fixed-time anytime-valid supermartingale bound, GT-1 Menger
    # cut/path duality (cut side), OE-2 covariance-intersection PSD closure,
    # C1 Basilic BDB quorum-intersection threshold, PB1 time-uniform PAC-Bayes
    # (Ville-assembly core), IF2 robust-declassification non-interference. All
    # CI-green, Mathlib- or kernel-backed, NO sorry / NO open obligation / NO new
    # declared axiom. EXPERIMENTAL, NOT folded into the locked v11 baseline
    # (stays 5 {F1,F11,F12,F18,F19}). Λ remains Conjecture 1.
    os.path.join("Lutar", "Wave9") + os.sep,
    # Wave10 candidate-theorem pack (wave10-experimental) — 6 additive known-theorem
    # formalizations, all Mathlib-FREE / Lean-core-only (build & kernel-verify on a
    # disk-constrained host without the Mathlib cache): RA-1 Signal-Temporal-Logic
    # robustness soundness (Donzé-Maler 2010 two-sided bounds), CN-1 quorum-
    # intersection consensus safety/agreement (Lamport Paxos; Howard Flexible
    # Paxos OPODIS 2016), TE-3 DSSE search-token injectivity (Kamara-Papamanthou
    # CCS 2012, PRF injectivity as explicit HYPOTHESIS not axiom), IF-3 non-
    # interference compositionality (Goguen-Meseguer 1982; Mantel MAKS), AU-1
    # audit-replay determinism + tamper localization (Schneider 1990; Lamport
    # 1978), MR-1 mesh reachability / route monotonicity (CLRS; cf Mathlib
    # Relation.ReflTransGen). Plus a Wave10 AxiomDisclosure ledger re-asserting
    # locked_count_five = 5. All CI-green, kernel-only axioms (propext/Quot.sound
    # or none), NO sorry / NO open obligation / NO new declared axiom. EXPERIMENTAL,
    # NOT folded into the locked v11 baseline (stays 5 {F1,F11,F12,F18,F19}).
    # Λ remains Conjecture 1.
    os.path.join("Lutar", "Wave10") + os.sep,
    # Wave11 FRONTIER proven pack (wave11-frontier) — 24 additive theorems across
    # four candidate-frontier formalizations, all locally lake-built kernel-clean
    # (Lean 4.18.0 / Mathlib v4.18.0; every #print axioms is a subset of
    # {propext, Classical.choice, Quot.sound}): CF-1 GraphAutoDistInvariant
    # (Λ-graph automorphism / isomorphism SimpleGraph.dist invariance + P-GNN
    # position-encoding equivariance, You et al. 2019 arXiv:1906.04817; also
    # closes the two formerly `:= True` PositionAware obligations), CF-2
    # OuroKVCacheSlots (looped-LM KV-cache slot-index bijection Fin T × Fin L ≃
    # Fin (T·L) via finProdFinEquiv, decode-equivalence, required size T·L, and
    # the undersized-cache collision; Antizana/ouro-cache-fix, Ouro
    # arXiv:2510.25741), CF-3 OuroLoopEarlyExit (loop fixed-point uniqueness +
    # quantitative kᵗ/(1−k) early-exit error envelope + convergence via Mathlib
    # ContractingWith; Banach 1922, DEQ arXiv:1909.01377), CF-5
    # ImmuneNeymanPearsonOpt (DISCRETE/finite Neyman-Pearson most-powerful LRT
    # optimality via the pointwise sign lemma; Neyman-Pearson 1933,
    # Cohen-Rosenfeld-Kolter arXiv:1902.02918 — the measure-theoretic
    # Gaussian-shift sorry₁ in Robustness/CertifiedRadius.lean stays OPEN). Plus a
    # Wave11 AxiomDisclosure ledger re-asserting locked_count_five = 5 and
    # wave11_theorem_count = 24. All CI-green, kernel-only axioms, NO sorry /
    # NO open obligation / NO new declared axiom. EXPERIMENTAL, NOT folded into
    # the locked v11 baseline (stays 5 {F1,F11,F12,F18,F19}). Λ remains
    # Conjecture 1.
    os.path.join("Lutar", "Wave11") + os.sep,
    # Wave13 full proof-sweep pack (wave13-sweep) — additive, EXPERIMENTAL, NOT folded
    # into the locked v11 baseline (stays 5 {F1,F11,F12,F18,F19}). Three kernel-clean
    # theorems (every #print axioms is a subset of {propext, Classical.choice,
    # Quot.sound}): quorum_agreement_single_valued_vote (the SIMPLIFIED non-Byzantine
    # single-valued-vote shadow of quorum agreement — explicitly NOT Khipu Conjecture 2,
    # which stays open in Innovations/round12/Identity_Ayni_Quorum.lean), and
    # hm_bottleneck_clean (clean x_i^{-1} statement of the Tetractys harmonic-mean
    # bottleneck; Hardy-Littlewood-Polya 1934 sec 2.5). The in-tree close of
    # findReplayRoot_complete (Lutar/PRNG/K10v2_ReplayRoot.lean, via List.find?_isSome)
    # is a BASELINE edit (-1 live sorry), recorded by bumping lean_numbers.json in this
    # same PR. Λ remains Conjecture 1; Byzantine BFT safety remains Khipu Conjecture 2.
    os.path.join("Lutar", "Wave13") + os.sep,
    # Wave14 frontier pack (wave14-frontier) — additive, EXPERIMENTAL, NOT folded into the
    # locked v11 baseline (stays 5 {F1,F11,F12,F18,F19}). Four files, nine kernel-clean
    # theorems (every #print axioms ⊆ {propext, Classical.choice, Quot.sound}; NO sorry /
    # NO new declared axiom). Each is a clean COMPANION upgrading an existing tab without
    # editing the baseline file (whose tracked sorrys stay honest):
    #   • LeibnizRemainder      (CF-18) — alternating-series / Mādhava remainder bound
    #                             (PACBayes/MadhavaBound; Mathlib Antitone.alternating_series).
    #   • ReedSolomonDistance   (CF-19) — RS MDS distance LOWER bound (achievability half of
    #                             Singleton; CodingTheory/ReedSolomonSingleton). The Singleton
    #                             UPPER bound / full MDS equality (Vandermonde rank) stays sorry.
    #   • VCGEfficiency         (CF-20) — VCG efficient-outcome maximality + truthfulness core
    #                             (clean Finset.exists_max_image route; the in-tree VCG.lean uses
    #                             a non-existent Finset.argmax and does not compile / is unwired).
    #   • LogSumInequality      (CF-21) — Cover–Thomas log-sum inequality + Gibbs' inequality
    #                             (the correctly-stated DPI core; the DPO klDivergence/pinsker
    #                             statements remain FALSE-as-stated for lack of a simplex hyp).
    # Λ remains Conjecture 1; Byzantine BFT safety remains Khipu Conjecture 2.
    os.path.join("Lutar", "Wave14") + os.sep,
    # Wave15 frontier pack (wave15-frontier) — additive, EXPERIMENTAL, NOT folded into the
    # locked v11 baseline (stays 5 {F1,F11,F12,F18,F19}). Three files, kernel-clean theorems
    # (every #print axioms ⊆ {propext, Classical.choice, Quot.sound}; NO sorry / NO new
    # declared axiom). Each is a clean COMPANION upgrading an existing tab without editing the
    # baseline file (whose tracked sorrys/axioms stay honest):
    #   • KLDivergenceSimplex (CF-22) — KL(p‖q) ≥ 0 ON THE SIMPLEX (∑p=∑q=1, p,q>0): the
    #                       CONDITIONAL repair of the FALSE-as-stated DPO klDivergence_nonneg
    #                       axiom, a direct corollary of Wave14 CF-21 gibbs_inequality. The
    #                       baseline axiom token DPOFeasibility.klDivergence_nonneg is UNTOUCHED;
    #                       dpo_klDivergence_nonneg_on_simplex restates the repair in the DPO
    #                       file's own klDivergence symbol. This is a NEW conditional theorem,
    #                       NOT a closure of the unconditional (still-false) axiom.
    #   • PinskerRoadmap     (CF-23) — Pinsker building blocks (gibbs_term_lower per-term bound +
    #                       klSum_lower_by_mass_gap summed bound) + HONEST roadmap. Full
    #                       conditional Pinsker (½‖p−q‖₁² ≤ KL) is NOT proven — the binary-bin
    #                       calculus + DPI reduction are not in Mathlib v4.18.0; nlinarith with
    #                       log≤x−1 provably fails. DPOFeasibility.pinsker stays FALSE-as-stated,
    #                       axiom token UNTOUCHED.
    #   • BisymmetryCut1     (CF-24) — CUT-1 partial: IsBisymmetric2 as a CHECKABLE PREDICATE
    #                       (NOT the declared Puriq.F23.A6_bisymmetric axiom token),
    #                       geoBin_isBisymmetric (geometric-mean witness, NNReal rpow upgrade of
    #                       the Wave4 decide-on-ℕ witness), and lambda_unique_of_bisymmetric_
    #                       separable (axiom-free CUT-1→CUT-2 bridge via lambda_unique_of_separable).
    #                       The full bisymmetry⇒quasi-arithmetic representation is deferred roadmap.
    # Λ remains Conjecture 1 (unconditional uniqueness FALSE); Byzantine BFT safety remains
    # Khipu Conjecture 2. locked-proven stays 5; nothing folded in.
    os.path.join("Lutar", "Wave15") + os.sep,
    # Wave16 frontier pack (wave16-frontier) — additive, EXPERIMENTAL, NOT folded into the
    # locked v11 baseline. Four files under Lutar/Wave16/, all kernel-clean (#print axioms ⊆
    # {propext, Classical.choice, Quot.sound}), NO sorry, NO new declared axiom token:
    #   • PinskerConvexity.lean  (CF-23 advance): binary_inv_sum_ge_four — the binary-entropy
    #     convexity crux g''(p)=1/p+1/(1-p)-4 ≥ 0 that Wave15 flagged as the missing piece of
    #     the binary Pinsker derivative argument; + tightness at p=1/2. Full Pinsker still NOT
    #     proven (MVT chain deferred); DPOFeasibility.pinsker stays FALSE-as-stated, UNTOUCHED.
    #   • Cut1MeanAxioms.lean     (CF-24 advance): geoBin_idem/comm/homog/mono_left — the
    #     geometric-mean generator satisfies the full Aczél quasi-arithmetic mean axioms
    #     (idempotency, symmetry, homogeneity, monotonicity), complementing Wave15's bisymmetry
    #     witness. Full bisymmetry⇒generator representation still DEFERRED roadmap; Λ STAYS
    #     Conjecture 1 (unconditional uniqueness FALSE).
    #   • LambdaScaleInvariance.lean (CF-25, MPP arXiv:2310.02994 / Abacus-adjacent): Λ
    #     product-multiplicativity Λ(c⊙x)=Λ(c)·Λ(x) ⇒ MPP normalization-invariance / scale
    #     robustness. Genuine new theorems about Λ (not the A2 uniform-scale axiom).
    #   • AbacusPlaceValue.lean   (CF-26, mcleish7/arithmetic arXiv:2405.17399, MIT):
    #     Abacus positional-encoding well-posedness — place-value recurrence (Horner) +
    #     zero-string anchor. The non-overflow bound abacusVal<bⁿ is DEFERRED roadmap (no
    #     in-tree lemma precedent; honestly documented, NOT faked).
    # locked-proven stays 5; nothing folded in.
    os.path.join("Lutar", "Wave16") + os.sep,
    # Wave17 frontier pack (wave17-frontier) — additive, EXPERIMENTAL, NOT folded into the
    # locked v11 baseline. Three files under Lutar/Wave17/, all kernel-clean (#print axioms ⊆
    # {propext, Classical.choice, Quot.sound}; NO new axiom token; NO sorry):
    #   • Wave17.BinaryPinsker  (CF-23) — the FULL binary (two-bin) Pinsker inequality
    #     2(p-q)² ≤ KL_bin(p,q), assembling Wave16's g''(p)=1/p+1/(1-p)-4≥0 convexity crux into the
    #     complete mean-value/monotone-derivative chain (deriv, second deriv, MonotoneOn /
    #     AntitoneOn around the minimiser p=q). This is the CONDITIONAL two-bin case; the
    #     UNCONDITIONAL simplex DPO axiom `pinsker` stays FALSE-as-stated, token UNTOUCHED. The
    #     remaining gap to full simplex Pinsker is the data-processing reduction (CF-23-FULL).
    #   • Wave17.MonDEQWellPosed (CF-27) — monotone-operator equilibrium net well-posedness
    #     (uniqueness): a strongly-monotone operator (m>0) on (Fin n → ℝ) is injective, so the
    #     equilibrium z=G(z) has at most one solution (Winston-Kolter arXiv:2006.08591;
    #     pattern-only, NO code copied). Existence half = CF-27-FULL roadmap.
    #   • Wave17.RecurrentDepth (CF-28) — recurrent-depth contraction amplification: a K-Lipschitz
    #     recurrent block iterated r times is Kʳ-Lipschitz, with antitone depth constant for a
    #     contraction (mcleish7/retrofitting-recurrence Apache-2.0, arXiv:2511.07384;
    #     concept-only). Distinct from CF-13 input-Lipschitz equilibrium.
    # locked-proven stays 5; Λ stays Conjecture 1; nothing folded in.
    os.path.join("Lutar", "Wave17") + os.sep,
    # Wave18 frontier pack (wave18-cut1) — additive, EXPERIMENTAL, NOT folded into the
    # locked v11 baseline (stays 5 {F1,F11,F12,F18,F19}). Two files under Lutar/Wave18/, all
    # kernel-clean (#print axioms in every theorem ⊆ {propext, Classical.choice, Quot.sound}),
    # NO sorry, NO new declared axiom token, each compiled locally to ZERO errors against the
    # cached Mathlib v4.18.0 oleans. CF-29 = the Aczél quasi-arithmetic REPRESENTATION theorem,
    # honest forward construction toward CUT-1:
    #   • AczelRepresentation.lean — `IsQuasiArithmetic2` representation predicate; the BKS
    #     dyadic-midpoint recursion `IsDyadicMidpointGen`; the COMPLETE soundness/only-if
    #     direction (quasiArith_reflexive/symmetric/bisymmetric/dyadic_recursion/strictMono_left:
    #     a φ-quasi-arithmetic mean satisfies all four Aczél axioms + the recursion); the analytic
    #     heart generator_collapse_affine / generator_unique_up_to_affine (generator-uniqueness
    #     up to affine via Round13 monotone_additive_linear rational squeeze, NO continuity); the
    #     Mathlib-backed continuous-extension bridge gen_continuous_of_denseRange; and the log
    #     generator endpoint expMidpoint_eq_geom (= √(xy)).
    #   • Cut1Chain.lean — the A2 1-homogeneity pin expMidpoint_homogeneous + expMidpoint_idem +
    #     log_generator_pins_geometric (geometric mean = unique homogeneous q.a. mean), and the
    #     axiom-free conditional CUT-1 conclusion cut1_conditional_lambda re-exported through the
    #     Wave15 bisymmetry bridge lambda_unique_of_bisymmetric_separable (bisymmetry as a
    #     CHECKABLE property, NO A6 axiom token).
    # The ONLY remaining gap to full CUT-1 = the topological dyadic_image_dense lemma (BKS
    # arXiv:2208.07083 Step 2; NOT in Mathlib v4.18.0; honestly documented, NOT faked, NO axiom).
    # Λ UNCONDITIONAL uniqueness STAYS Conjecture 1 (machine-checked FALSE).
    os.path.join("Lutar", "Wave18") + os.sep,
    # Wave19 frontier pack (wave19-cut1-density) — additive, EXPERIMENTAL, NOT folded into the
    # locked v11 baseline (stays 5 {F1,F11,F12,F18,F19}). Files under Lutar/Wave19/. Builds the
    # MISSING density engine of BKS arXiv:2208.07083 Lemma 6 Step 2: the
    # "countably-many-pairwise-disjoint-nonempty-opens on a separable line" contradiction engine
    # (countable_of_pairwiseDisjoint_open / false_of_uncountable_pairwiseDisjoint_Ioo), the
    # gap-to-disjoint-intervals BKS map, and the dyadic_image_dense assembly. NO sorry, NO new
    # axiom token. Λ UNCONDITIONAL uniqueness STAYS Conjecture 1 (machine-checked FALSE).
    os.path.join("Lutar", "Wave19") + os.sep,
    # Wave20 density PRIMITIVES pack (wave20-density-primitives) — additive, EXPERIMENTAL, NOT
    # folded into the locked v11 baseline (stays 5 {F1,F11,F12,F18,F19}). Two files under
    # Lutar/Wave20/, the standalone reusable engines behind BKS arXiv:2208.07083 Lemma 6 Step 2.
    # DisjointOpens.lean = PRIMITIVE A: pairwise-disjoint nonempty open sets are countable
    # (self-contained rational-injection proof over ℝ + general separable-space packaging +
    # uncountable/False corollaries + the Set.Ioo interval form). Accumulation.lean = PRIMITIVE B:
    # the perfect-nonempty ⇒ uncountable engine (Cantor injection), the
    # closed+no-isolated-points ⇒ perfect ⇒ uncountable bridge, the two-sided-accumulation
    # predicate + its bridge to Mathlib AccPt, reducing BKS bullet 2 to ONE named residual
    # (B-residual: closure of dyadic image contains a nonempty perfect set of two-sided
    # accumulation points). NO sorry, NO new axiom token; all #print axioms ⊆ {propext,
    # Classical.choice, Quot.sound}. Λ UNCONDITIONAL uniqueness STAYS Conjecture 1.
    os.path.join("Lutar", "Wave20") + os.sep,
    # Wave21 frontier pack (wave21-cut1-final) — additive, EXPERIMENTAL, NOT folded into the
    # locked v11 baseline (stays 5 {F1,F11,F12,F18,F19}). Files under Lutar/Wave21/. CLOSES the
    # FINAL residual of BKS arXiv:2208.07083 Lemma 6 Step-2 (dyadic_image_dense): the (B) residual
    # "uncountably many two-sided accumulation points" is discharged kernel-clean via the LIGHT
    # monotone-extension route of the parent paper arXiv:2107.07391 Theorem 8 — NO perfect-set /
    # Cantor machinery. Uncountable.lean proves: left/right one-sided-gap points of any H ⊆ ℝ are
    # countable (rational-injection); a non-two-sided point is a one-sided-gap point; hence an
    # uncountable H has uncountably many two-sided accumulation points; and a STRICTLY monotone
    # g : ℝ → ℝ has uncountable range (injects the continuum Ioo 0 1, Cardinal.mk_Ioo_real).
    # DyadicImageDense.lean assembles dyadic_image_dense_complete (B internal; only the (C-order)
    # gap-shift ordering remains a stated structural hypothesis). Cut1Final.lean splices into
    # Wave18 gen_continuous_of_denseRange (continuous BKS generator) and re-exports the CONDITIONAL
    # cut1_conditional_lambda_closed. No proof placeholders, NO new axiom token; all #print axioms
    # ⊆ {propext, Classical.choice, Quot.sound}. Λ UNCONDITIONAL uniqueness STAYS Conjecture 1
    # (machine-checked FALSE) — closing CUT-1 makes the CONDITIONAL Λ chain axiom-clean end to end,
    # NOT unconditional. Locked-proven set STAYS EXACTLY 5.
    os.path.join("Lutar", "Wave21") + os.sep,
    # Wave22 frontier pack (wave22-cut1-corder) — additive, EXPERIMENTAL, NOT folded into the
    # locked v11 baseline (stays 5 {F1,F11,F12,F18,F19}). Files under Lutar/Wave22/. CLOSES the ONE
    # honest residual of CUT-1 carried by Wave21's dyadic_image_dense_complete: the BKS Fourth-step
    # (C-order) gap-shift ordering R s <= L t (arXiv:2107.07391 Theorem 8, eqs (8)-(9)).
    # GapShiftOrdering.lean derives the discrete midpoint chain F (f a)(f c) <= F (f b)(f d) from
    # the generator recursion F (f a)(f b) = f((a+b)/2) + monotone f, and the monotone-limit
    # passage le_of_tendsto_of_tendsto. CorderClosure.lean constructs the (C-order) endpoint data
    # L a = F X a, R a = F Y a (nonemptiness from phi,psi strict mono; the gap-shift is DERIVED via
    # corder_gapshift from convergent gap sequences + continuity of psi, NOT re-assumed) and packs
    # it into the exact existential hC shape Wave21 requires. Cut1Corder.lean discharges that hC,
    # yielding dyadic_image_dense_corder_closed (full density), continuous_of_corder_closed and
    # continuous_of_corder_fully_derived (continuous BKS generator with the gap-shift fully derived).
    # LambdaConditional.lean STRENGTHENS the CONDITIONAL Lambda result: cut1_sharp_conditional_lambda
    # drops the bisymmetry hypothesis (proved redundant by bisymmetry_is_redundant) and the
    # unit-normalization f_i 1 = 1 (derived from A3 + separability + multiplicativity via
    # slice_one_eq_one_of_sep), leaving the WEAKEST checkable hypothesis set
    # {A1-A5}+separability+slice-multiplicativity+slice-monotonicity. No proof placeholders, NO new
    # axiom token; all #print axioms subset {propext, Classical.choice, Quot.sound}. CUT-1 is now
    # FULLY closed on its stated CHECKABLE hypotheses; Lambda UNCONDITIONAL uniqueness STAYS
    # Conjecture 1 (machine-checked FALSE). Locked-proven set STAYS EXACTLY 5.
    os.path.join("Lutar", "Wave22") + os.sep,
    # Wave23 frontier pack (wave23-bft-safety) — additive, EXPERIMENTAL, NOT folded into the
    # locked v11 baseline (stays 5 {F1,F11,F12,F18,F19}). Files under Lutar/Wave23/. Attacks the
    # GENUINE open conjecture (Khipu Conjecture 2, ubuntu_quorum_safety / khipu_consensus_safety):
    # Byzantine quorum SAFETY. UNCONDITIONAL safety stays Conjecture 2 (a faulty organ can
    # equivocate; n <= 3f is impossible per Lamport-Shostak-Pease, formalized in Lutar/Wave8). We do
    # NOT attempt the false unconditional statement. QuorumSafety.lean identifies the WEAKEST
    # CHECKABLE hypothesis that turns quorum safety into a THEOREM: honest non-equivocation under
    # signed votes (HonestNonEquivocation) — the BFT analog of slice-multiplicativity for Lambda.
    # Votes are a RELATION (faulty organs MAY equivocate, unlike the Wave13 total-function shadow);
    # only honest organs are single-valued. exists_honest_of_card_gt / exists_honest_in_inter
    # DISCHARGE the non-faulty-witness residual that Round12 AyniQuorum.ubuntu_quorum_safety and the
    # kernel KhipuConsensus.khipu_consensus_safety left as proof-deferred (Finset.not_subset +
    # card_le_card). Reusing the in-tree placeholder-free quorum_intersection_honest
    # (Round12, n >= 3f+1 ==> |Q1 cap Q2| > f), khipu_quorum_safety_conditional proves AGREEMENT
    # (no split-brain): two quorums of size >= n-f certifying v1,v2 ==> v1 = v2.
    # subsumes_single_valued_shadow re-derives the Wave13 single-valued shadow from the
    # Byzantine-aware theorem (strict generality). All #print axioms subset {propext,
    # Classical.choice, Quot.sound}; NO new axiom token; no proof placeholders. The result is
    # CONDITIONAL on {n >= 3f+1, |faulty| <= f, |Qi| >= n-f, honest non-equivocation}; UNCONDITIONAL
    # Byzantine BFT safety STAYS Conjecture 2. Locked-proven set STAYS EXACTLY 5; Lambda STAYS
    # Conjecture 1 (machine-checked FALSE).
    os.path.join("Lutar", "Wave23") + os.sep,
    # Wave24 admissibility-membership certification (wave24-admissibility-certificate) —
    # additive, EXPERIMENTAL, NOT folded into the locked v11 baseline (stays 5
    # {F1,F11,F12,F18,F19}). One file, three kernel-clean theorems formalizing the GPD
    # Adm-membership certifier as a structure + a first Semantic Linearizability property
    # (single linearization point: at most one verdict commits), proved BY REDUCTION to
    # Wave23 khipu_quorum_safety_conditional (NO new mathematics). Intended #print axioms
    # ⊆ {propext, Classical.choice, Quot.sound}; NO sorry / NO new declared axiom. CONDITIONAL
    # (inherits Wave23 hypotheses); unconditional BFT safety stays Khipu Conjecture 2; Λ
    # remains Conjecture 1.
    os.path.join("Lutar", "Wave24") + os.sep,
    # Theorem-U pack (theorem-u-kernel) — additive, EXPERIMENTAL, NOT folded into the locked
    # v11 baseline (stays 5 {F1,F11,F12,F18,F19}). Files under Lutar/Uniqueness/, all kernel-clean
    # (every #print axioms subset {propext, funext, Classical.choice, Quot.sound}), no proof
    # placeholders, NO new declared axiom token. Reframes the TARGET of Lambda-uniqueness as the
    # audit-invariant equivalence ~Lambda (LambdaEquiv): two aggregators are ~Lambda exactly when
    # they share the canonical audit-probe invariant; lambdaEquiv_equivalence proves it is a genuine
    # Equivalence (refl/symm/trans), instDecidableLambdaEquiv gives it a Decidable instance, and
    # lambdaEquiv_nondegenerate is the ANTI-VACUITY guard (the proven A1-A5 counterexample maxAgg is
    # NOT ~Lambda to Lambda 2, reusing the exact rpow script of Round13.maxAgg_ne_Lambda — so
    # "uniqueness modulo ~Lambda" is non-trivial, not vacuously true). Identifiability.lean bundles
    # FactorAssumptions / SeparableAssumptions / IdentifiabilityAssumptions (IA) with the bridges
    # factorAssumptions_to_IA / separableAssumptions_to_IA. TheoremU.lean lands Theorem U BY
    # REDUCTION to the already-proven Round13 conditional theorems lambda_unique_of_separable /
    # lambda_unique_of_factors: CorollaryU1/U2, identifiability_forces_lambda, TheoremU_LambdaUnique
    # (IA-solutions are ~Lambda), TheoremU_LambdaUnique_eq (strict =), lambda_equiv_to_eq_of_anchored
    # (gauge upgrade under Anchored/Normalized). AxiomCheck.lean is the axiom-hygiene ledger mirroring
    # Wave9/AxiomDisclosure. Conjecture1_LambdaUnique ships statement-only (a Prop, NO proof): the
    # UNCONDITIONAL statement stays OPEN / machine-checked FALSE as stated, Lambda STAYS Conjecture 1.
    # Locked-proven set STAYS EXACTLY 5.
    os.path.join("Lutar", "Uniqueness") + os.sep,
)


def _is_experimental(path: str) -> bool:
    """True if `path` lives in an experimental scope excluded from the v11 baseline.

    `path` is a repo-relative path (e.g. 'Lutar/Puriq/Formulas/X.lean'). A scope
    ending in os.sep is a directory prefix; otherwise it is an exact file.
    """
    norm = os.path.normpath(path)
    for scope in EXPERIMENTAL_SCOPES:
        if scope.endswith(os.sep):
            if (norm + os.sep).startswith(scope):
                return True
        elif norm == os.path.normpath(scope):
            return True
    return False

DECL_RE = re.compile(
    r"^(?:private\s+)?(?:noncomputable\s+)?(?:private\s+)?"
    r"(theorem|lemma|def|abbrev|instance|structure|inductive|class)\b"
)
AXIOM_RE = re.compile(r"^(?:private\s+)?axiom\s+([A-Za-z_][A-Za-z0-9_']*)")
SORRY_RE = re.compile(r"\bsorry\b")
COMMENT_LINE_RE = re.compile(r"^\s*--")


def iter_lean_files(root: str):
    base = os.path.join(root, "Lutar")
    for dirpath, _dirs, files in os.walk(base):
        for fn in files:
            if fn.endswith(".lean"):
                full = os.path.join(dirpath, fn)
                rel = os.path.relpath(full, root)
                # Skip experimental scopes — they do not roll into v11 numbers.
                if _is_experimental(rel):
                    continue
                yield full
    main = os.path.join(root, "Main.lean")
    if os.path.exists(main):
        yield main


def count(root: str) -> dict:
    declarations = 0
    axioms_raw = 0
    axiom_names: set[str] = set()
    sorries_raw = 0
    sorries_noncomment = 0
    sorries_putnam = 0
    sorries_baseline = 0

    for path in iter_lean_files(root):
        is_putnam = f"{os.sep}Putnam{os.sep}" in path
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            for line in fh:
                if DECL_RE.match(line):
                    declarations += 1
                m = AXIOM_RE.match(line)
                if m:
                    axioms_raw += 1
                    axiom_names.add(m.group(1))
                hits = len(SORRY_RE.findall(line))
                if hits:
                    sorries_raw += hits
                    if not COMMENT_LINE_RE.match(line):
                        sorries_noncomment += hits
                    if is_putnam:
                        sorries_putnam += hits
                    else:
                        sorries_baseline += hits

    return {
        "declarations": declarations,
        "axioms_raw": axioms_raw,
        "axioms_unique": len(axiom_names),
        "axiom_names": sorted(axiom_names),
        "sorries_raw": sorries_raw,
        "sorries_noncomment": sorries_noncomment,
        "sorries_putnam": sorries_putnam,
        "sorries_baseline": sorries_baseline,
    }


def git_head_sha(root: str) -> str:
    try:
        out = subprocess.check_output(
            ["git", "-C", root, "rev-parse", "HEAD"], text=True
        ).strip()
        return out
    except Exception:
        return "unknown"


def main() -> int:
    ap = argparse.ArgumentParser(description="Canonical lutar-lean corpus counter.")
    ap.add_argument("--repo-path", help="Path to an existing lutar-lean checkout.")
    ap.add_argument("--clone", action="store_true", help="Shallow-clone main first.")
    ap.add_argument("--ref", default="main", help="Branch/SHA to count (with --clone).")
    ap.add_argument("--out", help="Write JSON here (default: stdout).")
    args = ap.parse_args()

    tmp = None
    repo_path = args.repo_path
    if args.clone or not repo_path:
        tmp = tempfile.mkdtemp(prefix="lutar-lean-")
        subprocess.check_call(
            ["git", "clone", "--depth", "1", "--branch", args.ref, LUTAR_LEAN_URL, tmp]
        )
        repo_path = tmp

    if not os.path.isdir(os.path.join(repo_path, "Lutar")):
        print(f"error: {repo_path} has no Lutar/ directory", file=sys.stderr)
        return 2

    sha = git_head_sha(repo_path)
    numbers = count(repo_path)
    payload = {
        "schema": "szl.lean_numbers/v1",
        "repo": "szl-holdings/lutar-lean",
        "ref": args.ref,
        "sha": sha,
        "measured_at_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "method": "see .github/scripts/lean_numbers.py docstring (fixed grep-equivalent regexes)",
        "numbers": numbers,
    }

    out_json = json.dumps(payload, indent=2) + "\n"
    if args.out:
        os.makedirs(os.path.dirname(args.out) or ".", exist_ok=True)
        with open(args.out, "w", encoding="utf-8") as fh:
            fh.write(out_json)
        print(f"wrote {args.out} @ {sha}")
    else:
        sys.stdout.write(out_json)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
