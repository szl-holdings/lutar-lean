# Sorry Scoreboard

_Updated 2026-11-17 19:32 UTC_

- Open `sorry` in the compiled corpus (comment-stripped): **56**
- Pinned baseline: **56** (no-increase gate)
- Target: **0** (sorry-free)
- Excluded `proposals/` scratch mirror (UNVERIFIED, not in `lake build`): **6** — disclosed, not gated (see proposals/INDEX.md)

CI (`sorry-gate`) rejects any change that increases the COMPILED-corpus count above the pinned baseline. The `proposals/` mirror holds LLM candidate proofs staged for PhD review; its sorries are reported here but excluded from the gate because they duplicate corpus originals already inside the baseline.

## Baseline change log

- **57 → 56** (2026-11-17, [374](https://github.com/szl-holdings/lutar-lean/pull/374)):
  `Lutar/Innovations/round5/CodonK4Compress.lean` retired its single tracked
  `sorry` (`canonicalCodon`, the K4-orbit lex-min) by computing it as an
  explicit 4-way minimum over the diagonal Klein-four orbit (Jose & Zamudio
  2017 codon symmetry; constructor order C < A < U < G). Like its sibling
  (#373) the file was previously never compiled (ASCII `x` def bug, no
  importer) — now fixed and wired into the lake build. Zero new axioms;
  Innovations/round5 is outside the locked-8.
- **60 → 57** (2026-11-17, [#373](https://github.com/szl-holdings/lutar-lean/pull/373)):
  `Lutar/Innovations/round5/CodonRoundTrip.lean` retired its three tracked
  `sorry` obligations by filling the standard genetic-code tables verbatim
  (64 codon cases → 21 targets, Lenstra 2014 citation already on the file) and
  the canonical lex-first section (constructor order C < A < U < G); the
  round-trip theorem is proved by structural cases + definitional reduction
  (`cases aa <;> rfl`). The file — previously NEVER compiled (nothing imported
  it; its `def Codon` line used a literal ASCII `x` in place of the product
  symbol, so it could not have parsed) — is now imported from `Lutar.lean`,
  so the CI lake build machine-checks it. Zero new axioms; Innovations/round5
  is outside the locked-8.


- **61 → 60** (2026-11-17, [#370](https://github.com/szl-holdings/lutar-lean/pull/370)):
  `Lutar/Puriq/Formulas/F23_Uniqueness.lean` retired its single tracked `sorry`
  (`STEP2_MONOTONE_ADDITIVE_CONTINUOUS`) by delegating the file-local
  `monotone_additive_linear` to the sorry-free
  `Lutar.Round13.monotone_additive_linear` (rational squeeze; no continuity
  assumed; zero new axioms; same statement and signature). One compiled-corpus
  `sorry` removed; nothing else changed.
- **67 → 61** (2026-10-22, [#325](https://github.com/szl-holdings/lutar-lean/pull/325)):
  the gate was ratcheted to the measured count. `count_sorries.py` reported
  `TOTAL_SORRIES=61` outside `proposals/` at `0970b2f1` (2026-10-21), so the old
  pin of 67 would have let six new `sorry` land unnoticed. The two
  `Lutar/Materials/` ROADMAP scaffolds below still carry their tracked `sorry`
  and are inside the 61.
- **65 → 67** (Materials frontier wave): added two HONEST ROADMAP scaffolds under
  `Lutar/Materials/`, each carrying exactly one tracked `sorry`. These are
  **NOT folded into the locked-8** proven set {F1,F4,F7,F11,F12,F18,F19,F22} @
  kernel `c7c0ba17`, and are **NOT imported by `Lutar.lean`** (so they are not
  in `lake build`); they are counted by `count_sorries.py` (which walks all
  non-`proposals/` `.lean` files) and are therefore disclosed here transparently:
  - `Lutar/Materials/PDDInjective.lean` — `pdd_injective_on_isometry_classes`:
    CONJECTURE that the Pointwise-Distance-Distribution fingerprint is injective
    on isometry-classes of crystal structures. Empirically supported
    (Widdowson–Kurlin, ~660k CSD structures) and provable under genericity, but
    UNPROVEN unconditionally. Backs `/api/a11oy/v1/materials/novelty`.
  - `Lutar/Materials/PACBayesMaterials.lean` — `pac_bayes_materials_bound`:
    McAllester PAC-Bayes bound specialized to a bounded materials-regression
    risk. PROVEN-on-paper [McAllester 2003]; the machine-checked Lean proof is
    OPEN (needs a sub-Gaussian/Hoeffding step absent from pinned Mathlib
    v4.18.0, cf. `Lutar/PACBayes.lean` `MomentSubGaussian`). The bound
    COMPUTATION is exact. Backs `/api/a11oy/v1/materials/certify`.
