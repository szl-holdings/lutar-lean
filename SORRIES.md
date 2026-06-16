# Sorry Scoreboard

_Updated 2026-06-16 (Materials frontier wave)_

- Open `sorry` in the compiled corpus + tracked ROADMAP scaffolds (comment-stripped): **67**
- Pinned baseline: **67** (no-increase gate)
- Target: **0** (sorry-free)
- Excluded `proposals/` scratch mirror (UNVERIFIED, not in `lake build`): **5** — disclosed, not gated (see proposals/INDEX.md)

## Baseline change log

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

CI (`sorry-gate`) rejects any change that increases the COMPILED-corpus + tracked count above the pinned baseline. The `proposals/` mirror holds LLM candidate proofs staged for PhD review; its sorries are reported here but excluded from the gate because they duplicate corpus originals already inside the baseline.
