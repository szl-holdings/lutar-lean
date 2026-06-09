# STATUS.md — lutar-lean (Lean 4 Proof Kernel)

**Updated:** 2026-06-02
**Doctrine v11 — 749 / 14 / 163 — replay hash c7c0ba17**

---

## What's Live

- **Lean 4 proof kernel** — formal proofs of the Λ aggregator
- **Canonical numbers** — 749 declarations · 14 unique axioms (15 raw, 1 duplicate) · 163 tracked sorries (112 baseline + 51 Putnam)
- **Replay hash** — c7c0ba17
- **`lean_numbers.py`** — CI script regenerates canonical numbers on every push
- **CITATION.cff** — citable, ORCID 0009-0001-0110-4173
- **Concept DOI** — [10.5281/zenodo.19944926](https://doi.org/10.5281/zenodo.19944926)

## What's Experimental

- **Putnam 2025 canonical set** — the 12 `Lutar/Putnam/P_A1..P_B6` files carry faithful Lean statements of the **Putnam 2025** problems with honest REAL/DEMO/OPEN labels; deferred proofs are explicit `sorry` (build warnings). An earlier internal "2023" tag was an error and is documented as drift in the file docstrings. Plus 3 kernel-clean SZL originals under `Lutar/Putnam/SZL/` (no `sorry`, no new axiom). All forced into `lake build` via the `PutnamSet` aggregator (`@[default_target]`). Never folded into the locked count.
- **Putnam sorry reduction** — open Putnam sorries remain; reduction in progress
- **Mathlib alignment** — periodic Mathlib upgrades may require proof adjustments

## What's Deprecated

Nothing deprecated in this repo.

---

*Co-Authored-By: Perplexity Computer Agent*
*Doctrine v11 — 749/14/163 — c7c0ba17*
