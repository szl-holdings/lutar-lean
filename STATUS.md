# STATUS.md — lutar-lean (Lean 4 Proof Kernel)

**Updated:** 2026-06-02
**Doctrine v11 — 749 / 14 / 163 — replay hash c7c0ba17**

> **Doctrine v12 (ADDITIVE, 2026-06-01) — `781 / 14 / 194`.**
> v12 = v11 + PuriqFormulaLean scaffold module. **Same 14 unique axioms**
> (identical names). New sorries are clearly-marked roadmap
> (`SORRY_PURIQ_OPEN`). **Λ remains Conjecture 1.** SLSA L1 (honest). Quechua =
> brand only. **`yuyay_v3` replay hash `bacf5443…631fc5` UNCHANGED.** Monotone:
> declarations grew (749→781), sorries grew (163→194), axioms unchanged (14→14),
> so every v11 citation stays valid. Measured by `lake build` on lutar-lean PR
> #142 head `86d9fb2c` (CI run 26758112448, build green). v11 numbers below
> remain the LOCKED reference snapshot.

---

## What's Live

- **Lean 4 proof kernel** — formal proofs of the Λ aggregator
- **Canonical numbers** — 749 declarations · 14 unique axioms (15 raw, 1 duplicate) · 163 tracked sorries (112 baseline + 51 Putnam)
- **Replay hash** — c7c0ba17
- **`lean_numbers.py`** — CI script regenerates canonical numbers on every push
- **CITATION.cff** — citable, ORCID 0009-0001-0110-4173
- **Concept DOI** — [10.5281/zenodo.19944926](https://doi.org/10.5281/zenodo.19944926)

## What's Experimental

- **Putnam sorry reduction** — 51 Putnam sorries are open; reduction in progress
- **Mathlib alignment** — periodic Mathlib upgrades may require proof adjustments

## What's Deprecated

Nothing deprecated in this repo.

---

*Co-Authored-By: Perplexity Computer Agent*
*Doctrine v11 — 749/14/163 — c7c0ba17*
