# Estate Pinned Benchmark — `szl.lutar.estate-lean-eval/v1`

The estate's own mathematics, pinned **verbatim** as immutable benchmark
targets. This is the AxiomMath `weil_conjectures` lean-eval pattern turned on
our own kernel: statements cannot drift, and every claim the corpus makes is
machine-derived.

| File | Contents |
|---|---|
| `estate_pinned_v1.jsonl` | 147 rows: 24 locked-8 carriers · 6 Theorem-U headline decls · 66 Putnam decls · 51 sorry targets |
| `MANIFEST.json` | Counts, per-kind breakdown, corpus sha256 (self-bound) |

## Kinds and statuses (all machine-derived, never asserted)

- **`locked8`** — the 24 carrier theorems of the locked-8 formulas
  {F1,F4,F7,F11,F12,F18,F19,F22}. Status `PROVEN` comes **only** from
  `claims/locked-formulas.v1.json` (`COMPILED_LOCKED_SURFACE`); carriers are
  pinned **only** in `Lutar/Puriq/Formulas/ProvedFormulas.lean` — unbuilt
  `PuriqFormulaLean.lean` aliases are never pinned.
- **`theorem_u`** — the 6 headline Theorem-U declarations. Status
  `REAL-CONDITIONAL` per the szl-lake anchor receipt; Conjecture 1 (unconditional
  Λ-uniqueness) is OPEN and machine-checked FALSE — never relabelled.
- **`putnam`** — every decl in `Lutar/Putnam/P_[AB][0-9].lean`. Status is
  `sorry_free` / `sorry_open` only. No REAL/DEMO claims live here; the PhD gate
  owns those.
- **`sorry_open`** — every tracked `sorry` in the compiled corpus, one row per
  occurrence, `sorry_index` per declaration. These rows are what the
  self-proving loop consumes: **targets, not whole files.**

## Verify (offline, stdlib only)

```bash
python3 tools/build_estate_benchmark.py --check
```

Re-derives the corpus from the repo at HEAD and hard-fails on byte drift, then
cross-gates the sorry-row total against `count_sorries.py`'s `TOTAL_SORRIES`
(the SORRIES.md no-increase baseline). CI enforces the same via
`.github/workflows/benchmark-contract.yml`.

Each green run also uploads the kernel-derived `estate-benchmark-snapshot-<head>`
artifact (counts + corpus sha256 + per-kind honesty, nothing else) so the pinning
itself can be anchored into szl-lake (`anchor-szl-lake.yml`, kind
`estate-benchmark`, milestone status `PINNED-BASELINE` — pinned, never proven).

## Regenerate

A deliberate, visible act — the diff shows exactly which statements moved:

```bash
python3 tools/build_estate_benchmark.py
```

See `docs/ESTATE_LEAN_EVAL.md` for the doctrine and how the self-proving loop,
sorry2lemma promotion, and the AXLE secondary-oracle (hatun v9 `szl_axle_*`)
consume this corpus.
