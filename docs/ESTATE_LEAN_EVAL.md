# ESTATE LEAN-EVAL — the pinned benchmark doctrine (`szl.lutar.estate-lean-eval/v1`)

> **What this is:** the estate's own mathematics pinned **verbatim** as
> immutable benchmark targets — the `weil_conjectures` lean-eval pattern from
> the 2026-11-15 AxiomMath audit, applied to OUR kernel. No one benchmarks
> their own governed Lean estate against itself; we do.

## Why verbatim pinning

An LLM-training / eval corpus that quietly rewrites statements is worthless as
evidence: a "pass" against a mutated target proves nothing about the original.
So every row of `benchmark/estate_pinned_v1.jsonl` carries:

- `statement_sha256` — the verbatim declaration signature (keyword, binders,
  type, up to `:=`), hashed from raw source bytes;
- `block_sha256` — the whole declaration block, proof included;
- `source_path` + `start_line` — where the bytes live.

The check (`tools/build_estate_benchmark.py --check`, enforced by
`benchmark-contract.yml`) **re-derives everything from the repo at HEAD** and
fails on any byte drift. A statement cannot change without this corpus
changing, and the corpus cannot claim a statement the repo does not contain.
Cross-gate: the `sorry_open` row total must equal `count_sorries.py`'s
`TOTAL_SORRIES` (SORRIES.md pinned baseline 61, no-increase).

## What is pinned, and by whose authority

| Kind | Authority | Status semantics |
|---|---|---|
| `locked8` (24) | `claims/locked-formulas.v1.json` — `COMPILED_LOCKED_SURFACE` | `PROVEN` only ever from this file; carriers pinned only in `Lutar/Puriq/Formulas/ProvedFormulas.lean` |
| `theorem_u` (6) | szl-lake anchor receipt | `REAL-CONDITIONAL`; Conjecture 1 OPEN, machine-checked FALSE |
| `putnam` (66) | repo sources | `sorry_free` / `sorry_open` only — no REAL/DEMO claims (PhD gate owns those) |
| `sorry_open` (61) | `count_sorries.py` compiled scope | `OPEN`, one row per tracked sorry |

## How the loop consumes it (states, not files)

The recorded T1 doctrine: self-proving attempts run against **proof states,
not whole files.** Each `sorry_open` row identifies a target declaration; the
attempt pipeline extracts the goal state at that `sorry` (goal-state extraction
runs on the pinned toolchain in CI; the corpus pins the statements so the
extracted states always bind to a byte-stable target), asks a model for a
proof, and the candidate lands in `proposals/` staged for PhD review
(UNVERIFIED until then). A discharge:

1. replaces the tracked `sorry` with a real proof in the corpus file,
2. the sorry gate ratchets (`SORRIES.md` baseline only ever decreases),
3. the corpus regenerates and the row flips to `sorry_free` — a **visible
   benchmark diff** proving the target that changed,
4. a GREEN kernel build milestone can then be anchored into `szl-lake`
   (append-only Khipu chain via `anchor-szl-lake.yml`).

## sorry2lemma promotion

A candidate proof may be staged as a **standalone lemma** (`sorry2lemma`
pattern: the target statement is already pinned verbatim, so the lemma's type
is byte-comparable to the corpus row) inside `proposals/` — UNVERIFIED until
kernel-checked and PhD-gated. Standalone lemma sorries outside `proposals/`
would count against the no-increase gate; the mirror exists precisely so
candidates never inflate the tracked baseline.

## AXLE secondary-oracle corroboration

hatun-mcp v9 (`szl_axle_*`, 37 static tools) bridges AxiomMath's AXLE
Lean-verification endpoints as a **secondary oracle**: AXLE corroborates, it
never authorizes — the estate's local kernel stays the authorizing oracle, and
AXLE results carry `role: secondary_corroborating, authorizing: false`
fail-closed. The natural loop:

```
sorry_open row (pinned verbatim)
  → extract proof state (pinned toolchain)
  → model candidate (self-proving loop / Salad lanes)
  → local kernel check (authorizing)
  → szl_axle_check / szl_axle_verify_proof corroboration (secondary)
  → proposals/ → PhD gate → discharge → sorry-gate ratchet → szl-lake anchor
```

Citation rule unchanged: kernel-verified results are still
"kernel-verified, pending human review" until the PhD gate signs.

## Anchoring the pinning into szl-lake

The pinning itself is an anchorable milestone. Every green `benchmark-contract`
run emits a kernel-derived snapshot artifact (`estate-benchmark-snapshot-<head>`:
counts, corpus sha256, per-kind honesty — nothing else). Dispatch
`anchor-szl-lake.yml` with that green run's id plus:

```
kind=estate-benchmark
source_workflow=benchmark-contract
artifact_prefix=estate-benchmark-snapshot
snapshot_file=estate_benchmark_snapshot.json
predicate_type=https://szl-holdings/estate-benchmark-anchor/v1
```

The receipt then rides the same append-only Khipu chain (cosign keyless DSSE,
`chain_index` +1, szl-lake PR + hf-sync mirror) with milestone status
`PINNED-BASELINE` — the corpus is *pinned*, never relabelled *proven*.
