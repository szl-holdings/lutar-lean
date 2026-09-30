# Hugging Face dataset cards sourced from this repository

HF upgrade plan P18 makes this repository the GitHub source for two Hugging Face
datasets. Each `datasets/<id>/README.md` is a **verbatim import** of the current Hub
card (read-only fetch; nothing was written to the Hub), so GitHub holds the card
before any mirror publishes it.

| Hub dataset | Card imported from Hub revision | sha256 of the imported card |
|---|---|---|
| [`SZLHOLDINGS/lean-proofs-v1`](https://huggingface.co/datasets/SZLHOLDINGS/lean-proofs-v1) | `f877db13fd3b84d8304169c3cb27c71bd397ac64` | `9daa9425e237293187d6c176eee50118cbe15fdffce31a1fb9be682e2ec33bda` |
| [`SZLHOLDINGS/lean-theorem-tree`](https://huggingface.co/datasets/SZLHOLDINGS/lean-theorem-tree) | `8283cc8b75a54142016c8ac7fac5695903a9e6ba` | `6a11e1311a2c09b49829d650e1a17fe8b66d3de7cea72b1759c5c430bd55c019` |

Both cards declare `license: apache-2.0`, which matches this repository's
[`LICENSE`](../LICENSE). Both cards were last edited on the Hub on 2026-09-28, in the
"estate audit" Hub PRs. The dated counts in the cards are snapshots pinned to the
commits they cite. They are not live state.

## Publishing status

No workflow in this repository publishes these two datasets. Two things are missing:

1. the org-level `reusable-hf-mirror.yml` in `szl-holdings/.github` (not yet present);
2. a decision on the payload, because the Hub trees are older snapshots of this
   repository (for example, `lean-proofs-v1` holds a `Lutar/` tree of 53 files).

This repository writes no Hub repository. `anchor-szl-lake.yml` and
`conjecture-factory.yml` append receipts to the Khipu ledger in GitHub
`szl-holdings/szl-lake` (`data/khipu/lutar_lean_receipts.ndjson`), under the ledger
lock `szl-lake-ledger/lutar-lean`. szl-lake's own `hf-sync.yml` is the only writer
of `SZLHOLDINGS/szl-lake` (HF plan D1); the anchor waits for that mirror and checks
it byte for byte at an immutable Hub revision.
