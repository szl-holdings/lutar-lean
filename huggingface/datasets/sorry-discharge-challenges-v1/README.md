---
license: apache-2.0
task_categories:
- text-generation
tags:
- lean
- theorem-proving
- formal-mathematics
- sorry-discharge
- szl-estate
size_categories:
- n<1K
---

# sorry-discharge-challenges-v1

Machine-readable discharge challenges for the SZL Holdings self-proving estate
loop. Each row is one gated open `sorry` from the
[szl-holdings/lutar-lean](https://github.com/szl-holdings/lutar-lean) corpus,
exported by `tools/export_sorry_challenges.py` with scope identical to the
repository's sorry-gate (`count_sorries.py`).

- **Source of truth:** the repository at the `kernel_head` recorded in
  `data/manifest.json`; the dataset is a derived read view.
- **Verification is mechanical and fail-closed:** attempts are verified ONLY by
  rebuilding the real file on the pinned toolchain. See
  `docs/SORRY_DISCHARGE_LOOP.md` in the source repository for the full
  attempt contract (ABSTAIN is first-class; no new axioms; sorry-gate is the
  ratchet).
- **Counts:** see `data/manifest.json` (`total_challenges` +
  `challenges_sha256`). The gated baseline is recorded in the repository's
  SORRIES.md scoreboard.

CARD SOURCE ONLY — this file is the in-repo source for the dataset card.
Publication to the Hub is an owner-gated dispatch; no workflow in the source
repository writes this Hub dataset.
