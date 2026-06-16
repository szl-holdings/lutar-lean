# Sorry Scoreboard

_Updated 2026-06-16 00:37 UTC_

- Open `sorry` in the compiled corpus (comment-stripped): **65**
- Pinned baseline: **65** (no-increase gate)
- Target: **0** (sorry-free)
- Excluded `proposals/` scratch mirror (UNVERIFIED, not in `lake build`): **5** — disclosed, not gated (see proposals/INDEX.md)

CI (`sorry-gate`) rejects any change that increases the COMPILED-corpus count above the pinned baseline. The `proposals/` mirror holds LLM candidate proofs staged for PhD review; its sorries are reported here but excluded from the gate because they duplicate corpus originals already inside the baseline.
