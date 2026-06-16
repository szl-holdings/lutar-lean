#!/usr/bin/env python3
"""Write SORRIES.md — progress scoreboard toward a sorry-free Lambda proof."""
import datetime as dt
import sys

from count_sorries import scan, total_sorries

TARGET = 0
BASELINE = 65


def main(argv):
    root = argv[1] if len(argv) > 1 else "."
    remaining = total_sorries(root)
    # Transparency: surface the EXCLUDED scratch-mirror count, never hide it.
    all_files = scan(root, include_excluded=True)
    gated_files = scan(root)
    excluded = sum(n for p, n in all_files.items() if p not in gated_files)
    now = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    md = (
        "# Sorry Scoreboard\n\n"
        f"_Updated {now}_\n\n"
        f"- Open `sorry` in the compiled corpus (comment-stripped): **{remaining}**\n"
        f"- Pinned baseline: **{BASELINE}** (no-increase gate)\n"
        f"- Target: **{TARGET}** (sorry-free)\n"
        f"- Excluded `proposals/` scratch mirror (UNVERIFIED, not in `lake build`): "
        f"**{excluded}** — disclosed, not gated (see proposals/INDEX.md)\n\n"
        "CI (`sorry-gate`) rejects any change that increases the COMPILED-corpus count "
        "above the pinned baseline. The `proposals/` mirror holds LLM candidate proofs "
        "staged for PhD review; its sorries are reported here but excluded from the gate "
        "because they duplicate corpus originals already inside the baseline.\n"
    )
    with open("SORRIES.md", "w", encoding="utf-8") as fh:
        fh.write(md)
    sys.stdout.write(md)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
