#!/usr/bin/env python3
"""Write SORRIES.md — progress scoreboard toward a sorry-free Lambda proof."""
import datetime as dt
import sys

from count_sorries import total_sorries

TARGET = 0


def main(argv):
    root = argv[1] if len(argv) > 1 else "."
    remaining = total_sorries(root)
    now = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    md = (
        "# Sorry Scoreboard\n\n"
        f"_Updated {now}_\n\n"
        f"- Open `sorry` (comment-stripped): **{remaining}**\n"
        f"- Target: **{TARGET}** (sorry-free)\n\n"
        "CI (`sorry-gate`) rejects any change that increases the count above the pinned baseline.\n"
    )
    with open("SORRIES.md", "w", encoding="utf-8") as fh:
        fh.write(md)
    sys.stdout.write(md)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
