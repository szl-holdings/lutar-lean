#!/usr/bin/env python3
"""Write SORRIES.md — progress scoreboard toward a sorry-free Lambda proof.

Usage: python3 scoreboard.py [ROOT] [BASELINE]

BASELINE defaults to the sorry-gate's own pin (SORRY_BASELINE in
.github/workflows/sorry-gate.yml), so the scoreboard can never report a
baseline the gate does not enforce. An existing "## Baseline change log"
section in SORRIES.md is carried over verbatim (it is history, not output).
"""
import datetime as dt
import os
import re
import sys

from count_sorries import scan, total_sorries

TARGET = 0
GATE_WORKFLOW = os.path.join(".github", "workflows", "sorry-gate.yml")
CHANGELOG_HEADING = "## Baseline change log"
_GATE_PIN = re.compile(r'^\s*SORRY_BASELINE:\s*"?(\d+)"?\s*$', re.M)


def gate_baseline(root="."):
    """The no-increase baseline the sorry-gate workflow enforces."""
    path = os.path.join(root, GATE_WORKFLOW)
    with open(path, encoding="utf-8") as fh:
        pins = _GATE_PIN.findall(fh.read())
    if len(pins) != 1:
        raise SystemExit(f"{path}: expected exactly one SORRY_BASELINE pin, found {len(pins)}")
    return int(pins[0])


def existing_changelog(path):
    """The '## Baseline change log' section of an existing SORRIES.md, or ''."""
    try:
        with open(path, encoding="utf-8") as fh:
            text = fh.read()
    except FileNotFoundError:
        return ""
    i = text.find(CHANGELOG_HEADING)
    return text[i:].rstrip() + "\n" if i != -1 else ""


def render(remaining, baseline, excluded, now, changelog=""):
    md = (
        "# Sorry Scoreboard\n\n"
        f"_Updated {now}_\n\n"
        f"- Open `sorry` in the compiled corpus (comment-stripped): **{remaining}**\n"
        f"- Pinned baseline: **{baseline}** (no-increase gate)\n"
        f"- Target: **{TARGET}** (sorry-free)\n"
        f"- Excluded `proposals/` scratch mirror (UNVERIFIED, not in `lake build`): "
        f"**{excluded}** — disclosed, not gated (see proposals/INDEX.md)\n\n"
        "CI (`sorry-gate`) rejects any change that increases the COMPILED-corpus count "
        "above the pinned baseline. The `proposals/` mirror holds LLM candidate proofs "
        "staged for PhD review; its sorries are reported here but excluded from the gate "
        "because they duplicate corpus originals already inside the baseline.\n"
    )
    return md + ("\n" + changelog if changelog else "")


def main(argv):
    root = argv[1] if len(argv) > 1 else "."
    baseline = int(argv[2]) if len(argv) > 2 else gate_baseline(root)
    remaining = total_sorries(root)
    # Transparency: surface the EXCLUDED scratch-mirror count, never hide it.
    all_files = scan(root, include_excluded=True)
    gated_files = scan(root)
    excluded = sum(n for p, n in all_files.items() if p not in gated_files)
    now = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    out = os.path.join(root, "SORRIES.md")
    md = render(remaining, baseline, excluded, now, existing_changelog(out))
    with open(out, "w", encoding="utf-8") as fh:
        fh.write(md)
    sys.stdout.write(md)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
