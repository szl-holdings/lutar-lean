#!/usr/bin/env python3
"""Count `sorry` tokens in .lean files and enforce a no-increase baseline.

Usage: python3 count_sorries.py [ROOT] [BASELINE]
Prints per-file counts and TOTAL_SORRIES=N. Exit 1 if N > BASELINE.
Comments (-- line, /- block -/) are stripped before counting.

Scope: the baseline counts the COMPILED corpus only — i.e. the same scope the
canonical number-accounting (.github/scripts/lean_numbers.py) uses. The
`proposals/` directory is an UNVERIFIED, NOT-compiled, NOT-in-`lake build`
scratch mirror of corpus files: it holds LLM-generated candidate proofs staged
for PhD review + diff against the originals (see proposals/INDEX.md, PR #244).
Those mirror copies still carry the originals' `sorry`s, so counting them would
double-count tracked corpus sorries that already sit inside the baseline. They
are therefore EXCLUDED from the gated total — but reported separately below so
the number stays fully transparent (no silent hiding).
"""
import os, re, sys

_TOKEN = re.compile(r"\bsorry\b")

# UNVERIFIED scratch mirror, not part of the compiled corpus -> excluded from the
# gated baseline (still reported separately). os.sep-bounded directory prefix.
_EXCLUDED_DIRS = ("proposals",)


def _strip_comments(text):
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    lines = []
    for line in text.splitlines():
        i = line.find("--")
        if i != -1:
            line = line[:i]
        lines.append(line)
    return "\n".join(lines)


def count_file(path):
    try:
        with open(path, encoding="utf-8", errors="replace") as fh:
            return len(_TOKEN.findall(_strip_comments(fh.read())))
    except OSError:
        return 0


def _is_excluded(root, dirpath):
    rel = os.path.relpath(dirpath, root)
    first = os.path.normpath(rel).split(os.sep)[0]
    return first in _EXCLUDED_DIRS


def scan(root=".", include_excluded=False):
    per_file = {}
    for dirpath, _dirs, files in os.walk(root):
        if os.sep + ".git" in dirpath:
            continue
        if not include_excluded and _is_excluded(root, dirpath):
            continue
        for name in files:
            if name.endswith(".lean"):
                p = os.path.join(dirpath, name)
                n = count_file(p)
                if n:
                    per_file[p] = n
    return per_file


def total_sorries(root="."):
    return sum(scan(root).values())


def main(argv):
    root = argv[1] if len(argv) > 1 else "."
    baseline = int(argv[2]) if len(argv) > 2 else None
    per_file = scan(root)
    total = sum(per_file.values())
    for p, n in sorted(per_file.items(), key=lambda kv: -kv[1]):
        print(f"{n:5d}  {p}")
    print(f"TOTAL_SORRIES={total}")
    # Transparency: report the EXCLUDED scratch-mirror count too (never hidden).
    all_files = scan(root, include_excluded=True)
    excluded = {p: n for p, n in all_files.items() if p not in per_file}
    excluded_total = sum(excluded.values())
    if excluded_total:
        print(f"EXCLUDED_PROPOSALS_SORRIES={excluded_total} "
              f"(UNVERIFIED scratch mirror, not in lake build; see proposals/INDEX.md)")
        for p, n in sorted(excluded.items(), key=lambda kv: -kv[1]):
            print(f"  [excluded] {n:5d}  {p}")
    if baseline is not None and total > baseline:
        print(f"FAIL: sorry count {total} exceeds baseline {baseline}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
