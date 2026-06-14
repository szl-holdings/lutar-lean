#!/usr/bin/env python3
"""Count `sorry` tokens in .lean files and enforce a no-increase baseline.

Usage: python3 count_sorries.py [ROOT] [BASELINE]
Prints per-file counts and TOTAL_SORRIES=N. Exit 1 if N > BASELINE.
Comments (-- line, /- block -/) are stripped before counting.
"""
import os, re, sys

_TOKEN = re.compile(r"\bsorry\b")


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


def scan(root="."):
    per_file = {}
    for dirpath, _dirs, files in os.walk(root):
        if os.sep + ".git" in dirpath:
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
    if baseline is not None and total > baseline:
        print(f"FAIL: sorry count {total} exceeds baseline {baseline}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
