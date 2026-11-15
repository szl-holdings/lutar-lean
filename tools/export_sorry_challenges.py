#!/usr/bin/env python3
"""Export every gated `sorry` as a machine-readable discharge challenge.

Scope mirrors count_sorries.py EXACTLY (non-proposals walk, comment-stripped
\bsorry\b token): the challenge set is the gated scoreboard — no more, no less.
The sorry-gate baseline and this exporter can never disagree on scope.

Usage: python3 tools/export_sorry_challenges.py [--root ROOT] [--out DIR]
Writes challenges.jsonl + manifest.json. Deterministic for a given tree.

The exported block_text is a COMMENT-STRIPPED EXCERPT between enclosing
declaration starts. It exists so frontier models can READ the challenge.
Verification NEVER happens against the excerpt: an attempt is verified only by
rebuilding the real file on the pinned toolchain (see docs/SORRY_DISCHARGE_LOOP.md).
"""
import argparse, hashlib, json, os, re, subprocess

_TOKEN = re.compile(r"\bsorry\b")
_DECL = re.compile(
    r"^\s*(?:private\s+|protected\s+|@\[[^\]]*\]\s*)*"
    r"(theorem|lemma|def|instance|abbrev)\s+([A-Za-z_][A-Za-z0-9_!?']*)",
    re.M)
_EXCLUDED_DIRS = ("proposals",)


def _strip_comments(text):
    """Byte-identical semantics to count_sorries._strip_comments."""
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    lines = []
    for line in text.splitlines():
        i = line.find("--")
        if i != -1:
            line = line[:i]
        lines.append(line)
    return "\n".join(lines)


def file_challenges(rel, raw):
    stripped = _strip_comments(raw)
    decls = [(m.start(), m.group(1), m.group(2)) for m in _DECL.finditer(stripped)]
    out = []
    for m in _TOKEN.finditer(stripped):
        enclosing = None
        for pos, kind, name in decls:
            if pos <= m.start():
                enclosing = (pos, kind, name)
            else:
                break
        if enclosing is None:
            continue  # file-level sorry outside a named decl: counted by the gate, not exportable
        pos, kind, name = enclosing
        later = [p for p, _, _ in decls if p > pos]
        end = min(later, default=len(stripped))
        block = stripped[pos:end].strip()
        out.append({
            "file": rel, "decl_kind": kind, "decl": name,
            "header": block.splitlines()[0][:400],
            "block_text": block,
            "file_imports": [l.strip() for l in raw.splitlines()
                             if l.strip().startswith("import ")][:40],
        })
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".")
    ap.add_argument("--out", default="huggingface/datasets/sorry-discharge-challenges-v1/data")
    a = ap.parse_args()
    rows = []
    for dirpath, _dirs, files in os.walk(a.root):
        if os.sep + ".git" in dirpath:
            continue
        rel_dir = os.path.relpath(dirpath, a.root)
        if rel_dir.split(os.sep)[0] in _EXCLUDED_DIRS:
            continue
        for name in sorted(files):
            if not name.endswith(".lean"):
                continue
            p = os.path.join(dirpath, name)
            try:
                raw = open(p, encoding="utf-8", errors="replace").read()
            except OSError:
                continue
            rows += file_challenges(os.path.relpath(p, a.root), raw)
    rows.sort(key=lambda r: (r["file"], r["decl"], r["block_text"]))
    for i, r in enumerate(rows):
        r["id"] = "sdc1-" + hashlib.sha256(
            (r["file"] + "|" + r["decl"] + "|" + str(i)).encode()).hexdigest()[:16]
    os.makedirs(a.out, exist_ok=True)
    jsonl = "\n".join(json.dumps(
        {k: r[k] for k in ("id", "file", "decl_kind", "decl", "header",
                           "block_text", "file_imports")},
        sort_keys=True) for r in rows) + "\n"
    with open(os.path.join(a.out, "challenges.jsonl"), "w", encoding="utf-8") as fh:
        fh.write(jsonl)
    sha = hashlib.sha256(jsonl.encode()).hexdigest()
    git_sha = ""
    try:
        git_sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=a.root,
                                  capture_output=True, text=True,
                                  timeout=30).stdout.strip()
    except Exception:
        pass
    toolchain = "UNKNOWN"
    tp = os.path.join(a.root, "lean-toolchain")
    if os.path.exists(tp):
        toolchain = open(tp, encoding="utf-8").read().strip()
    manifest = {
        "schema": "szl.sorry-discharge-challenges/v1",
        "total_challenges": len(rows),
        "challenges_sha256": sha,
        "kernel_head": git_sha or "NOT_A_GIT_TREE",
        "toolchain": toolchain,
        "scope": "mirrors count_sorries.py gated scope (non-proposals, comment-stripped)",
        "note": ("block_text is a comment-stripped excerpt between enclosing "
                 "declaration starts; verification always happens against the "
                 "real file on the pinned toolchain, never against the excerpt."),
    }
    with open(os.path.join(a.out, "manifest.json"), "w", encoding="utf-8") as fh:
        fh.write(json.dumps(manifest, indent=1, sort_keys=True) + "\n")
    print("TOTAL_CHALLENGES=%d SHA256=%s" % (len(rows), sha))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
