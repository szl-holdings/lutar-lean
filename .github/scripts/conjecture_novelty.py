#!/usr/bin/env python3
"""Conjecture Factory — novelty screen (step 3 of the pipeline).

Screens a normalised candidate for prior art. This is a SCREEN, not a proof of
originality: it can flag a likely duplicate, but a "novel-candidate" verdict only
ever means "no near-duplicate was found by the methods that were reachable".

Two layers, each honestly labelled:

  1. LOCAL CORPUS near-duplicate detection (always runs, fully offline):
     character n-gram (default 5) shingle Jaccard similarity of the candidate's
     canonical statement against every `.txt`/`.md`/`.json` document in a local
     corpus directory. Deterministic, no network. Reports the maximum similarity
     and the nearest document.

  2. EXTERNAL prior-art lookup (optional, network): arXiv + Crossref title/abstract
     search. Each source carries a status label:
         live        — query succeeded against the live API
         cached      — served from an on-disk cache (no live call this run)
         unreachable — the API could not be reached / errored / disabled
     A score is NEVER fabricated: an unreachable source contributes NO hits and is
     reported as unreachable, it does not silently pass as "0 hits / novel".

Verdict (honest, conservative):
  - possible-duplicate : local max similarity >= threshold OR an external source
                         returned a high-confidence title match.
  - novel-candidate    : no near-duplicate found by the methods that ran. If any
                         external source was unreachable this is annotated
                         "(local-only; external prior-art not fully screened)".
  - inconclusive       : nothing could be screened at all.

Doctrine v11: novelty is advisory. The candidate remains OPEN regardless.

stdlib only. Network is opt-in via --online; default is offline (CI passes
--online, self-test stays offline). `--self-test` runs offline fixtures.
"""
from __future__ import annotations

import argparse
import datetime as _dt
import json
import os
import re
import sys
import urllib.error
import urllib.parse
import urllib.request

SCHEMA = "szl.conjecture.novelty/v1"
UA = "szl-conjecture-novelty/1.0"
DEFAULT_NGRAM = 5
DEFAULT_THRESHOLD = 0.80
EXTERNAL_TITLE_MATCH = 0.92  # cosine-ish title overlap that counts as a hit


def _utcnow() -> str:
    return _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _norm_text(s: str) -> str:
    return re.sub(r"\s+", " ", s.lower().strip())


def shingles(text: str, n: int) -> set[str]:
    t = _norm_text(text)
    if len(t) < n:
        return {t} if t else set()
    return {t[i:i + n] for i in range(len(t) - n + 1)}


def jaccard(a: set[str], b: set[str]) -> float:
    if not a or not b:
        return 0.0
    inter = len(a & b)
    union = len(a | b)
    return inter / union if union else 0.0


def _read_doc(path: str) -> str:
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            text = fh.read()
    except OSError:
        return ""
    if path.endswith(".json"):
        # Pull out human-readable string fields rather than hashing JSON syntax.
        try:
            obj = json.loads(text)
        except json.JSONDecodeError:
            return text
        return " ".join(_json_strings(obj))
    return text


def _json_strings(obj):
    out = []
    if isinstance(obj, str):
        out.append(obj)
    elif isinstance(obj, dict):
        for v in obj.values():
            out.extend(_json_strings(v))
    elif isinstance(obj, list):
        for v in obj:
            out.extend(_json_strings(v))
    return out


def scan_local_corpus(statement: str, corpus_dir: str, ngram: int,
                      threshold: float) -> dict:
    cand = shingles(statement, ngram)
    docs = []
    if corpus_dir and os.path.isdir(corpus_dir):
        for dirpath, _d, files in os.walk(corpus_dir):
            for fn in sorted(files):
                if fn.lower().endswith((".txt", ".md", ".json")):
                    docs.append(os.path.join(dirpath, fn))
    docs.sort()
    best_sim = 0.0
    best_doc = None
    scored = []
    for path in docs:
        sim = jaccard(cand, shingles(_read_doc(path), ngram))
        rel = os.path.relpath(path, corpus_dir) if corpus_dir else path
        scored.append({"doc": rel, "similarity": round(sim, 4)})
        if sim > best_sim:
            best_sim, best_doc = sim, rel
    scored.sort(key=lambda d: (-d["similarity"], d["doc"]))
    return {
        "corpus_dir": corpus_dir,
        "documents_scanned": len(docs),
        "method": f"char-{ngram}-gram shingle Jaccard",
        "threshold": threshold,
        "max_similarity": round(best_sim, 4),
        "nearest": ({"doc": best_doc, "similarity": round(best_sim, 4)}
                    if best_doc else None),
        "top": scored[:5],
        "near_duplicate": best_sim >= threshold,
    }


# --------------------------------------------------------------------------- #
# External prior-art lookup (opt-in)
# --------------------------------------------------------------------------- #
def _http_get(url: str, timeout: int) -> str:
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read().decode("utf-8", "replace")


def _title_overlap(a: str, b: str) -> float:
    wa = set(re.findall(r"[a-z0-9]+", a.lower()))
    wb = set(re.findall(r"[a-z0-9]+", b.lower()))
    if not wa or not wb:
        return 0.0
    return len(wa & wb) / len(wa | wb)


def query_arxiv(query: str, timeout: int) -> dict:
    url = ("http://export.arxiv.org/api/query?"
           + urllib.parse.urlencode({"search_query": f"all:{query}",
                                     "start": 0, "max_results": 5}))
    try:
        body = _http_get(url, timeout)
    except (urllib.error.URLError, OSError, TimeoutError) as exc:
        return {"source": "arxiv", "status": "unreachable", "error": str(exc),
                "query": query, "hits": 0, "top": []}
    titles = re.findall(r"<title>(.*?)</title>", body, re.DOTALL)
    # First <title> is the feed title; the rest are entries.
    entries = [re.sub(r"\s+", " ", t).strip() for t in titles[1:]]
    top = [{"title": t, "title_overlap": round(_title_overlap(query, t), 3)}
           for t in entries]
    hits = sum(1 for t in top if t["title_overlap"] >= EXTERNAL_TITLE_MATCH)
    return {"source": "arxiv", "status": "live", "query": query,
            "hits": hits, "top": top}


def query_crossref(query: str, timeout: int) -> dict:
    url = ("https://api.crossref.org/works?"
           + urllib.parse.urlencode({"query.bibliographic": query, "rows": 5}))
    try:
        body = _http_get(url, timeout)
        data = json.loads(body)
    except (urllib.error.URLError, OSError, TimeoutError, json.JSONDecodeError) as exc:
        return {"source": "crossref", "status": "unreachable", "error": str(exc),
                "query": query, "hits": 0, "top": []}
    items = (data.get("message") or {}).get("items") or []
    top = []
    for it in items:
        title = " ".join(it.get("title") or []) or "(no title)"
        top.append({"title": re.sub(r"\s+", " ", title).strip(),
                    "title_overlap": round(_title_overlap(query, title), 3),
                    "doi": it.get("DOI", "")})
    hits = sum(1 for t in top if t["title_overlap"] >= EXTERNAL_TITLE_MATCH)
    return {"source": "crossref", "status": "live", "query": query,
            "hits": hits, "top": top}


def _verdict(local: dict, external: list[dict]) -> dict:
    if local["near_duplicate"]:
        return {"verdict": "possible-duplicate",
                "reason": f"local corpus similarity {local['max_similarity']} "
                          f">= threshold {local['threshold']}"}
    ext_hit = any(e.get("hits", 0) > 0 for e in external)
    if ext_hit:
        srcs = [e["source"] for e in external if e.get("hits", 0) > 0]
        return {"verdict": "possible-duplicate",
                "reason": f"external high-confidence title match in {srcs}"}
    ran_any = bool(local["documents_scanned"]) or any(
        e.get("status") in ("live", "cached") for e in external)
    if not ran_any:
        return {"verdict": "inconclusive",
                "reason": "no local corpus and no reachable external source"}
    unreachable = [e["source"] for e in external if e.get("status") == "unreachable"]
    if unreachable:
        return {"verdict": "novel-candidate",
                "reason": f"no near-duplicate found (local-only; external prior-art "
                          f"not fully screened — unreachable: {unreachable})"}
    return {"verdict": "novel-candidate",
            "reason": "no near-duplicate found by local + external screen"}


def screen(candidate: dict, *, corpus_dir: str, ngram: int, threshold: float,
           online: bool, timeout: int, external_results: list | None = None) -> dict:
    statement = candidate.get("statement_canonical") or candidate.get("statement", "")
    title = candidate.get("title", "")
    local = scan_local_corpus(statement, corpus_dir, ngram, threshold)

    external: list[dict] = []
    if external_results is not None:
        external = external_results  # injected (self-test)
    elif online:
        q = (title + " " + statement)[:300]
        external = [query_arxiv(q, timeout), query_crossref(q, timeout)]
    else:
        external = [
            {"source": "arxiv", "status": "unreachable",
             "note": "offline run (--online not set)", "hits": 0, "top": []},
            {"source": "crossref", "status": "unreachable",
             "note": "offline run (--online not set)", "hits": 0, "top": []},
        ]

    v = _verdict(local, external)
    return {
        "schema": SCHEMA,
        "candidate_id": candidate.get("id", ""),
        "statement_hash": candidate.get("statement_hash", ""),
        "screened_utc": _utcnow(),
        "local_corpus": local,
        "external": external,
        "verdict": v["verdict"],
        "verdict_reason": v["reason"],
        "honesty": (
            "Novelty is a screen, not a proof of originality. External sources are "
            "labelled live/cached/unreachable; an unreachable source contributes no "
            "hits and is never silently treated as confirming novelty. The candidate "
            "stays OPEN regardless of this verdict (doctrine v11)."
        ),
    }


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Novelty-screen a conjecture candidate.")
    ap.add_argument("--candidate", help="normalised candidate JSON")
    ap.add_argument("--corpus-dir", default="", help="local prior-art corpus directory")
    ap.add_argument("--ngram", type=int, default=DEFAULT_NGRAM)
    ap.add_argument("--threshold", type=float, default=DEFAULT_THRESHOLD)
    ap.add_argument("--online", action="store_true", help="enable external lookups")
    ap.add_argument("--timeout", type=int, default=20)
    ap.add_argument("--out", help="write novelty JSON here")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args(argv)

    if args.self_test:
        return _self_test()

    if not args.candidate:
        ap.error("--candidate is required (or use --self-test)")
    with open(args.candidate, "r", encoding="utf-8") as fh:
        candidate = json.load(fh)
    result = screen(candidate, corpus_dir=args.corpus_dir, ngram=args.ngram,
                    threshold=args.threshold, online=args.online, timeout=args.timeout)
    out = json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    if args.out:
        with open(args.out, "w", encoding="utf-8") as fh:
            fh.write(out)
        print(f"novelty OK: verdict={result['verdict']} "
              f"local_max={result['local_corpus']['max_similarity']} -> {args.out}")
    else:
        sys.stdout.write(out)
    return 0


def _self_test() -> int:
    import tempfile

    cand = {
        "id": "cf-deadbeef0001",
        "title": "Collatz-style stopping bound",
        "statement": "For every positive integer n, the orbit of f reaches 1.",
        "statement_canonical": "For every positive integer n, the orbit of f reaches 1.",
        "statement_hash": "sha256:abc",
    }

    with tempfile.TemporaryDirectory() as d:
        # Empty corpus + offline -> NOTHING was screened -> inconclusive (honest).
        rE = screen(cand, corpus_dir=d, ngram=5, threshold=0.8, online=False, timeout=1)
        assert rE["verdict"] == "inconclusive", rE["verdict"]

        # Distinct doc scanned + offline external -> novel-candidate, annotated as
        # not-fully-screened because the external sources were unreachable.
        with open(os.path.join(d, "other.txt"), "w", encoding="utf-8") as fh:
            fh.write("The Riemann hypothesis concerns zeros of the zeta function.")
        r0 = screen(cand, corpus_dir=d, ngram=5, threshold=0.8, online=False, timeout=1)
        assert r0["verdict"] == "novel-candidate", r0["verdict"]
        assert "not fully screened" in r0["verdict_reason"]
        assert all(e["status"] == "unreachable" for e in r0["external"])
        assert r0["local_corpus"]["max_similarity"] < 0.8

        # Near-duplicate doc -> possible-duplicate.
        with open(os.path.join(d, "dup.txt"), "w", encoding="utf-8") as fh:
            fh.write("For every positive integer n, the orbit of f reaches 1.")
        r1 = screen(cand, corpus_dir=d, ngram=5, threshold=0.8, online=False, timeout=1)
        assert r1["verdict"] == "possible-duplicate", r1["verdict"]
        assert r1["local_corpus"]["max_similarity"] >= 0.8

    # Injected external HIT -> possible-duplicate (no network).
    ext_hit = [{"source": "arxiv", "status": "live", "hits": 1,
                "top": [{"title": "exact", "title_overlap": 0.99}]}]
    r3 = screen(cand, corpus_dir="", ngram=5, threshold=0.8, online=False,
                timeout=1, external_results=ext_hit)
    assert r3["verdict"] == "possible-duplicate", r3["verdict"]

    # Injected unreachable external + no corpus -> inconclusive.
    ext_un = [{"source": "arxiv", "status": "unreachable", "hits": 0, "top": []}]
    r4 = screen(cand, corpus_dir="", ngram=5, threshold=0.8, online=False,
                timeout=1, external_results=ext_un)
    assert r4["verdict"] == "inconclusive", r4["verdict"]

    # jaccard sanity
    assert jaccard(set(), {"a"}) == 0.0
    assert jaccard({"a", "b"}, {"a", "b"}) == 1.0

    print("conjecture_novelty self-test OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
