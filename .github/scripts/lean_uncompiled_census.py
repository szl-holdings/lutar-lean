#!/usr/bin/env python3
"""Report-first census of Lean modules that `lake build` does NOT compile.

A module under SCOPE (default `Lutar/`) is "uncompiled" when, after a successful
`lake build`, no .olean exists for it. Each uncompiled module is compiled in
dependency order with `lake env lean -o`, so modules that import each other work.

Per-module status: OK | FAILED | BLOCKED_BY_IMPORT | TIMEOUT | NOT_RUN.
It also records `declaration uses 'sorry'` warnings per module.
This script never edits sources and never hides a failure: exit code is 0 unless
a --baseline file is given and a module fails that the baseline does not list.
"""
import argparse, concurrent.futures as cf, json, os, re, subprocess, sys, time

ap = argparse.ArgumentParser()
ap.add_argument("--scope", default="Lutar")
ap.add_argument("--exclude", action="append", default=["proposals"])
ap.add_argument("--workers", type=int, default=3)
ap.add_argument("--per-file-timeout", type=int, default=900)
ap.add_argument("--budget-seconds", type=int, default=4800)
ap.add_argument("--out", default="lean-uncompiled-census.json")
ap.add_argument("--baseline")
a = ap.parse_args()

def sh(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)

lean_path = sh(["lake", "env", "printenv", "LEAN_PATH"]).stdout.strip()
build_lib = ".lake/build/lib/lean"
outdir = os.path.abspath(".lake/uncompiled-census/lean")
os.makedirs(outdir, exist_ok=True)

mods = {}
for root, dirs, fs in os.walk(a.scope):
    dirs[:] = [d for d in dirs if d not in (".lake", ".git") and d not in a.exclude]
    for f in fs:
        if f.endswith(".lean"):
            p = os.path.join(root, f)
            m = p[:-5].replace(os.sep, ".")
            if not os.path.exists(os.path.join(build_lib, p[:-5] + ".olean")):
                mods[m] = p
print(f"uncompiled modules under {a.scope}/: {len(mods)}", flush=True)

imports = {}
for m, p in mods.items():
    src = open(p, encoding="utf-8", errors="replace").read()
    imports[m] = [i for i in re.findall(r"(?m)^import\s+(\S+)", src) if i in mods]

res = {}
t0 = time.time()

def compile_one(m):
    p = mods[m]
    o = os.path.join(outdir, m.replace(".", "/"))
    os.makedirs(os.path.dirname(o), exist_ok=True)
    env = dict(os.environ)
    env["LEAN_PATH"] = lean_path + ":" + outdir
    s = time.time()
    try:
        r = sh(["lake", "env", "lean", "-o", o + ".olean", "-i", o + ".ilean", p],
               env=env, timeout=a.per_file_timeout)
    except subprocess.TimeoutExpired:
        return m, {"status": "TIMEOUT", "seconds": a.per_file_timeout, "sorry_warnings": None, "errors": []}
    out = r.stdout + r.stderr
    errs = [l for l in out.split("\n") if re.search(r"\berror\b", l)][:6]
    return m, {"status": "OK" if r.returncode == 0 else "FAILED", "seconds": round(time.time() - s, 1),
               "sorry_warnings": len(re.findall(r"declaration uses 'sorry'", out)), "errors": errs}

pending = set(mods)
with cf.ThreadPoolExecutor(a.workers) as ex:
    while pending:
        if time.time() - t0 > a.budget_seconds:
            for m in pending:
                res[m] = {"status": "NOT_RUN", "reason": "global time budget exhausted"}
            break
        ready = []
        progress = False
        for m in sorted(pending):
            deps = imports[m]
            if any(d in pending for d in deps):
                continue
            bad = [d for d in deps if res[d]["status"] != "OK"]
            if bad:
                res[m] = {"status": "BLOCKED_BY_IMPORT", "blocked_by": bad}
                pending.discard(m)
                progress = True
                continue
            ready.append(m)
        if not ready:
            if pending and not progress:
                for m in list(pending):  # import cycle among uncompiled modules
                    res[m] = {"status": "FAILED", "errors": ["import cycle or unresolved dependency"]}
                    pending.discard(m)
            continue
        for m, r in ex.map(compile_one, ready):
            res[m] = r
            pending.discard(m)
            print(f"{r['status']:18} {m}", flush=True)

counts = {}
for r in res.values():
    counts[r["status"]] = counts.get(r["status"], 0) + 1
sorry_total = sum((r.get("sorry_warnings") or 0) for r in res.values())
report = {"scope": a.scope, "uncompiled_modules": len(mods), "counts": counts,
          "sorry_warnings_in_ok_or_failed_modules": sorry_total, "modules": res}
json.dump(report, open(a.out, "w"), indent=1, sort_keys=True)

md = [f"## Lean modules not built by `lake build` (scope `{a.scope}/`)", "",
      f"Uncompiled modules: **{len(mods)}**; results: `{counts}`; sorry warnings seen: **{sorry_total}**", "",
      "| module | status | sorry | first error |", "|---|---|---|---|"]
for m in sorted(res):
    r = res[m]
    md.append(f"| `{m}` | {r['status']} | {r.get('sorry_warnings','')} | {(r.get('errors') or [''])[0][:140].replace('|','/')} |")
summary = "\n".join(md)
print(summary)
if os.environ.get("GITHUB_STEP_SUMMARY"):
    open(os.environ["GITHUB_STEP_SUMMARY"], "a").write(summary + "\n")

if a.baseline and os.path.exists(a.baseline):
    expected = set(json.load(open(a.baseline))["expected_non_ok"])
    nonok = {m for m, r in res.items() if r["status"] != "OK"}
    new = sorted(nonok - expected)
    if new:
        print("NEW NON-OK MODULES vs baseline:", *new, sep="\n  ")
        sys.exit(1)
    print(f"baseline respected: {len(nonok)} non-ok, {len(expected - nonok)} improved")
else:
    print("REPORT-ONLY: no baseline file; exit 0 (nothing is gated by this run)")
