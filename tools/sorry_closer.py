#!/usr/bin/env python3
"""SZL sorry-closer: bounded automation per CI-reported sorry. Closes only what Lean accepts."""
import json, os, pathlib, re, subprocess, sys, time

TARGETS = [
    ("Lutar/DPI/TH6_DPI_Soundness.lean", 110),
    ("Lutar/Innovations/round12/Identity_Ayni_Quorum.lean", 102),
    ("Lutar/KhipuConsensus.lean", 175),
    ("Lutar/KhipuConsensus.lean", 193),
    ("Lutar/PACBayes.lean", 247),
    ("Lutar/PACBayes/MadhavaBound.lean", 115),
    ("Lutar/PACBayes/MadhavaBound.lean", 137),
    ("Lutar/PRNG/K10v2_ReplayRoot.lean", 176),
    ("Lutar/PRNG/K10v2_ReplayRoot.lean", 186),
    ("Lutar/PRNG/K10v2_ReplayRoot.lean", 196),
    ("Lutar/PRNG/K10v2_ReplayRoot.lean", 284),
    ("Lutar/Round13/Lambda_Uniqueness.lean", 232),
    ("Lutar/TwoWitness.lean", 140),
    ("Lutar/Uniqueness.lean", 187),
]
TIERS = [
    ("core", "first | rfl | decide | omega | simp | simp_all | trivial"),
    ("mathlib", "first | norm_num | linarith | nlinarith | positivity | aesop | tauto"),
]
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*(?:theorem|lemma|def|instance|example|abbrev|structure|inductive|class|axiom|opaque)\b|^(?:end|namespace|section|open|variable|#)")
ART = pathlib.Path("artifacts")
ART.mkdir(exist_ok=True)


def code_mask(s):
    m = [True] * len(s)
    i, n = 0, len(s)
    while i < n:
        if s.startswith("--", i):
            j = s.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                m[k] = False
            i = j
            continue
        if s.startswith("/-", i):
            depth, j = 0, i
            while j < n:
                if s.startswith("/-", j):
                    depth += 1; j += 2; continue
                if s.startswith("-/", j):
                    depth -= 1; j += 2
                    if depth == 0:
                        break
                    continue
                j += 1
            for k in range(i, min(j, n)):
                m[k] = False
            i = j
            continue
        if s[i] == '"':
            j = i + 1
            while j < n and s[j] != '"':
                j += 2 if s[j] == "\\" else 1
            for k in range(i, min(j + 1, n)):
                m[k] = False
            i = j + 1
            continue
        i += 1
    return m


def sorry_spans(text, line):
    lines = text.split("\n")
    offs = [0]
    for l in lines:
        offs.append(offs[-1] + len(l) + 1)
    start = offs[line - 1]
    end_line = len(lines)
    for j in range(line, len(lines)):
        if DECL.match(lines[j]):
            end_line = j
            break
    end = offs[end_line]
    mask = code_mask(text)
    return [(start + mt.start(), start + mt.start() + 5) for mt in re.finditer(r"\bsorry\b", text[start:end]) if mask[start + mt.start()]]


def replace(text, spans, tac):
    out = text
    for a, b in sorted(spans, reverse=True):
        pre = out[:a].rstrip()
        ls = out.rfind("\n", 0, a) + 1
        first_on_line = out[ls:a].strip() in ("", "\u00b7", ".")
        tactic = (not pre.endswith(":=")) and (pre.endswith("by") or first_on_line or pre.endswith(";") or pre.endswith("<;>") or pre.endswith("\u00b7"))
        rep = ("(" + tac + ")") if tactic else ("(by " + tac + ")")
        out = out[:a] + rep + out[b:]
    return out


def check(path, line):
    t0 = time.time()
    try:
        p = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True, timeout=900)
        out, rc = p.stdout + p.stderr, p.returncode
    except subprocess.TimeoutExpired:
        return False, "TIMEOUT", round(time.time() - t0, 1)
    still = re.search(r"%s:%d:\d+: warning: declaration uses .sorry." % (re.escape(path), line), out)
    return (rc == 0 and not still), out[-1500:], round(time.time() - t0, 1)


def sh(*a):
    subprocess.run(list(a), check=True)


def run():
    results, closed = [], {}
    for path, line in TARGETS:
        orig = pathlib.Path(path).read_text(encoding="utf-8")
        spans = sorry_spans(orig, line)
        r = {"file": path, "line": line, "sorry_tokens": len(spans), "state": "OPEN", "tier": "", "attempts": []}
        if not spans:
            r["state"] = "NO_SORRY_TOKEN_FOUND"
            results.append(r); print(json.dumps(r), flush=True); continue
        for name, tac in TIERS:
            pathlib.Path(path).write_text(replace(orig, spans, tac), encoding="utf-8")
            ok, tail, secs = check(path, line)
            pathlib.Path(path).write_text(orig, encoding="utf-8")
            r["attempts"].append({"tier": name, "ok": ok, "seconds": secs, "log_tail": "" if ok else tail[-600:]})
            if ok:
                r["state"], r["tier"] = "CLOSED", name
                closed.setdefault(path, []).append((line, tac))
                break
        results.append(r)
        print(json.dumps({"file": path, "line": line, "state": r["state"], "tier": r["tier"]}), flush=True)
    for path, items in closed.items():
        orig = pathlib.Path(path).read_text(encoding="utf-8")
        txt = orig
        for line, tac in sorted(items, key=lambda x: -x[0]):
            txt = replace(txt, sorry_spans(txt, line), tac)
        pathlib.Path(path).write_text(txt, encoding="utf-8")
    build = {"ran": False}
    if closed:
        p = subprocess.run(["lake", "build"], capture_output=True, text=True)
        out = p.stdout + p.stderr
        uniq = sorted(set((re.sub(r"^(\./)+", "", f), l) for f, l in re.findall(r"([^\s:]+\.lean):(\d+):\d+: warning: declaration uses 'sorry'", out)))
        build = {"ran": True, "rc": p.returncode, "remaining_sorry_declarations": len(uniq), "remaining": ["%s:%s" % u for u in uniq]}
        with open(ART / "proofs.patch", "w", encoding="utf-8") as fh:
            subprocess.run(["git", "diff", "--", "Lutar/"], stdout=fh)
    head = subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    tc = pathlib.Path("lean-toolchain").read_text().strip() if pathlib.Path("lean-toolchain").exists() else ""
    summary = {"schema": "szl.sorry-closer-receipt/v1", "signing": "UNSIGNED_HONEST", "commit": head, "toolchain": tc,
               "run_id": os.environ.get("GITHUB_RUN_ID", "local"), "targets": len(TARGETS),
               "closed": sum(1 for r in results if r["state"] == "CLOSED"), "results": results, "build": build,
               "policy": "Closed only if `lake env lean` exits 0 with no sorry warning at the target line; no native_decide; combined lake build must pass before any PR."}
    json.dump(summary, open(ART / "results.json", "w", encoding="utf-8"), indent=1)
    print(json.dumps({"closed": summary["closed"], "build": build}), flush=True)


def publish():
    res = json.load(open(ART / "results.json", encoding="utf-8"))
    repo = os.environ["GITHUB_REPOSITORY"]; run_id = os.environ.get("GITHUB_RUN_ID", "local")
    run_url = "https://github.com/%s/actions/runs/%s" % (repo, run_id)
    closed = [r for r in res["results"] if r["state"] == "CLOSED"]
    pr_url = ""
    patch = ART / "proofs.patch"
    if closed and res["build"].get("rc") == 0 and patch.exists() and patch.stat().st_size > 0:
        br = "proofs/auto-close-" + run_id
        sh("git", "config", "user.name", "szl-sorry-closer")
        sh("git", "config", "user.email", "41898282+github-actions[bot]@users.noreply.github.com")
        sh("git", "checkout", "--", "Lutar/")
        sh("git", "fetch", "origin", "main")
        sh("git", "checkout", "-B", br, "origin/main")
        sh("git", "apply", str(patch))
        sh("git", "add", "Lutar/")
        sh("git", "commit", "-m", "proof: close %d sorry declaration(s) by bounded automation (sorry-closer run %s)" % (len(closed), run_id))
        sh("git", "push", "origin", br)
        body = "Closed by bounded automation; each closure compiled with no sorry warning at its line, and the combined `lake build` passed.\n\n" + \
               "\n".join("- %s:%d (%s tier)" % (r["file"], r["line"], r["tier"]) for r in closed) + \
               "\n\nRemaining after this PR: %s\n\nReceipt: %s (artifact sorry-closer-receipt)" % (res["build"].get("remaining_sorry_declarations"), run_url)
        pr = subprocess.run(["gh", "pr", "create", "--repo", repo, "--base", "main", "--head", br,
                             "--title", "proof: close %d sorry declaration(s) (CI-verified automation)" % len(closed), "--body", body],
                            capture_output=True, text=True)
        pr_url = pr.stdout.strip()
        print("PROOF_PR", pr_url, flush=True)
    lines = ["## sorry-closer run %s" % run_id, "", "Commit `%s`, toolchain `%s`." % (res["commit"][:12], res["toolchain"]), "",
             "| # | Location | Result | Tier |", "|---|---|---|---|"]
    for i, r in enumerate(res["results"]):
        lines.append("| %d | %s:%d | %s | %s |" % (i + 1, r["file"], r["line"], r["state"], r["tier"] or "-"))
    lines += ["", "Closed: **%d / %d**. Combined build: %s. Proof PR: %s" % (res["closed"], res["targets"], json.dumps(res["build"].get("rc")), pr_url or "none"),
              "", "OPEN rows need hand-written proofs; failure tails are in the receipt artifact: " + run_url]
    subprocess.run(["gh", "issue", "comment", "287", "--repo", repo, "--body", "\n".join(lines)])


if __name__ == "__main__":
    publish() if "--publish" in sys.argv else run()