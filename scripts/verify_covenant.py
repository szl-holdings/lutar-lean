#!/usr/bin/env python3
"""Produce a revision-bound receipt for the bounded Covenant proof verification.

This verifies fresh source re-elaboration and mutation rejection only. It does
not claim a full-library build, runtime refinement, deployment or authorization.
The output directory must be new. Historical logs are never accepted as inputs.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

INPUTS = (
    "lean-toolchain", "lake-manifest.json", "lakefile.lean", "Lutar.lean",
    "Lutar/Covenant/DenyMonotonic.lean", "tools/lean/CovenantGuard.lean",
    ".github/scripts/check_covenant_guard.py", "scripts/verify_covenant.py",
    ".github/workflows/lake-build.yml",
)
SCHEMA = "szl.lutar.covenant-verification/v1"


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(repo: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", "-C", str(repo), *args], capture_output=True, text=True,
        timeout=30, check=False,
    )
    if result.returncode:
        raise RuntimeError("git " + args[0] + " failed: " + result.stderr[-1000:])
    return result.stdout.strip()


def snapshot(repo: Path) -> dict:
    files = {}
    for relative in INPUTS:
        path = repo / relative
        committed = git(repo, "rev-parse", "HEAD:" + relative)
        working = git(repo, "hash-object", "--path=" + relative, relative)
        files[relative] = {
            "sha256": digest(path), "head_blob": committed,
            "working_blob": working, "matches_head": committed == working,
        }
    return {
        "commit": git(repo, "rev-parse", "HEAD"),
        "tree": git(repo, "rev-parse", "HEAD^{tree}"),
        "tracked_status": git(repo, "status", "--porcelain=v1", "--untracked-files=no"),
        "inputs": files,
    }


def clean(state: dict) -> bool:
    return not state["tracked_status"] and all(
        row["matches_head"] for row in state["inputs"].values()
    )


def run_command(command: list[str], repo: Path, log: Path) -> dict:
    record = {"command": command, "started_at": now(), "exit_code": None}
    with log.open("w", encoding="utf-8") as stream:
        try:
            result = subprocess.run(
                command, cwd=repo, stdin=subprocess.DEVNULL, stdout=stream,
                stderr=subprocess.STDOUT, check=False, timeout=900,
            )
            record["exit_code"] = result.returncode
        except (OSError, subprocess.TimeoutExpired) as exc:
            record["error"] = type(exc).__name__ + ": " + str(exc)
    record.update({
        "finished_at": now(), "log": log.name, "log_sha256": digest(log),
    })
    return record


def assess(before: dict, after: dict | None, commands: list[dict], expected: int) -> tuple[str, str]:
    if not clean(before):
        return "FAIL", "tracked source or required input differs from HEAD"
    if after is None:
        return "UNKNOWN", "final source snapshot unavailable"
    if before != after or not clean(after):
        return "FAIL", "source changed during verification"
    if any(row["exit_code"] is None for row in commands):
        return "UNKNOWN", "a command has no observed native exit code"
    if any(row["exit_code"] != 0 for row in commands):
        return "FAIL", "a verification command failed"
    if len(commands) != expected:
        return "UNKNOWN", "verification sequence incomplete"
    return "PASS", "all commands succeeded against unchanged committed inputs"


def verify(repo: Path, output: Path) -> dict:
    receipt = {
        "schema": SCHEMA, "started_at": now(), "status": "UNKNOWN",
        "scope": "fresh Covenant source re-elaboration and four negative mutation controls",
        "limitations": [
            "Not a full-library or fresh-dependency build receipt.",
            "Does not establish runtime refinement, deployment, authorization or model quality.",
            "A digest provides content integrity, not an independent signature.",
        ],
        "source_before": None, "source_after": None, "commands": [],
        "verified_commit": None,
    }
    commands = [
        ["lake", "--version"],
        ["lake", "env", "lean", "--version"],
        [sys.executable, ".github/scripts/check_covenant_guard.py",
         "--repo-path", str(repo), "--output-dir", str(output / "mutations")],
    ]
    try:
        before = snapshot(repo)
        receipt["source_before"] = before
        if clean(before):
            for index, command in enumerate(commands, start=1):
                record = run_command(command, repo, output / (str(index) + ".log"))
                receipt["commands"].append(record)
                if record["exit_code"] != 0:
                    break
        after = snapshot(repo)
        receipt["source_after"] = after
        status, reason = assess(before, after, receipt["commands"], len(commands))
        if status == "PASS":
            results_path = output / "mutations" / "results.json"
            results = json.loads(results_path.read_text(encoding="utf-8"))
            if (
                results.get("passed") is not True
                or results.get("public_theorem_count") != 12
                or len(results.get("cases", [])) != 5
                or any(row.get("passed") is not True for row in results["cases"])
            ):
                status, reason = "FAIL", "mutation evidence is incomplete or failed"
            else:
                receipt["mutation_results_sha256"] = digest(results_path)
        receipt["status"], receipt["reason"] = status, reason
        if status == "PASS":
            receipt["verified_commit"] = before["commit"]
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as exc:
        receipt["status"] = "UNKNOWN"
        receipt["reason"] = type(exc).__name__ + ": " + str(exc)
    receipt["finished_at"] = now()
    payload = json.dumps(receipt, sort_keys=True, separators=(",", ":")).encode("utf-8")
    receipt["receipt_digest"] = hashlib.sha256(payload).hexdigest()
    return receipt


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-path", type=Path, default=Path("."))
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=False)
    receipt = verify(args.repo_path.resolve(), output)
    temporary = output / "receipt.json.tmp"
    temporary.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    os.replace(temporary, output / "receipt.json")
    print("COVENANT_VERIFICATION " + receipt["status"] + ": " + receipt["reason"])
    return 0 if receipt["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
