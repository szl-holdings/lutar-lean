#!/usr/bin/env python3
"""Compile Covenant guard and meaningful mutants in isolated temporary modules.

Uses the pinned Lean selected by Lake, with only Lean core plus the temporary
Covenant module on LEAN_PATH. It never edits the checkout or shared .lake files.
A mutant is rejected only for its expected failure, not for a tool error.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

THEOREMS = (
    "denyMonotonic", "denyMonotonic_of_hardDenied", "denyMonotonic_recon",
    "denyMonotonic_foreignWrite", "denyMonotonic_weaponize", "denyMonotonic_seq",
    "denyMonotonic_seq_recon", "denyMonotonic_seq_foreignWrite",
    "denyMonotonic_seq_weaponize", "hardDeny_ne_release",
    "release_ne_of_hardDenied", "benign_lifts_with_one_approval",
)
SOURCE = Path("Lutar/Covenant/DenyMonotonic.lean")
GUARD = Path("tools/lean/CovenantGuard.lean")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def replace_once(text: str, old: str, new: str) -> str:
    if text.count(old) != 1:
        raise ValueError("mutation anchor must match exactly once")
    return text.replace(old, new, 1)


def run(command: list[str], cwd: Path, env: dict[str, str], log: Path) -> dict:
    timed_out = False
    with log.open("w", encoding="utf-8") as stream:
        try:
            result = subprocess.run(
                command, cwd=cwd, env=env, stdin=subprocess.DEVNULL,
                stdout=stream, stderr=subprocess.STDOUT, timeout=120, check=False,
            )
            code = result.returncode
        except subprocess.TimeoutExpired:
            code = None
            timed_out = True
    return {
        "command": command, "exit_code": code, "timed_out": timed_out,
        "log": log.name, "log_sha256": sha256(log),
    }


def pinned_lean(repo: Path) -> Path:
    result = subprocess.run(
        ["lake", "env", "lean", "--print-prefix"], cwd=repo,
        capture_output=True, text=True, timeout=120, check=False,
    )
    if result.returncode:
        raise RuntimeError("cannot resolve pinned Lean: " + result.stderr[-2000:])
    lines = result.stdout.strip().splitlines()
    if not lines:
        raise RuntimeError("pinned Lean prefix was empty")
    binary = Path(lines[-1].strip()) / "bin" / ("lean.exe" if os.name == "nt" else "lean")
    if not binary.is_file():
        raise RuntimeError("pinned Lean executable is missing")
    pin = (repo / "lean-toolchain").read_text(encoding="utf-8").strip()
    expected = pin.rsplit(":", 1)[-1].removeprefix("v")
    version = subprocess.run(
        [str(binary), "--version"], capture_output=True, text=True,
        timeout=30, check=False,
    )
    if version.returncode or not re.search(r"\bversion\s+" + re.escape(expected) + r"(?=[,\s)])", version.stdout):
        raise RuntimeError("selected Lean version does not match lean-toolchain")
    return binary


def check(repo: Path, output: Path) -> dict:
    source = (repo / SOURCE).read_text(encoding="utf-8")
    guard = (repo / GUARD).read_text(encoding="utf-8")
    declared = re.findall(r"^theorem\s+(\w+)", source, re.MULTILINE)
    if set(declared) != set(THEOREMS) or len(declared) != len(THEOREMS):
        raise ValueError("Covenant theorem inventory changed; review the guard membership")
    lean = pinned_lean(repo)
    benign = (
        "theorem benign_lifts_with_one_approval :\n"
        "    approvals 1 (gate OpClass.benign) = PolicyState.release := rfl"
    )
    custom = (
        "axiom benign_lift_oracle : approvals 1 (gate OpClass.benign) = PolicyState.release\n"
        + benign.replace(":= rfl", ":= benign_lift_oracle")
    )
    transition = (
        "def approveStep : PolicyState -> PolicyState\n"
        "  | .release => .release\n  | .softDeny => .release\n"
        "  | .hardDeny => .hardDeny"
    )
    variants = [
        ("clean", source, "pass"),
        ("custom_axiom", replace_once(source, benign, custom), "axiom"),
        ("admit", replace_once(source, benign, benign.replace(":= rfl", ":= by admit")), "axiom"),
        ("hard_deny_lifts", replace_once(
            source, transition, transition.replace("| .hardDeny => .hardDeny", "| .hardDeny => .release")
        ), "module"),
        ("benign_default_release", replace_once(
            source, "  | .benign => .softDeny", "  | .benign => .release"
        ), "control"),
    ]
    results = []
    for name, text, expectation in variants:
        with tempfile.TemporaryDirectory(prefix="covenant-guard-") as directory:
            temp = Path(directory)
            module = temp / SOURCE
            module.parent.mkdir(parents=True)
            module.write_text(text, encoding="utf-8", newline="\n")
            local_guard = temp / "CovenantGuard.lean"
            local_guard.write_text(guard, encoding="utf-8", newline="\n")
            compiled = temp / "lib" / "Lutar" / "Covenant" / "DenyMonotonic.olean"
            compiled.parent.mkdir(parents=True)
            env = os.environ.copy()
            env["LEAN_PATH"] = str(temp / "lib")
            env.pop("LEAN_SRC_PATH", None)
            module_run = run(
                [str(lean), "-o", str(compiled), str(SOURCE)], temp, env,
                output / (name + ".module.log"),
            )
            guard_run = None
            module_log = (output / module_run["log"]).read_text(encoding="utf-8", errors="replace")
            if module_run["exit_code"] == 0:
                guard_run = run(
                    [str(lean), "CovenantGuard.lean"], temp, env,
                    output / (name + ".guard.log"),
                )
            guard_log = (
                (output / guard_run["log"]).read_text(encoding="utf-8", errors="replace")
                if guard_run else ""
            )
            if expectation == "pass":
                accepted = (
                    module_run["exit_code"] == 0 and guard_run is not None
                    and guard_run["exit_code"] == 0
                    and guard_log.count("COVENANT_GUARD_OK 12") == 1
                    and guard_log.count("COVENANT_CONTROLS_OK 7") == 1
                    and all(
                        guard_log.count("COVENANT_AXIOMS Lutar.Covenant." + theorem + " 0") == 1
                        for theorem in THEOREMS
                    )
                )
            elif expectation == "module":
                accepted = (
                    module_run["exit_code"] not in (0, None)
                    and "error:" in module_log
                    and "Tactic `rfl` failed" in module_log
                    and "approveStep PolicyState.hardDeny" in module_log
                )
            elif expectation == "axiom":
                accepted = (
                    module_run["exit_code"] == 0 and guard_run is not None
                    and guard_run["exit_code"] not in (0, None)
                    and "COVENANT_AXIOM_GATE Lutar.Covenant.benign_lifts_with_one_approval" in guard_log
                    and ("benign_lift_oracle" in guard_log if name == "custom_axiom" else "sorryAx" in guard_log)
                )
            else:
                accepted = (
                    module_run["exit_code"] == 0 and guard_run is not None
                    and guard_run["exit_code"] not in (0, None)
                    and "error:" in guard_log
                    and "gate OpClass.benign" in guard_log
                )
            row = {
                "case": name, "expected": expectation, "passed": accepted,
                "module": module_run, "guard": guard_run,
            }
            results.append(row)
            print(name + ": " + ("PASS" if accepted else "FAIL"), flush=True)
    return {
        "schema": "szl.lutar.covenant-guard-tests/v1",
        "source_sha256": sha256(repo / SOURCE),
        "guard_sha256": sha256(repo / GUARD),
        "public_theorem_count": len(THEOREMS),
        "lean_binary_sha256": sha256(lean),
        "lean_toolchain": (repo / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "cases": results,
        "passed": all(row["passed"] for row in results),
        "scope": "abstract Covenant policy model; no runtime correspondence or deployment claim",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-path", type=Path, default=Path("."))
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=False)
    try:
        result = check(args.repo_path.resolve(), output)
    except (OSError, RuntimeError, ValueError, subprocess.SubprocessError) as exc:
        result = {"schema": "szl.lutar.covenant-guard-tests/v1", "passed": False, "error": str(exc)}
    (output / "results.json").write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8",
    )
    print("COVENANT_MUTATION_TESTS " + ("PASS" if result["passed"] else "FAIL"))
    return 0 if result["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
