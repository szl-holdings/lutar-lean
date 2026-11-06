"""The forbidden-domain gate must really scan, and must fail when it cannot.

The gate used to call ripgrep, which is not installed on ubuntu-latest, and it
appended `|| true` to each call. The runner logged `rg: command not found` and
the gate still printed OK, so it never scanned anything. These tests run the
gate's own shell script, taken verbatim from forbidden-domain.yml, against
fixture trees: a violation fails it, a guard-context mention passes it, and a
scanner that errors fails it instead of passing silently.

Stdlib only (bash and GNU grep, as on the runner).
"""
from __future__ import annotations

import os
import re
import shutil
import stat
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = ROOT / ".github" / "workflows" / "forbidden-domain.yml"
# Assembled at run time so this file never contains the forbidden literal.
FORBIDDEN = "a11oy" + ".com"

pytestmark = pytest.mark.skipif(
    shutil.which("bash") is None or shutil.which("grep") is None,
    reason="the gate is a bash script over GNU grep; both are on every CI runner")


def _gate_script() -> str:
    """The gate step's `run: |` block, de-indented (plain line scan, no YAML lib)."""
    lines = WORKFLOW.read_text(encoding="utf-8").splitlines()
    start = next(i for i, line in enumerate(lines)
                 if line.strip() == "- name: Scan for forbidden domain references")
    run = next(i for i in range(start + 1, len(lines)) if lines[i].strip() == "run: |")
    indent = len(lines[run]) - len(lines[run].lstrip()) + 2
    body = []
    for line in lines[run + 1:]:
        if line.strip() and len(line) - len(line.lstrip()) < indent:
            break
        body.append(line[indent:])
    assert body, "forbidden-domain.yml: empty gate script"
    return "\n".join(body) + "\n"


def _run(tree: Path, env=None) -> subprocess.CompletedProcess:
    return subprocess.run(["bash", "-e", "-o", "pipefail", "-c", _gate_script()], cwd=tree,
                          capture_output=True, text=True, env=env, timeout=60)


def _tree(tmp_path: Path, files: dict) -> Path:
    for rel, body in files.items():
        path = tmp_path / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(body, encoding="utf-8")
    return tmp_path


def test_gate_does_not_depend_on_ripgrep_or_swallow_errors() -> None:
    script = _gate_script()
    assert not re.search(r"(^|[\s|$(])rg\s", script), "rg is not installed on ubuntu-latest"
    assert "|| true" not in script


def test_violation_fails_the_gate(tmp_path: Path) -> None:
    tree = _tree(tmp_path, {"docs/x.md": f"See https://{FORBIDDEN}/pricing\n"})
    result = _run(tree)
    assert result.returncode == 1, result.stdout + result.stderr
    assert "docs/x.md:1:" in result.stdout


def test_guard_context_and_hyphenated_domain_pass(tmp_path: Path) -> None:
    tree = _tree(tmp_path, {
        "a.md": f"The forbidden domain {FORBIDDEN} must never appear.\n",
        "b.md": "Product: https://a-11-oy.com\n",
        ".git/config.md": f"{FORBIDDEN}\n",
    })
    result = _run(tree)
    assert result.returncode == 0, result.stdout + result.stderr
    assert "OK: no forbidden domain references" in result.stdout


def test_scanner_error_fails_the_gate_instead_of_passing(tmp_path: Path) -> None:
    tree = _tree(tmp_path / "tree", {"a.md": "clean\n"})
    fake_bin = tmp_path / "bin"
    fake_bin.mkdir()
    fake_grep = fake_bin / "grep"
    fake_grep.write_text("#!/bin/sh\necho 'grep: simulated failure' >&2\nexit 2\n", encoding="utf-8")
    fake_grep.chmod(fake_grep.stat().st_mode | stat.S_IXUSR)
    env = dict(os.environ, PATH=f"{fake_bin}{os.pathsep}{os.environ.get('PATH', '')}")
    result = _run(tree, env=env)
    assert result.returncode == 2, result.stdout + result.stderr
    assert "could not run" in result.stdout
    assert "OK:" not in result.stdout


def test_repository_itself_passes_the_gate() -> None:
    result = _run(ROOT)
    assert result.returncode == 0, result.stdout + result.stderr
