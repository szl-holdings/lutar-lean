from __future__ import annotations

from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def _tracked_paths() -> list[str]:
    completed = subprocess.run(
        ["git", "ls-files", "-z"],
        cwd=ROOT,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return [part.decode("utf-8") for part in completed.stdout.split(b"\0") if part]


def test_generated_python_bytecode_is_not_tracked() -> None:
    offenders = [
        path
        for path in _tracked_paths()
        if "/__pycache__/" in f"/{path}" or path.endswith((".pyc", ".pyo"))
    ]
    assert offenders == [], f"generated Python bytecode is tracked: {offenders}"


def test_python_bytecode_is_ignored() -> None:
    ignore = (ROOT / ".gitignore").read_text(encoding="utf-8")
    assert "__pycache__/" in ignore
    assert "*.py[cod]" in ignore


def test_contribution_terms_match_checked_in_license() -> None:
    license_text = (ROOT / "LICENSE").read_text(encoding="utf-8")
    contributing = (ROOT / "CONTRIBUTING.md").read_text(encoding="utf-8")
    assert "Apache License" in license_text
    assert "Apache License 2.0" in contributing
    assert "source-available, proprietary software" not in contributing
