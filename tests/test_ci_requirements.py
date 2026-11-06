"""CI installs Python packages only from hash-locked closures.

Every ``pip install`` in .github/workflows/ installs ``requirements/ci/<name>.txt``
with ``--require-hashes``. Each lock is compiled from its ``.in`` source with
``uv pip compile --generate-hashes`` (the command is in each ``.in`` header), and
Dependabot watches ``/requirements/ci`` so the hashes stay current. These checks
keep the sources, the locks and the workflows in step, so no workflow can
quietly go back to installing unpinned, unhashed packages (OpenSSF Scorecard
Pinned-Dependencies).

Stdlib only: the Tests workflow installs nothing but pytest.
"""
from __future__ import annotations

import re
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
CI = ROOT / "requirements" / "ci"
WORKFLOWS = ROOT / ".github" / "workflows"
PIN = re.compile(r"^([A-Za-z0-9][A-Za-z0-9._-]*)==([^\s;\\]+)")
PIP_INSTALL = re.compile(r"(?:python3?\s+-m\s+pip|pip3?|uv\s+pip)\s+install\b(?P<args>[^\n]*)")
LOCKS = sorted(p.stem for p in CI.glob("*.in"))


def norm(name: str) -> str:
    return re.sub(r"[-_.]+", "-", name).lower()


def pins(path: Path) -> dict[str, str]:
    out = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        match = PIN.match(line.strip())
        if match:
            out[norm(match.group(1))] = match.group(2)
    return out


def requirement_names(path: Path) -> list[str]:
    names = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if line and not line.startswith("#"):
            names.append(norm(re.split(r"[<>=!~;\s\[]", line, maxsplit=1)[0]))
    return names


def test_every_source_has_a_compiled_lock_and_vice_versa() -> None:
    assert LOCKS, "requirements/ci/*.in must exist"
    assert sorted(p.stem for p in CI.glob("*.txt")) == LOCKS


@pytest.mark.parametrize("lock", LOCKS)
def test_compiled_lock_is_hashed_and_matches_its_source(lock: str) -> None:
    text = (CI / f"{lock}.txt").read_text(encoding="utf-8")
    locked = pins(CI / f"{lock}.txt")
    assert locked, f"{lock}.txt pins nothing"
    for name in requirement_names(CI / f"{lock}.in"):
        assert name in locked, f"{name} from {lock}.in is missing from {lock}.txt; recompile it"
    for name, version in pins(CI / f"{lock}.in").items():
        assert locked[name] == version, f"{lock}.txt is stale for {name}; recompile it"
    for line in text.splitlines():
        if PIN.match(line.strip()):
            assert line.rstrip().endswith("\\"), f"unhashed requirement in {lock}.txt: {line}"
    assert text.count("--hash=sha256:") >= len(locked)
    assert "uv pip compile --generate-hashes" in (CI / f"{lock}.in").read_text(encoding="utf-8")


def test_workflows_install_only_hash_locked_closures() -> None:
    used = set()
    for wf in sorted(WORKFLOWS.glob("*.y*ml")):
        for match in PIP_INSTALL.finditer(wf.read_text(encoding="utf-8")):
            args = match.group("args")
            lock = re.search(r"--require-hashes\s+-r\s+requirements/ci/([\w-]+)\.txt\s*$", args)
            assert lock, f"{wf.name}: unhashed install: {match.group(0).strip()}"
            assert lock.group(1) in LOCKS, f"{wf.name}: unknown lock {lock.group(1)}"
            used.add(lock.group(1))
    assert used == set(LOCKS), f"locks no workflow installs: {set(LOCKS) - used}"


def test_dependabot_watches_the_ci_locks() -> None:
    text = (ROOT / ".github" / "dependabot.yml").read_text(encoding="utf-8")
    blocks = re.split(r"\n\s*- package-ecosystem:", text)
    pip = [b for b in blocks if b.lstrip().startswith('"pip"') or b.lstrip().startswith("pip")]
    assert pip, "dependabot.yml has no pip ecosystem entry"
    assert any(re.search(r'directory:\s*"?/requirements/ci"?', b) for b in pip)
