"""SORRIES.md and scoreboard.py must state the baseline the sorry-gate enforces.

The gate was ratcheted 67 -> 61 in #325, but scoreboard.py kept a hard-coded
BASELINE = 65 and the committed SORRIES.md still said 67/67, so every report
disagreed with the gate. The pin now lives once, as SORRY_BASELINE in
sorry-gate.yml; the gate step and the scoreboard both read it, and the
scoreboard keeps the SORRIES.md change log (history) verbatim.

Stdlib only: the Tests workflow installs nothing but pytest.
"""
from __future__ import annotations

import importlib.util
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
GATE = ROOT / ".github" / "workflows" / "sorry-gate.yml"


def _load(name: str):
    sys.path.insert(0, str(ROOT))
    try:
        spec = importlib.util.spec_from_file_location(name, ROOT / f"{name}.py")
        module = importlib.util.module_from_spec(spec)
        assert spec.loader is not None
        spec.loader.exec_module(module)
        return module
    finally:
        sys.path.remove(str(ROOT))


SB = _load("scoreboard")


def test_gate_and_scoreboard_read_the_one_pin() -> None:
    text = GATE.read_text(encoding="utf-8")
    baseline = SB.gate_baseline(str(ROOT))
    assert baseline > 0
    assert 'python3 count_sorries.py . "$SORRY_BASELINE"' in text
    assert 'python3 scoreboard.py . "$SORRY_BASELINE"' in text
    assert "|| true" not in text, "the report step must not hide a broken scoreboard"
    assert not re.search(r"count_sorries\.py \. \d", text), "no second, literal baseline"
    assert not re.search(r"^BASELINE\s*=", (ROOT / "scoreboard.py").read_text(encoding="utf-8"), re.M)


def test_committed_scoreboard_states_the_enforced_baseline() -> None:
    md = (ROOT / "SORRIES.md").read_text(encoding="utf-8")
    pinned = re.search(r"^- Pinned baseline: \*\*(\d+)\*\*", md, re.M)
    assert pinned, "SORRIES.md has no pinned-baseline line"
    assert int(pinned.group(1)) == SB.gate_baseline(str(ROOT))
    assert SB.CHANGELOG_HEADING in md


def test_scoreboard_keeps_the_change_log_and_uses_the_gate_pin(tmp_path) -> None:
    (tmp_path / ".github" / "workflows").mkdir(parents=True)
    (tmp_path / ".github" / "workflows" / "sorry-gate.yml").write_text(
        'jobs:\n  g:\n    env:\n      SORRY_BASELINE: "3"\n', encoding="utf-8")
    (tmp_path / "Lutar").mkdir()
    (tmp_path / "Lutar" / "A.lean").write_text("a := sorry\nb := sorry\n", encoding="utf-8")
    history = "## Baseline change log\n\n- **4 -> 3**: ratchet.\n"
    (tmp_path / "SORRIES.md").write_text("# old\n\n" + history, encoding="utf-8")
    assert SB.main(["scoreboard.py", str(tmp_path)]) == 0
    md = (tmp_path / "SORRIES.md").read_text(encoding="utf-8")
    assert "comment-stripped): **2**" in md
    assert "- Pinned baseline: **3**" in md
    assert md.endswith(history) and md.count(SB.CHANGELOG_HEADING) == 1
    # An explicit baseline argument still wins (the workflow passes the pin).
    assert SB.main(["scoreboard.py", str(tmp_path), "5"]) == 0
    assert "- Pinned baseline: **5**" in (tmp_path / "SORRIES.md").read_text(encoding="utf-8")
