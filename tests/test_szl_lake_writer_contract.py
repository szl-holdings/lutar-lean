"""Contract for this repo's writers of the Hugging Face dataset SZLHOLDINGS/szl-lake.

anchor-szl-lake.yml and conjecture-factory.yml both append to the same Khipu
ledger on the Hub (read, append one receipt, upload the whole file). They must:

- share one per-asset lock, hf-write/dataset/SZLHOLDINGS/szl-lake, without
  cancelling a queued run (HF plan D3), so they cannot race each other;
- stay dispatch-only (no schedule, push or pull_request trigger);
- install an exact huggingface_hub pin (HF plan D6).

Stdlib only: the Tests workflow installs nothing but pytest.
"""
from __future__ import annotations

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
WORKFLOWS = ROOT / ".github" / "workflows"
WRITERS = ("anchor-szl-lake.yml", "conjecture-factory.yml")
LOCK = "hf-write/dataset/SZLHOLDINGS/szl-lake"
HUB_PIN = "huggingface_hub==2.0.0"


def _text(name: str) -> str:
    return (WORKFLOWS / name).read_text(encoding="utf-8")


def _top_level_block(text: str, key: str) -> str:
    match = re.search(rf"^{key}:\n((?:[ \t]+.*\n|\n)*)", text, re.M)
    assert match, f"missing top-level {key}:"
    return match.group(1)


def test_every_szl_lake_writer_is_one_of_the_known_workflows() -> None:
    writers = sorted(
        path.name
        for path in WORKFLOWS.glob("*.yml")
        if "HF_LAKE_TOKEN" in path.read_text(encoding="utf-8")
    )
    assert writers == sorted(WRITERS)


def test_writers_share_the_per_asset_lock() -> None:
    for name in WRITERS:
        block = _top_level_block(_text(name), "concurrency")
        assert re.search(rf"^\s+group:\s*{re.escape(LOCK)}\s*$", block, re.M), name
        assert re.search(r"^\s+cancel-in-progress:\s*false\s*$", block, re.M), name
        assert "github." not in block, f"{name}: lock must not vary by event or ref"


def test_writers_are_dispatch_only() -> None:
    for name in WRITERS:
        on_block = _top_level_block(_text(name), "on")
        keys = re.findall(r"^  ([a-z_]+):", on_block, re.M)
        assert keys == ["workflow_dispatch"], (name, keys)


def test_writers_pin_the_hub_client() -> None:
    for name in WRITERS:
        installs = [
            line for line in _text(name).splitlines()
            if "pip install" in line and "huggingface" in line
        ]
        assert len(installs) == 1, name
        assert re.search(rf"(?<![\w-]){re.escape(HUB_PIN)}(?![\w.])", installs[0]), installs[0]
