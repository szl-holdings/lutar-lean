"""Contract: this repository appends to the szl-lake Khipu ledger but never writes
the Hugging Face dataset SZLHOLDINGS/szl-lake.

anchor-szl-lake.yml and conjecture-factory.yml append one receipt at a time to
data/khipu/lutar_lean_receipts.ndjson in GitHub szl-holdings/szl-lake, the
ledger's source of truth. szl-lake's own hf-sync.yml is the only writer of the
Hub dataset SZLHOLDINGS/szl-lake (HF plan D1: one asset, one committed writer).
So the appenders must:

- hold no Hugging Face credential, and anchor_szl_lake.py must have no Hub write
  path (its Hub reads are anonymous);
- share one ledger lock that is not an hf-write/* lock (HF plan D3 reserves those
  for jobs that write the Hub), without cancelling a queued run;
- stay dispatch-only;
- check out szl-lake and let szl-lake's own publisher re-render its checked
  source index, so the commit passes szl-lake's --check-index and hf-sync;
- commit against exactly the szl-lake head the ledger was read from.

Stdlib only: the Tests workflow installs nothing but pytest.
"""
from __future__ import annotations

import importlib.util
import json
import re
import subprocess
import sys
import textwrap
import urllib.request
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
WORKFLOWS = ROOT / ".github" / "workflows"
ANCHOR_PY = ROOT / ".github" / "scripts" / "anchor_szl_lake.py"
APPENDERS = ("anchor-szl-lake.yml", "conjecture-factory.yml")
LOCK = "szl-lake-ledger/lutar-lean"
HUB_PIN = "huggingface_hub==2.0.0"
SHA_A = "a" * 40
SHA_B = "b" * 40


def _load_anchor():
    spec = importlib.util.spec_from_file_location("anchor_szl_lake", ANCHOR_PY)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


A = _load_anchor()


def _text(name: str) -> str:
    return (WORKFLOWS / name).read_text(encoding="utf-8")


def _top_level_block(text: str, key: str) -> str:
    match = re.search(rf"^{key}:\n((?:[ \t]+.*\n|\n)*)", text, re.M)
    assert match, f"missing top-level {key}:"
    return match.group(1)


# --------------------------------------------------------------------------- #
# Workflow contract
# --------------------------------------------------------------------------- #
def test_appenders_hold_no_hugging_face_secret() -> None:
    for name in APPENDERS:
        assert not re.search(r"secrets\.(HF|HUGGING)", _text(name)), name


def test_no_workflow_uses_the_retired_lake_hub_token() -> None:
    # HF_LAKE_TOKEN was the appenders' szl-lake Hub write credential. Nothing in
    # this repository may write SZLHOLDINGS/szl-lake again (D1), so no workflow
    # may pick it back up.
    holders = sorted(
        path.name
        for path in WORKFLOWS.glob("*.y*ml")
        if "HF_LAKE_TOKEN" in path.read_text(encoding="utf-8")
    )
    assert holders == []


def test_appenders_share_the_ledger_lock() -> None:
    for name in APPENDERS:
        block = _top_level_block(_text(name), "concurrency")
        assert re.search(rf"^\s+group:\s*{re.escape(LOCK)}\s*$", block, re.M), name
        assert re.search(r"^\s+cancel-in-progress:\s*false\s*$", block, re.M), name
        assert "github." not in block, f"{name}: lock must not vary by event or ref"
        assert "hf-write/" not in block, f"{name}: hf-write/* locks are for Hub writers"


def test_appenders_are_dispatch_only() -> None:
    for name in APPENDERS:
        on_block = _top_level_block(_text(name), "on")
        keys = re.findall(r"^  ([a-z_]+):", on_block, re.M)
        assert keys == ["workflow_dispatch"], (name, keys)


def test_appenders_pin_the_hub_client() -> None:
    for name in APPENDERS:
        installs = [
            line for line in _text(name).splitlines()
            if "pip install" in line and "huggingface" in line
        ]
        assert len(installs) == 1, name
        assert re.search(rf"(?<![\w-]){re.escape(HUB_PIN)}(?![\w.])", installs[0]), installs[0]


def test_appenders_check_out_szl_lake_and_hand_it_to_the_anchor() -> None:
    for name in APPENDERS:
        text = _text(name)
        step = re.search(
            r"- name: Check out szl-lake[^\n]*\n((?:[ \t]+.*\n)+)", text)
        assert step, f"{name}: no szl-lake checkout step"
        body = step.group(1)
        assert "uses: actions/checkout@" in body, name
        assert re.search(r"^\s+repository:\s*szl-holdings/szl-lake\s*$", body, re.M), name
        assert re.search(r"^\s+ref:\s*main\s*$", body, re.M), name
        assert re.search(r"^\s+path:\s*szl-lake\s*$", body, re.M), name
        assert re.search(r"^\s+persist-credentials:\s*false\s*$", body, re.M), name
        assert text.index("Check out szl-lake") < text.index("anchor_szl_lake.py \\"), name
        assert "--lake-checkout szl-lake" in text, name


# --------------------------------------------------------------------------- #
# anchor_szl_lake.py: no Hub write path, anonymous Hub reads
# --------------------------------------------------------------------------- #
def test_anchor_script_has_no_hub_write_path() -> None:
    source = ANCHOR_PY.read_text(encoding="utf-8")
    for forbidden in ("HfApi", "upload_file", "upload_folder", "create_commit",
                      "CommitOperation", "HF_LAKE_TOKEN", "HF_TOKEN"):
        assert forbidden not in source, forbidden


def test_hub_reads_send_no_credentials(monkeypatch) -> None:
    seen = []

    class _Response:
        def __enter__(self):
            return self

        def __exit__(self, *exc):
            return False

        def read(self):
            return b"{}"

    def fake_urlopen(request, timeout=None):
        seen.append(request)
        return _Response()

    monkeypatch.setattr(urllib.request, "urlopen", fake_urlopen)
    A._http_get("https://huggingface.co/api/datasets/SZLHOLDINGS/szl-lake/revision/main")
    assert len(seen) == 1
    assert seen[0].get_header("Authorization") is None


def test_hub_reads_refuse_a_mutable_revision() -> None:
    with pytest.raises(SystemExit):
        A.hf_read_at(A.HF_NDJSON, "main", get=lambda url: b"")
    with pytest.raises(SystemExit):
        A.hf_main_revision(get=lambda url: b'{"sha": "main"}')
    urls = []
    A.hf_read_at(A.HF_NDJSON, SHA_A, get=lambda url: urls.append(url) or b"x")
    assert urls == [f"{A.HF_RESOLVE}/{SHA_A}/{A.HF_NDJSON}"]


def test_hub_paths_are_github_paths_without_the_data_prefix() -> None:
    assert A.GH_NDJSON == "data/" + A.HF_NDJSON
    assert A.GH_CHECKED_INDEX == "data/lake_index.json"
    snapshot = {"verified_theorems": {"theorems": [{"name": "T"}], "count": 1}}
    rel, manifest = A.build_theorem_manifest(snapshot, "f" * 64, "k", "c" * 40, "r", 1, "v")
    doc = json.loads(manifest)
    assert rel == doc["hf_path"] == f"{A.THEOREMS_DIR}/{'c' * 40}.json"
    assert doc["github_path"] == "data/" + rel


# --------------------------------------------------------------------------- #
# Ledger agreement, commit against the read head, mirror wait
# --------------------------------------------------------------------------- #
def test_surfaces_must_agree_before_append() -> None:
    A.require_surfaces_agree(b'{"a":1}\n', b'{"a":1}\n')
    A.require_surfaces_agree(b"", None)
    with pytest.raises(SystemExit):
        A.require_surfaces_agree(b'{"a":1}\n', b'{"a":1}\n{"a":2}\n')
    with pytest.raises(SystemExit):
        A.require_surfaces_agree(b'{"a":1}\n', None)


def test_signed_commit_is_made_against_the_head_that_was_read() -> None:
    calls = []

    def fake_graphql(token, query, variables):
        calls.append(variables)
        return {"data": {"createCommitOnBranch": {"commit": {"oid": SHA_B, "url": "u"}}}}

    additions = [{"path": A.GH_NDJSON, "contents": "eA=="}]
    oid, url = A.gh_signed_commit("t", additions, "head\n\nbody", SHA_A, graphql=fake_graphql)
    assert (oid, url) == (SHA_B, "u")
    (variables,) = calls
    assert variables["input"]["expectedHeadOid"] == SHA_A
    assert variables["input"]["branch"] == {
        "repositoryNameWithOwner": "szl-holdings/szl-lake", "branchName": "main"}
    assert variables["input"]["fileChanges"] == {"additions": additions}
    with pytest.raises(SystemExit):
        A.gh_signed_commit("t", additions, "m", "main", graphql=fake_graphql)
    with pytest.raises(SystemExit):
        A.gh_signed_commit("t", additions, "m", SHA_A,
                           graphql=lambda *a: {"errors": [{"message": "moved"}]})


def test_wait_for_hub_mirror_returns_the_revision_holding_the_bytes() -> None:
    expected = b'{"r":1}\n{"r":2}\n'
    served = iter([(SHA_A, b'{"r":1}\n'), (SHA_B, expected)])
    state = {}

    def fake_get(url):
        if url == A.HF_API_REVISION:
            state["rev"], state["body"] = next(served)
            return json.dumps({"sha": state["rev"]}).encode()
        assert url == f"{A.HF_RESOLVE}/{state['rev']}/{A.HF_NDJSON}"
        return state["body"]

    clock = iter(range(0, 10_000, 30))
    got = A.wait_for_hub_mirror(expected, 600, get=fake_get,
                                sleep=lambda s: None, clock=lambda: next(clock))
    assert got == SHA_B


def test_wait_for_hub_mirror_times_out_closed() -> None:
    clock = iter(range(0, 10_000, 30))
    got = A.wait_for_hub_mirror(
        b"new\n", 90,
        get=lambda url: (json.dumps({"sha": SHA_A}).encode()
                         if url == A.HF_API_REVISION else b"old\n"),
        sleep=lambda s: None, clock=lambda: next(clock))
    assert got is None


# --------------------------------------------------------------------------- #
# Staging: szl-lake's own publisher renders the checked index
# --------------------------------------------------------------------------- #
FAKE_PUBLISHER = textwrap.dedent('''
    import hashlib, json, sys
    from pathlib import Path
    ROOT = Path(__file__).resolve().parents[1]
    DATA = ROOT / "data"
    INDEX = DATA / "lake_index.json"
    def render():
        files = {p.relative_to(DATA).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                 for p in sorted(DATA.rglob("*")) if p.is_file() and p != INDEX}
        return (json.dumps({"files": files}, sort_keys=True) + "\\n").encode()
    if sys.argv[1] == "--write-index":
        INDEX.write_bytes(render())
    elif sys.argv[1] == "--check-index":
        sys.exit(0 if INDEX.read_bytes() == render() else 1)
''')


def _fake_lake(tmp_path: Path, publisher: str = FAKE_PUBLISHER) -> Path:
    lake = tmp_path / "szl-lake"
    (lake / "scripts").mkdir(parents=True)
    (lake / "scripts" / "publish_hf_dataset.py").write_text(publisher, encoding="utf-8")
    (lake / "data" / "khipu").mkdir(parents=True)
    (lake / "data" / "khipu" / "lutar_lean_receipts.ndjson").write_bytes(b'{"r":1}\n')
    (lake / "data" / "lake_index.json").write_bytes(b"stale\n")
    return lake


def test_stage_lake_changes_renders_the_index_with_the_lakes_publisher(tmp_path) -> None:
    lake = _fake_lake(tmp_path)
    manifest_rel = "data/" + A.THEOREMS_DIR + "/c.json"
    staged = A.stage_lake_changes(lake, {
        A.GH_NDJSON: '{"r":1}\n{"r":2}\n',
        A.GH_INDEX: "{}\n",
        manifest_rel: "{}\n",
    })
    assert set(staged) == {A.GH_NDJSON, A.GH_INDEX, manifest_rel, A.GH_CHECKED_INDEX}
    index = json.loads(staged[A.GH_CHECKED_INDEX])
    assert set(index["files"]) == {A.HF_NDJSON, A.THEOREMS_DIR + "/c.json"}
    assert (lake / A.GH_NDJSON).read_bytes() == b'{"r":1}\n{"r":2}\n'
    assert (lake / A.GH_CHECKED_INDEX).read_text(encoding="utf-8") == staged[A.GH_CHECKED_INDEX]


def test_stage_lake_changes_fails_closed_when_the_index_check_fails(tmp_path) -> None:
    rejecting = FAKE_PUBLISHER.replace(
        'sys.exit(0 if INDEX.read_bytes() == render() else 1)', 'sys.exit(1)')
    lake = _fake_lake(tmp_path, rejecting)
    with pytest.raises(subprocess.CalledProcessError):
        A.stage_lake_changes(lake, {A.GH_NDJSON: '{"r":1}\n{"r":2}\n'})


def test_stage_lake_changes_refuses_the_index_and_escaping_paths(tmp_path) -> None:
    lake = _fake_lake(tmp_path)
    for rel in (A.GH_CHECKED_INDEX, "../outside.json", "/abs.json"):
        with pytest.raises(SystemExit):
            A.stage_lake_changes(lake, {rel: "x"})


def test_stage_lake_changes_requires_the_publisher(tmp_path) -> None:
    lake = tmp_path / "empty"
    lake.mkdir()
    with pytest.raises(SystemExit):
        A.stage_lake_changes(lake, {A.GH_NDJSON: "x"})


def test_lake_head_is_the_checked_out_commit(tmp_path) -> None:
    repo = tmp_path / "repo"
    repo.mkdir()

    def git(*args: str) -> str:
        return subprocess.run(["git", "-C", str(repo), *args], check=True,
                              capture_output=True, text=True).stdout.strip()

    git("init", "-q")
    (repo / "f").write_text("x", encoding="utf-8")
    git("add", "f")
    git("-c", "user.name=t", "-c", "user.email=t@example.invalid",
        "-c", "commit.gpgsign=false", "commit", "-q", "-m", "t")
    assert A.lake_head(repo) == git("rev-parse", "HEAD")


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-q"]))
