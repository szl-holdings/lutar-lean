"""Contract: this repository proposes appends to the szl-lake Khipu ledger but
never writes szl-lake main or the Hugging Face dataset SZLHOLDINGS/szl-lake.

anchor-szl-lake.yml and conjecture-factory.yml propose one receipt at a time for
data/khipu/lutar_lean_receipts.ndjson in GitHub szl-holdings/szl-lake, the
ledger's source of truth, as a pull request against szl-lake main. szl-lake's
own hf-sync.yml is the only writer of the Hub dataset SZLHOLDINGS/szl-lake (HF
plan D1: one asset, one committed writer). So the appenders must:

- hold no Hugging Face credential, and anchor_szl_lake.py must have no Hub write
  path (its Hub reads are anonymous);
- share one ledger lock that is not an hf-write/* lock (HF plan D3 reserves those
  for jobs that write the Hub), without cancelling a queued run;
- stay dispatch-only;
- check out szl-lake and let szl-lake's own publisher re-render its checked
  source index, so the proposal passes szl-lake's --check-index and hf-sync;
- create the proposal branch at, and commit against, exactly the szl-lake head
  the ledger was read from, and never commit to szl-lake main;
- keep at most one lutar-lean append pending: the same idempotency tuple already
  proposed is a no-op, any other open proposal fails the run closed.

Stdlib only: the Tests workflow installs nothing but pytest.
"""
from __future__ import annotations

import base64
import hashlib
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
    # Both appenders install exactly one hash-locked closure, and that closure
    # keeps szl-lake's own client pins (huggingface_hub==2.0.0, pyarrow>=16,<22).
    for name in APPENDERS:
        installs = [line for line in _text(name).splitlines() if "pip install" in line]
        assert len(installs) == 1, (name, installs)
        assert "--require-hashes -r requirements/ci/anchor.txt" in installs[0], installs[0]
    source = (ROOT / "requirements" / "ci" / "anchor.in").read_text(encoding="utf-8")
    assert re.search(rf"^{re.escape(HUB_PIN)}$", source, re.M), "anchor.in must pin " + HUB_PIN
    lock = (ROOT / "requirements" / "ci" / "anchor.txt").read_text(encoding="utf-8")
    assert re.search(r"^huggingface-hub==2\.0\.0 \\$", lock, re.M)
    pyarrow = re.search(r"^pyarrow==(\d+)\.", lock, re.M)
    assert pyarrow and 16 <= int(pyarrow.group(1)) < 22, "pyarrow must stay on szl-lake's >=16,<22"


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
# Ledger agreement, commit against the read head on a proposal branch only
# --------------------------------------------------------------------------- #
SNAP = "f" * 64
BRANCH = A.ANCHOR_BRANCH_PREFIX + "3-theorem-u-ffffffffffff-run7-1"


def test_surfaces_must_agree_before_append() -> None:
    A.require_surfaces_agree(b'{"a":1}\n', b'{"a":1}\n')
    A.require_surfaces_agree(b"", None)
    with pytest.raises(SystemExit):
        A.require_surfaces_agree(b'{"a":1}\n', b'{"a":1}\n{"a":2}\n')
    with pytest.raises(SystemExit):
        A.require_surfaces_agree(b'{"a":1}\n', None)


def _fake_graphql(calls):
    def fake_graphql(token, query, variables):
        calls.append(variables)
        return {"data": {"createCommitOnBranch": {"commit": {"oid": SHA_B, "url": "u"}}}}
    return fake_graphql


def test_signed_commit_is_made_against_the_head_that_was_read() -> None:
    calls = []
    additions = [{"path": A.GH_NDJSON, "contents": "eA=="}]
    oid, url = A.gh_signed_commit("t", additions, "head\n\nbody", SHA_A, BRANCH,
                                  graphql=_fake_graphql(calls))
    assert (oid, url) == (SHA_B, "u")
    (variables,) = calls
    assert variables["input"]["expectedHeadOid"] == SHA_A
    assert variables["input"]["branch"] == {
        "repositoryNameWithOwner": "szl-holdings/szl-lake", "branchName": BRANCH}
    assert variables["input"]["fileChanges"] == {"additions": additions}
    with pytest.raises(SystemExit):
        A.gh_signed_commit("t", additions, "m", "main", BRANCH, graphql=_fake_graphql([]))
    with pytest.raises(SystemExit):
        A.gh_signed_commit("t", additions, "m", SHA_A, BRANCH,
                           graphql=lambda *a: {"errors": [{"message": "moved"}]})


def test_signed_commit_never_targets_szl_lake_main_or_a_foreign_branch() -> None:
    for branch in ("main", "master", "refs/heads/main", "feature/x", "", None):
        calls = []
        with pytest.raises(SystemExit):
            A.gh_signed_commit("t", [], "m", SHA_A, branch, graphql=_fake_graphql(calls))
        assert calls == [], f"{branch!r}: no commit may be attempted"


def test_anchor_branch_name_is_a_safe_unique_proposal_ref() -> None:
    name = A.anchor_branch_name("theorem-u", 3, SNAP, "run7-1")
    assert name == BRANCH
    assert A.anchor_branch_name("Conjecture Disclosure/../x", 12, SNAP, "Local20261106T170000Z") == (
        A.ANCHOR_BRANCH_PREFIX + "12-conjecture-disclosure-x-ffffffffffff-local20261106t170000z")
    assert re.fullmatch(r"[a-z0-9/-]+", name) and ".." not in name
    for bad in ((0, SNAP, "s"), (True, SNAP, "s"), (1, "f" * 63, "s"),
                (1, "F" * 64, "s"), (1, SNAP, "  ")):
        with pytest.raises(SystemExit):
            A.anchor_branch_name("theorem-u", *bad)


def test_proposal_suffix_names_the_run_attempt() -> None:
    assert A.proposal_suffix({"GITHUB_RUN_ID": "42", "GITHUB_RUN_ATTEMPT": "2"}) == "run42-2"
    assert A.proposal_suffix({"GITHUB_RUN_ID": "42"}) == "run42-1"
    assert re.fullmatch(r"local\d{8}T\d{6}Z", A.proposal_suffix({}))


def _pr(number, ref, *, repo=A.GH_REPO, state="open", base="main", sha=SHA_B):
    return {"number": number, "state": state, "html_url": f"https://pr/{number}",
            "head": {"ref": ref, "sha": sha, "repo": {"full_name": repo}},
            "base": {"ref": base}}


def test_pending_anchor_prs_are_this_pipelines_own_open_proposals() -> None:
    ours = _pr(1, BRANCH)
    pulls = [ours,
             _pr(2, "feature/unrelated"),
             _pr(3, BRANCH, repo="someone/fork-of-szl-lake"),
             _pr(4, BRANCH, state="closed"),
             _pr(5, BRANCH, base="release")]
    assert A.pending_anchor_prs(pulls) == [ours]
    assert A.pending_anchor_prs([]) == [] and A.pending_anchor_prs(None) == []


def test_one_pending_append_rule() -> None:
    proposed = json.dumps({"kind": "theorem-u-anchor", "kernel_commit": "c" * 40,
                           "subject": {"sha256": SNAP}}) + "\n"
    ledgers = {SHA_A: proposed, SHA_B: '{"kind": "other-anchor"}\n'}

    def check(pending):
        return A.check_pending_anchors(pending, ledgers.get, "theorem-u-anchor", "c" * 40, SNAP)

    assert check([]) is None
    same = _pr(1, BRANCH, sha=SHA_A)
    assert check([same]) is same                     # already proposed -> no-op
    assert check([_pr(2, BRANCH, sha=SHA_B), same]) is same
    with pytest.raises(SystemExit):                  # a different append is pending
        check([_pr(2, BRANCH, sha=SHA_B)])


class _FakeGitHub:
    """Records REST calls; optionally fails one of them."""

    def __init__(self, fail_on=None, pr_response=None):
        self.calls = []
        self.fail_on = fail_on
        self.pr_response = pr_response

    def __call__(self, method, path, payload=None):
        self.calls.append((method, path, payload))
        if self.fail_on and (method, path.split("?")[0]) == self.fail_on:
            raise A.GitHubAPIError(method, path, 422, "boom")
        if method == "POST" and path.endswith("/pulls"):
            if self.pr_response is not None:
                return self.pr_response
            return {"number": 9, "html_url": "https://github.com/szl-holdings/szl-lake/pull/9",
                    "head": {"ref": payload["head"]}, "base": {"ref": payload["base"]}}
        return {}


def _propose(api, staged, read_back=None, commits=None):
    commits = [] if commits is None else commits

    def commit(additions, message, head, ref):
        commits.append((additions, message, head, ref))
        return SHA_B, "https://github.com/szl-holdings/szl-lake/commit/" + SHA_B

    return A.propose_ledger_append(
        api, commit, read_back or (lambda rel, ref: staged[rel]), staged,
        "anchor: headline\n\nbody", SHA_A, BRANCH, "anchor: headline", "pr body")


def test_proposal_is_a_branch_at_the_read_head_and_a_pr_against_main() -> None:
    staged = {A.GH_NDJSON: '{"r":1}\n{"r":2}\n', A.GH_CHECKED_INDEX: "{}\n"}
    api, commits = _FakeGitHub(), []
    result = _propose(api, staged, commits=commits)
    ref_call, pr_call = api.calls
    assert ref_call == ("POST", "/repos/szl-holdings/szl-lake/git/refs",
                        {"ref": "refs/heads/" + BRANCH, "sha": SHA_A})
    ((additions, message, head, ref),) = commits
    assert (head, ref) == (SHA_A, BRANCH)
    assert {a["path"] for a in additions} == set(staged)
    assert pr_call[0:2] == ("POST", "/repos/szl-holdings/szl-lake/pulls")
    assert pr_call[2]["head"] == BRANCH and pr_call[2]["base"] == "main"
    assert result["commit_oid"] == SHA_B and result["pull_request"]["number"] == 9
    assert not any(m == "DELETE" for m, _, _ in api.calls)


def test_failed_readback_deletes_the_branch_and_opens_no_pr() -> None:
    staged = {A.GH_NDJSON: '{"r":1}\n{"r":2}\n'}
    api = _FakeGitHub()
    with pytest.raises(SystemExit):
        _propose(api, staged, read_back=lambda rel, ref: "tampered\n")
    assert [m for m, _, _ in api.calls] == ["POST", "DELETE"]
    assert api.calls[-1][1] == "/repos/szl-holdings/szl-lake/git/refs/heads/" + BRANCH


def test_failed_pr_open_deletes_the_branch_and_surfaces_the_error() -> None:
    staged = {A.GH_NDJSON: '{"r":1}\n{"r":2}\n'}
    api = _FakeGitHub(fail_on=("POST", "/repos/szl-holdings/szl-lake/pulls"))
    with pytest.raises(A.GitHubAPIError):
        _propose(api, staged)
    assert api.calls[-1][0] == "DELETE"


def test_unexpected_pr_response_fails_closed() -> None:
    staged = {A.GH_NDJSON: '{"r":1}\n'}
    for response in ({"number": 9, "head": {"ref": "elsewhere"}, "base": {"ref": "main"}},
                     {"number": "9", "head": {"ref": BRANCH}, "base": {"ref": "main"}},
                     {"number": 9, "head": {"ref": BRANCH}, "base": {"ref": "release"}}):
        api = _FakeGitHub(pr_response=response)
        with pytest.raises(SystemExit):
            _propose(api, staged)
        assert api.calls[-1][0] == "DELETE"


def test_cleanup_failure_is_reported_and_the_original_error_wins(capsys) -> None:
    staged = {A.GH_NDJSON: '{"r":1}\n'}

    class _CleanupAlsoFails(_FakeGitHub):
        def __call__(self, method, path, payload=None):
            if method == "DELETE":
                self.calls.append((method, path, payload))
                raise A.GitHubAPIError(method, path, 500, "down")
            return super().__call__(method, path, payload)

    api = _CleanupAlsoFails(fail_on=("POST", "/repos/szl-holdings/szl-lake/pulls"))
    with pytest.raises(A.GitHubAPIError, match="HTTP 422"):
        _propose(api, staged)
    assert "could not delete the unfinished proposal branch" in capsys.readouterr().out


def test_list_open_pulls_reads_every_page() -> None:
    pages = {1: [{"n": i} for i in range(100)], 2: [{"n": 100}]}
    seen = []

    def api(method, path, payload=None):
        seen.append(path)
        page = int(re.search(r"page=(\d+)$", path).group(1))
        return pages[page]

    assert len(A.list_open_pulls(api)) == 101
    assert all("state=open" in p and "base=main" in p for p in seen) and len(seen) == 2
    with pytest.raises(SystemExit):
        A.list_open_pulls(lambda *a, **k: {"message": "not a list"})


def test_proposal_body_carries_the_chain_facts() -> None:
    receipt = {"kind": "theorem-u-anchor", "chain_index": 3, "prev_hash": "p" * 64,
               "receipt_id": "r" * 64, "kernel_commit": "c" * 40,
               "subject": {"sha256": SNAP}, "source_run": {"url": "https://run/1"},
               "signing": {"rekor_log_index": 123}}
    body = A.proposal_body(receipt, base_oid=SHA_A, branch=BRANCH, run_url="https://run/2",
                           baseline_line="verify-anchor-receipts floor: min_receipts 2 -> 3\n",
                           honesty_note="Theorem U REAL-conditional", verify_cmd="cosign verify ...")
    for needle in ("chain_index **3**", "p" * 64, "r" * 64, SNAP, SHA_A, BRANCH,
                   "min_receipts 2 -> 3", "exactly one", "https://run/2", "cosign verify ..."):
        assert needle in body, needle


def test_anchor_script_never_names_szl_lake_main_as_a_commit_branch() -> None:
    source = ANCHOR_PY.read_text(encoding="utf-8")
    assert not re.search(r'"branchName"\s*:\s*"main"', source)
    assert "wait_for_hub_mirror" not in source, "the Hub mirror is verified by szl-lake after merge"


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


def _git_lake(tmp_path: Path) -> Path:
    """A real git checkout of a fake szl-lake (fake publisher, one receipt)."""
    lake = _fake_lake(tmp_path)
    (lake / "data" / "khipu" / "lutar_lean_receipts.ndjson").write_text(
        json.dumps({"kind": "old-anchor", "receipt_id": "r1", "chain_index": 1}) + "\n",
        encoding="utf-8")
    run = lambda *args: subprocess.run(["git", "-C", str(lake), *args], check=True,  # noqa: E731
                                       capture_output=True, text=True)
    run("init", "-q")
    run("add", "-A")
    run("-c", "user.name=t", "-c", "user.email=t@example.invalid",
        "-c", "commit.gpgsign=false", "commit", "-q", "-m", "seed")
    return lake


SNAPSHOT_BYTES = json.dumps({
    "kind": "theorem-u", "kernel_commit": "c" * 40, "kernel_commit_short": "c" * 12,
    "branch": "main", "honesty": {"doctrine": "v11"},
    "milestone": {"status": "REAL-conditional", "title": "Theorem U"}}).encode()
SNAPSHOT_SHA = hashlib.sha256(SNAPSHOT_BYTES).hexdigest()


def _run_main(tmp_path, monkeypatch, pulls, ledgers=None):
    """Drive anchor_szl_lake.main() offline; return (exit code, REST calls, commits)."""
    lake = _git_lake(tmp_path)
    ledger = (lake / A.GH_NDJSON).read_bytes()
    snap_path = tmp_path / "theorem_u_snapshot.json"
    snap_path.write_bytes(SNAPSHOT_BYTES)
    (tmp_path / "bundle.json").write_text("{}", encoding="utf-8")
    calls, commits, staged_reads = [], [], {}

    def fake_rest(token, method, path, payload=None):
        calls.append((method, path, payload))
        if method == "GET" and "/pulls?" in path:
            return pulls
        if method == "POST" and path.endswith("/pulls"):
            return {"number": 7, "html_url": "https://github.com/szl-holdings/szl-lake/pull/7",
                    "head": {"ref": payload["head"]}, "base": {"ref": payload["base"]}}
        return {}

    def fake_commit(token, additions, message, head, branch, graphql=None):
        commits.append((additions, message, head, branch))
        for a in additions:
            staged_reads[a["path"]] = base64.b64decode(a["contents"]).decode()
        return SHA_B, "https://github.com/szl-holdings/szl-lake/commit/" + SHA_B

    def fake_raw(token, path, ref="main"):
        if ref == SHA_B:
            return staged_reads.get(path)
        return (ledgers or {}).get(ref)

    monkeypatch.setattr(A, "parse_cosign_bundle", lambda bundle, sha: {
        "mode": "cosign-keyless-oidc", "predicate_type": A.DEFAULT_PREDICATE_TYPE,
        "fulcio_identity": A.IDENTITY_PREFIX + ".github/workflows/anchor-szl-lake.yml@refs/heads/main",
        "oidc_issuer": A.GH_OIDC_ISSUER, "rekor_log_index": 5})
    monkeypatch.setattr(A, "hf_main_revision", lambda get=None: SHA_A)
    monkeypatch.setattr(A, "hf_read_at", lambda path, rev, get=None: ledger)
    monkeypatch.setattr(A, "gh_rest", fake_rest)
    monkeypatch.setattr(A, "gh_signed_commit", fake_commit)
    monkeypatch.setattr(A, "gh_get_raw", fake_raw)
    monkeypatch.setenv("SZL_LAKE_TOKEN", "test-token-not-a-secret")
    monkeypatch.setenv("GITHUB_RUN_ID", "77")
    monkeypatch.setenv("GITHUB_RUN_ATTEMPT", "1")
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(sys, "argv", [
        "anchor_szl_lake.py", "--lake-checkout", str(lake), "--snapshot", str(snap_path),
        "--bundle", str(tmp_path / "bundle.json"), "--source-run-id", "1",
        "--source-run-url", "https://github.com/szl-holdings/lutar-lean/actions/runs/1"])
    return A.main(), calls, commits


def test_main_proposes_one_pull_request_and_never_claims_the_hub(tmp_path, monkeypatch) -> None:
    code, calls, commits = _run_main(tmp_path, monkeypatch, pulls=[])
    assert code == 0
    methods = [(m, p.split("?")[0]) for m, p, _ in calls]
    assert methods == [("GET", "/repos/szl-holdings/szl-lake/pulls"),
                       ("POST", "/repos/szl-holdings/szl-lake/git/refs"),
                       ("POST", "/repos/szl-holdings/szl-lake/pulls")]
    ((additions, message, head, branch),) = commits
    assert branch.startswith(A.ANCHOR_BRANCH_PREFIX + "2-theorem-u-") and branch.endswith("-run77-1")
    lake_head = A.lake_head(tmp_path / "szl-lake")
    assert head == lake_head == calls[1][2]["sha"]
    paths = {a["path"] for a in additions}
    assert {A.GH_NDJSON, A.GH_INDEX, A.GH_CHECKED_INDEX, A.GH_BASELINE} <= paths
    ledger = [json.loads(line) for line in base64_text(additions, A.GH_NDJSON).splitlines()]
    assert [r["chain_index"] for r in ledger] == [1, 2] and ledger[1]["prev_hash"] == "r1"
    result = json.loads((tmp_path / "anchor_result.json").read_text(encoding="utf-8"))
    assert result["pull_request"]["number"] == 7 and result["github_branch"] == branch
    assert result["hub_mirror"]["status"] == "PENDING_MERGE"
    assert result["hub_mirror"]["revision"] is None
    assert "Signed-off-by:" in message


def base64_text(additions, path):
    (entry,) = [a for a in additions if a["path"] == path]
    return base64.b64decode(entry["contents"]).decode("utf-8")


def test_main_is_a_no_op_when_the_same_append_is_already_proposed(tmp_path, monkeypatch) -> None:
    proposed = json.dumps({"kind": "theorem-u-anchor", "kernel_commit": "c" * 40,
                           "subject": {"sha256": SNAPSHOT_SHA}}) + "\n"
    pending = [_pr(4, BRANCH, sha=SHA_A)]
    code, calls, commits = _run_main(tmp_path, monkeypatch, pulls=pending,
                                     ledgers={SHA_A: proposed})
    assert code == 0 and commits == []
    assert [m for m, _, _ in calls] == ["GET"]
    assert not (tmp_path / "anchor_result.json").exists()


def test_main_fails_closed_while_a_different_append_is_pending(tmp_path, monkeypatch) -> None:
    pending = [_pr(4, BRANCH, sha=SHA_A)]
    with pytest.raises(SystemExit, match="already pending review"):
        _run_main(tmp_path, monkeypatch, pulls=pending,
                  ledgers={SHA_A: '{"kind": "other-anchor"}\n'})


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
