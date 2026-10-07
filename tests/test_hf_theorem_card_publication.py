"""Offline synthetic-provider tests, not protected admission or live Hub proof."""
from dataclasses import replace
import json
import base64
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
from types import ModuleType
import unittest
from unittest.mock import MagicMock, patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import publish_hf_theorem_card as publication

PARENT = "a" * 40
COMMIT = "b" * 40
SOURCE = "c" * 40
IMPORT = b"---\nlicense: apache-2.0\n---\nSYNTHETIC fixture, not Lean results.\n"
CARD = IMPORT.replace(b"\n---\n", b"\n" + publication.SELECTOR + b"---\n", 1)
DATA = b'{"declarations":[{"name":"synthetic fixture"}]}\n'


class FakeAPI:
    repo_id = publication.TARGET
    repo_type = publication.REPO_TYPE

    def __init__(self, state):
        self.state = state
        self.current = PARENT
        self.before = {"README.md": IMPORT, ".gitattributes": b"* text=auto\n",
                       "SZL_ESTATE_MANAGED.json": b'{"synthetic":true}\n',
                       "data/lean_theorem_tree.json": DATA}
        self.after = None
        self.calls = []
        self.write_attempts = 0
        self.writes = 0
        self.auth_error = None
        self.commit_error = None
        self.error_after_write = False
        self.post_error = False
        self.post_change = None
        self.advance_on_auth = False
        self.advance_after_commit = False
        self.native_commit = COMMIT
        self.manifest_extra = []
        self.iterator_error = False
        self.spoof_read = False

    def head(self):
        self.calls.append(("head", self.current))
        return self.current

    def files(self, revision):
        self.calls.append(("files", revision))
        if revision != PARENT and self.post_error:
            raise OSError("synthetic readback failure, no real network")
        content = self.before if revision == PARENT else self.after
        for path, raw in content.items():
            yield publication.FileSpec(path, len(raw), publication.blob_oid(raw))
        yield from self.manifest_extra
        if self.iterator_error:
            raise OSError("synthetic later-page failure")

    def read(self, path, revision, limit):
        self.calls.append(("read", path, revision, limit))
        content = self.before if revision == PARENT else self.after
        return b"spoof" if self.spoof_read else content[path]

    def authorize_write(self):
        self.calls.append(("auth",))
        if self.auth_error:
            raise self.auth_error
        if self.advance_on_auth:
            self.current = "d" * 40

    def commit_readme(self, content, expected_parent):
        self.calls.append(("commit", expected_parent))
        self.write_attempts += 1
        journal = json.loads((self.state / "lean-theorem-tree.publication.json").read_bytes())
        if journal["status"] != "PENDING" or journal["expected_parent"] != expected_parent:
            raise AssertionError("write was not fenced durably before the provider call")
        if journal["allowed_paths"] != ["README.md"]:
            raise AssertionError("unexpected write set")
        if self.commit_error and not self.error_after_write:
            raise self.commit_error
        if self.current != expected_parent:
            raise RuntimeError("synthetic CAS conflict")
        self.after = dict(self.before, **{"README.md": content})
        if self.post_change:
            self.post_change(self.after)
        self.writes += 1
        self.current = "d" * 40 if self.advance_after_commit else COMMIT
        if self.commit_error:
            raise self.commit_error
        return self.native_commit


class PublicationTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="szl-lean-card-test-")
        self.addCleanup(self.directory.cleanup)
        self.state = Path(self.directory.name) / "private-owner-state"
        self.api = FakeAPI(self.state)
        # Synthetic hashes are explicitly scoped to tests. Production pins remain
        # unchanged; this harness does not certify the real dataset's contents.
        self.pins = patch.multiple(publication, CARD_SHA256=publication.sha256(CARD),
                                   IMPORT_SHA256=publication.sha256(IMPORT),
                                   DATA_SHA256=publication.sha256(DATA))
        self.pins.start()
        self.addCleanup(self.pins.stop)
        self.native_preflight = patch.object(publication, "verify_native_source", return_value=None)
        self.native_mock = self.native_preflight.start()
        self.addCleanup(self.native_preflight.stop)
        self.source = publication.SourceCard(SOURCE, publication.blob_oid(CARD), CARD)

    def run_publish(self, **kwargs):
        return publication.publish(self.api, self.source, PARENT, self.state, **kwargs)

    def journal(self):
        return json.loads((self.state / "lean-theorem-tree.publication.json").read_bytes())

    def assert_no_mutation(self):
        self.assertEqual(self.api.write_attempts, 0)
        self.assertFalse((self.state / "lean-theorem-tree.publication.json").exists())
        self.assertFalse((self.state / "lean-theorem-tree.writer.lock").exists())

    def assert_unknown_fence(self):
        record = self.journal()
        self.assertEqual(record["status"], "UNKNOWN")
        self.assertEqual(record["provider_writes"], "UNKNOWN")
        self.assertTrue(record["unknown_write"])
        self.assertTrue((self.state / "lean-theorem-tree.writer.lock").exists())
        count, calls = self.api.write_attempts, list(self.api.calls)
        with self.assertRaises(publication.PublicationError):
            self.run_publish(apply=True, authorized=True)
        self.assertEqual(self.api.write_attempts, count)
        self.assertEqual(self.api.calls, calls)

    def test_default_check_only_has_no_state_or_auth_write(self):
        result = self.run_publish()
        self.assertEqual(result["status"], "CHECK_ONLY")
        self.assertEqual(set(result["before"]), publication.REQUIRED)
        self.assertFalse(self.state.exists())
        self.assertNotIn(("auth",), self.api.calls)
        self.assert_no_mutation()

    def test_publish_exact_readme_only_with_native_readback(self):
        result = self.run_publish(apply=True, authorized=True)
        self.assertEqual(result["status"], "VERIFIED")
        self.assertEqual(result["provider_commit"], COMMIT)
        self.assertEqual(result["provider_writes"], 1)
        self.assertFalse(result["viewer_verified"])
        self.assertFalse(result["protected_admission_verified_by_this_program"])
        self.assertEqual(self.api.after["README.md"], CARD)
        for path in publication.REQUIRED - {"README.md"}:
            self.assertEqual(result["after"][path], result["before"][path])
        self.assertEqual(self.journal(), result)
        self.assertFalse((self.state / "lean-theorem-tree.writer.lock").exists())

    def test_matching_source_is_noop_and_no_authority_probe(self):
        self.api.before["README.md"] = CARD
        self.assertEqual(self.run_publish(apply=True, authorized=True)["status"], "NO_CHANGE")
        self.assertNotIn(("auth",), self.api.calls)
        self.assert_no_mutation()

    def test_source_sha_blob_owner_path_and_bytes_must_bind(self):
        variants = [replace(self.source, revision="main"), replace(self.source, blob="f" * 40),
                    replace(self.source, repository="someone/else"),
                    replace(self.source, path="README.md"),
                    replace(self.source, content=CARD + b"unqualified claim")]
        for variant in variants:
            with self.subTest(variant=variant):
                with self.assertRaises(publication.PublicationError):
                    publication.publish(self.api, variant, PARENT, self.state)
        self.assertEqual(self.api.calls, [])

    def test_fixed_dataset_target_and_type(self):
        for repo, kind in [("SZLHOLDINGS/lean-proofs-v1", "dataset"),
                           (publication.TARGET, "model"), (publication.TARGET, "space")]:
            with self.subTest(repo=repo, kind=kind):
                self.api.repo_id, self.api.repo_type = repo, kind
                with self.assertRaises(publication.PublicationError):
                    self.run_publish(apply=True, authorized=True)
        self.assertEqual(self.api.calls, [])

    def test_publish_requires_explicit_owner_authority(self):
        with self.assertRaises(publication.PublicationError):
            self.run_publish(apply=True)
        self.assertEqual(self.api.calls, [])
        self.assert_no_mutation()

    def test_relative_state_path_cannot_skip_absolute_ancestor_checks(self):
        with self.assertRaisesRegex(publication.PublicationError, "absolute lexical"):
            publication.publish(self.api, self.source, PARENT, Path("relative-state"),
                                apply=True, authorized=True)
        self.assertEqual(self.api.calls, [])

    def test_head_mismatch_before_any_manifest_or_write(self):
        self.api.current = "d" * 40
        with self.assertRaises(publication.PublicationError):
            self.run_publish(apply=True, authorized=True)
        self.assertEqual(len(self.api.calls), 1)
        self.assert_no_mutation()

    def test_auth_failure_is_terminal_without_pending_or_write(self):
        self.api.auth_error = PermissionError("synthetic 401 secret must not be journalled")
        with self.assertRaises(PermissionError):
            self.run_publish(apply=True, authorized=True)
        self.assert_no_mutation()

    def test_head_advance_after_auth_refuses_cas_attempt(self):
        self.api.advance_on_auth = True
        with self.assertRaises(publication.PublicationError):
            self.run_publish(apply=True, authorized=True)
        self.assert_no_mutation()

    def test_source_main_advance_at_write_boundary_is_pre_mutation_blocker(self):
        self.native_mock.side_effect = publication.PublicationError("native source main moved")
        with self.assertRaisesRegex(publication.PublicationError, "main moved"):
            self.run_publish(apply=True, authorized=True)
        self.native_mock.assert_called_once_with(self.source)
        self.assert_no_mutation()

    def test_unrelated_card_edit_is_not_overwritten(self):
        self.api.before["README.md"] = IMPORT + b"concurrent prose"
        with self.assertRaises(publication.PublicationError):
            self.run_publish(apply=True, authorized=True)
        self.assert_no_mutation()

    def test_missing_preserved_file_fails_closed(self):
        del self.api.before["SZL_ESTATE_MANAGED.json"]
        with self.assertRaises(publication.PublicationError):
            self.run_publish(apply=True, authorized=True)
        self.assert_no_mutation()

    def test_changed_data_is_not_qualified_by_same_row_count(self):
        self.api.before["data/lean_theorem_tree.json"] = DATA + b" "
        with self.assertRaises(publication.PublicationError):
            self.run_publish(apply=True, authorized=True)
        self.assert_no_mutation()

    def test_later_page_failure_never_becomes_complete_map(self):
        self.api.iterator_error = True
        with self.assertRaises(OSError):
            self.run_publish(apply=True, authorized=True)
        self.assert_no_mutation()

    def test_native_blob_and_exact_length_must_match_bytes(self):
        self.api.spoof_read = True
        with self.assertRaises(publication.PublicationError):
            self.run_publish(apply=True, authorized=True)
        self.assert_no_mutation()

    def test_duplicate_unsafe_or_oversize_entries_fail_before_read(self):
        variants = [publication.FileSpec("README.md", 1, "e" * 40),
                    publication.FileSpec("../outside", 1, "e" * 40),
                    publication.FileSpec("/outside", 1, "e" * 40),
                    publication.FileSpec("a\\b", 1, "e" * 40),
                    publication.FileSpec("a//b", 1, "e" * 40),
                    publication.FileSpec("huge", publication.MAX_FILE_BYTES + 1, "e" * 40),
                    publication.FileSpec("bad-size", True, "e" * 40),
                    publication.FileSpec("bad-blob", 1, "main")]
        for entry in variants:
            with self.subTest(entry=entry):
                self.api.calls = []
                self.api.manifest_extra = [entry]
                with self.assertRaises(publication.PublicationError):
                    self.run_publish()
                self.assertFalse(any(call[0] == "read" for call in self.api.calls))

    def test_tree_count_and_total_bytes_are_bounded(self):
        for entries in [[publication.FileSpec(f"extra/{n}", 1, "e" * 40)
                         for n in range(publication.MAX_FILES)],
                        [publication.FileSpec(f"extra/{n}", publication.MAX_FILE_BYTES, "e" * 40)
                         for n in range(9)]]:
            self.api.manifest_extra = entries
            with self.assertRaises(publication.PublicationError):
                self.run_publish()
        self.assert_no_mutation()

    def test_existing_pending_unknown_verified_or_corrupt_journal_never_replays(self):
        self.state.mkdir()
        journal = self.state / "lean-theorem-tree.publication.json"
        for raw in [b'{"status":"PENDING"}', b'{"status":"UNKNOWN"}',
                    b'{"status":"VERIFIED"}', b"incomplete crash bytes"]:
            journal.write_bytes(raw)
            with self.assertRaises(publication.PublicationError):
                self.run_publish(apply=True, authorized=True)
            self.assertEqual(journal.read_bytes(), raw)
        self.assertEqual(self.api.calls, [])

    def test_existing_other_writer_lock_is_not_removed(self):
        self.state.mkdir()
        lock = self.state / "lean-theorem-tree.writer.lock"
        lock.write_bytes(b"another owner's retained fence")
        with self.assertRaises(publication.PublicationError):
            self.run_publish(apply=True, authorized=True)
        self.assertEqual(lock.read_bytes(), b"another owner's retained fence")
        self.assertEqual(self.api.calls, [])

    def test_commit_exception_before_or_after_effect_is_unknown_and_once_only(self):
        for after_write in [False, True]:
            with self.subTest(after_write=after_write):
                self.state = Path(self.directory.name) / str(after_write)
                self.api = FakeAPI(self.state)
                self.api.commit_error = TimeoutError("SYNTHETIC_SECRET_DO_NOT_RECORD")
                self.api.error_after_write = after_write
                with self.assertRaises(TimeoutError):
                    self.run_publish(apply=True, authorized=True)
                self.assert_unknown_fence()
                self.assertNotIn("SYNTHETIC_SECRET_DO_NOT_RECORD", json.dumps(self.journal()))

    def test_readback_failure_holds_known_native_commit_without_replay(self):
        self.api.post_error = True
        with self.assertRaises(OSError):
            self.run_publish(apply=True, authorized=True)
        self.assert_unknown_fence()
        self.assertEqual(self.journal()["provider_commit"], COMMIT)

    def test_readback_missing_extra_changed_preserved_or_wrong_card_is_unknown(self):
        changes = [lambda tree: tree.pop(".gitattributes"),
                   lambda tree: tree.update({"extra": b"unintended write"}),
                   lambda tree: tree.update({"SZL_ESTATE_MANAGED.json": b"changed"}),
                   lambda tree: tree.update({"README.md": IMPORT})]
        for number, change in enumerate(changes):
            self.state = Path(self.directory.name) / f"post-{number}"
            self.api = FakeAPI(self.state)
            self.api.post_change = change
            with self.assertRaises(publication.PublicationError):
                self.run_publish(apply=True, authorized=True)
            self.assert_unknown_fence()

    def test_current_main_advance_after_commit_is_not_operational_success(self):
        self.api.advance_after_commit = True
        with self.assertRaises(publication.PublicationError):
            self.run_publish(apply=True, authorized=True)
        self.assert_unknown_fence()

    def test_invalid_native_commit_retains_unknown_fence(self):
        self.api.native_commit = "not-a-native-sha"
        with self.assertRaises(publication.PublicationError):
            self.run_publish(apply=True, authorized=True)
        self.assert_unknown_fence()

    def test_journal_update_failure_preserves_original_pending_and_lock(self):
        with patch.object(publication, "durable_update", side_effect=OSError("disk failure")):
            with self.assertRaises(OSError):
                self.run_publish(apply=True, authorized=True)
        self.assertEqual(self.journal()["status"], "PENDING")
        self.assertTrue((self.state / "lean-theorem-tree.writer.lock").exists())
        with self.assertRaises(publication.PublicationError):
            self.run_publish(apply=True, authorized=True)
        self.assertEqual(self.api.write_attempts, 1)

    def test_durable_update_refuses_another_attempts_journal(self):
        self.state.mkdir()
        journal = self.state / "lean-theorem-tree.publication.json"
        original = b'{"attempt_id":"owner-a","status":"UNKNOWN"}'
        journal.write_bytes(original)
        with self.assertRaises(publication.PublicationError):
            publication.durable_update(journal, {"attempt_id": "owner-b"})
        self.assertEqual(journal.read_bytes(), original)

    def test_exclusive_journal_collision_does_not_overwrite_prior_evidence(self):
        real_create = publication.durable_create
        other = b'{"attempt_id":"other-owner","status":"UNKNOWN"}'

        def collide(path, raw):
            if path.name.endswith("publication.json"):
                path.write_bytes(other)
            return real_create(path, raw)

        with patch.object(publication, "durable_create", side_effect=collide):
            with self.assertRaises(FileExistsError):
                self.run_publish(apply=True, authorized=True)
        self.assertEqual((self.state / "lean-theorem-tree.publication.json").read_bytes(), other)
        self.assertEqual(self.api.write_attempts, 0)
        self.assertTrue((self.state / "lean-theorem-tree.writer.lock").exists())

    def test_git_binding_reads_blob_not_working_tree_and_fails_safely(self):
        def fake_git(command, **kwargs):
            self.assertEqual(command[:5],
                             ["git", "-c", "core.fsmonitor=false", "-C", "synthetic-root"])
            arguments = command[5:]
            outputs = {("--version",): b"git version 2.36.0\n",
                       ("config", "--get", "remote.origin.url"):
                       b"https://github.com/szl-holdings/lutar-lean.git\n",
                       ("symbolic-ref", "--short", "HEAD"): b"main\n",
                       ("rev-parse", "HEAD"): SOURCE.encode() + b"\n",
                       ("status", "--porcelain=v1", "--untracked-files=all"): b"",
                       ("cat-file", "-t", SOURCE): b"commit\n",
                       ("rev-parse", f"{SOURCE}:{publication.SOURCE_PATH}"):
                       self.source.blob.encode() + b"\n",
                       ("cat-file", "-s", f"{SOURCE}:{publication.SOURCE_PATH}"):
                       str(len(CARD)).encode() + b"\n",
                       ("cat-file", "blob", f"{SOURCE}:{publication.SOURCE_PATH}"): CARD}
            return subprocess.CompletedProcess(command, 0, outputs[tuple(arguments)], b"")

        with patch.object(publication.subprocess, "run", side_effect=fake_git):
            result = publication.load_git_source(Path("synthetic-root"), SOURCE, self.source.blob)
        self.assertEqual(result, self.source)
        with patch.object(publication.subprocess, "run", side_effect=PermissionError("secret")):
            with self.assertRaisesRegex(publication.PublicationError, "unavailable"):
                publication.load_git_source(Path("synthetic-root"), SOURCE, self.source.blob)

    def test_dirty_checkout_is_not_publishable(self):
        def fake_git(command, **kwargs):
            self.assertEqual(command[:5],
                             ["git", "-c", "core.fsmonitor=false", "-C", "synthetic-root"])
            arguments = command[5:]
            if arguments == ["--version"]:
                raw = b"git version 2.55.0.windows.5\n"
            elif arguments[0] == "config":
                raw = b"https://github.com/szl-holdings/lutar-lean.git\n"
            elif arguments[0] == "symbolic-ref":
                raw = b"main\n"
            elif arguments[0] == "rev-parse":
                raw = SOURCE.encode() + b"\n"
            else:
                raw = b"?? unreviewed-source.py\n"
            return subprocess.CompletedProcess(command, 0, raw, b"")

        with patch.object(publication.subprocess, "run", side_effect=fake_git):
            with self.assertRaisesRegex(publication.PublicationError, "changes"):
                publication.load_git_source(Path("synthetic-root"), SOURCE, self.source.blob)

    def test_old_git_is_refused_before_checkout_or_hook_capable_status(self):
        for version in [b"git version 2.35.1\n", b"git version 2.35.2.windows.1\n",
                        b"git version 1.9.5\n"]:
            with self.subTest(version=version):
                output = subprocess.CompletedProcess([], 0, version, b"")
                with patch.object(publication.subprocess, "run", return_value=output) as run:
                    with self.assertRaisesRegex(publication.PublicationError, "Git 2.36"):
                        publication.load_git_source(Path("synthetic-root"), SOURCE, self.source.blob)
                self.assertEqual(run.call_count, 1)
                self.assertEqual(run.call_args.args[0],
                                 ["git", "-c", "core.fsmonitor=false", "-C", "synthetic-root", "--version"])
                self.native_mock.assert_not_called()

    def test_unknown_git_version_is_refused_before_any_checkout_read(self):
        for version in [b"", b"git version unknown\n", b"git version 2.55.0\nextra-output\n"]:
            with self.subTest(version=version):
                output = subprocess.CompletedProcess([], 0, version, b"")
                with patch.object(publication.subprocess, "run", return_value=output) as run:
                    with self.assertRaisesRegex(publication.PublicationError, "Git 2.36"):
                        publication.load_git_source(Path("synthetic-root"), SOURCE, self.source.blob)
                self.assertEqual(run.call_count, 1)
                self.native_mock.assert_not_called()

    def test_windows_reparse_point_and_missing_capability_fail_closed(self):
        for attrs in [0x400, None]:
            information = SimpleNamespace(st_mode=publication.stat.S_IFDIR)
            if attrs is not None:
                information.st_file_attributes = attrs
            path = self.state
            with patch.object(publication.os, "name", "nt"), \
                    patch.object(type(path), "lstat", return_value=information):
                with self.assertRaises(publication.PublicationError):
                    publication.require_plain_state(path)

    def test_cross_origin_redirect_never_forwards_credentials(self):
        handler = publication.SameOriginRedirect()
        for url in ["https://example.org/file", "http://huggingface.co/file",
                    "https://huggingface.co.evil.invalid/file"]:
            with self.assertRaises(publication.PublicationError):
                handler.redirect_request(None, None, 302, "redirect", {}, url)


class NativeSourceTests(unittest.TestCase):
    def setUp(self):
        self.source = publication.SourceCard(SOURCE, publication.blob_oid(CARD), CARD)
        self.branch = {"name": "main", "protected": True, "commit": {"sha": SOURCE}}
        self.commit = {"sha": SOURCE, "verification": {"verified": True, "reason": "valid"}}
        self.blob = {"path": publication.SOURCE_PATH, "type": "file",
                     "sha": self.source.blob, "encoding": "base64", "size": len(CARD),
                     "content": base64.b64encode(CARD).decode()}
        self.branch_raw = None

    def native_run(self, command, **kwargs):
        self.assertEqual(command[:7], ["gh", "api", "--hostname", "github.com", "--method", "GET", command[6]])
        path = command[-1]
        if path.endswith("/branches/main"):
            raw = self.branch_raw or publication.encode(self.branch)
        elif "/git/commits/" in path:
            raw = publication.encode(self.commit)
        else:
            raw = publication.encode(self.blob)
        return subprocess.CompletedProcess(command, 0, raw, b"")

    def verify(self):
        with patch.object(publication.subprocess, "run", side_effect=self.native_run):
            publication.verify_native_source(self.source)

    def test_native_exact_main_protection_signature_and_blob(self):
        self.verify()

    def test_moved_main_unprotected_or_ambiguous_branch_fails(self):
        for branch in [dict(self.branch, commit={"sha": "d" * 40}),
                       dict(self.branch, protected=False), dict(self.branch, protected=None)]:
            self.branch = branch
            with self.assertRaises(publication.PublicationError):
                self.verify()

    def test_unsigned_invalid_or_different_commit_fails(self):
        variants = [{"sha": SOURCE, "verification": {"verified": False, "reason": "unsigned"}},
                    {"sha": SOURCE, "verification": {"verified": True, "reason": "unknown_key"}},
                    {"sha": "d" * 40, "verification": {"verified": True, "reason": "valid"}}]
        for commit in variants:
            self.commit = commit
            with self.assertRaises(publication.PublicationError):
                self.verify()

    def test_duplicate_metadata_or_non_object_or_oversize_is_not_admission(self):
        variants = [b'{"name":"main","protected":true,"protected":false}', b"[]",
                    b"{" * (publication.MAX_FILE_BYTES + 1), b'{"value":NaN}', b"invalid"]
        for raw in variants:
            self.branch_raw = raw
            with self.assertRaises(publication.PublicationError):
                self.verify()

    def test_source_blob_size_encoding_oid_and_content_must_match(self):
        original = dict(self.blob)
        variants = [dict(original, path="another-source.md"), dict(original, type="symlink"),
                    dict(original, sha="e" * 40), dict(original, size=len(CARD) + 1),
                    dict(original, encoding="plain"), dict(original, content="!not-base64"),
                    dict(original, content=base64.b64encode(CARD + b"changed").decode())]
        for blob in variants:
            self.blob = blob
            with self.assertRaises(publication.PublicationError):
                self.verify()

    def test_unavailable_native_read_does_not_expose_error_secret(self):
        with patch.object(publication.subprocess, "run", side_effect=PermissionError("secret-token")):
            with self.assertRaises(publication.PublicationError) as error:
                publication.verify_native_source(self.source)
        self.assertNotIn("secret-token", str(error.exception))


class AdapterTests(unittest.TestCase):
    """SDK/HTTP call shape only; every provider and HTTP response is SIMULATED."""
    def setUp(self):
        self.sdk = ModuleType("huggingface_hub")
        self.sdk_api = ModuleType("huggingface_hub.hf_api")
        self.sdk_utils = ModuleType("huggingface_hub.utils")
        self.api = MagicMock()
        self.sdk.HfApi = MagicMock(return_value=self.api)
        self.sdk.CommitOperationAdd = MagicMock(side_effect=lambda **kwargs: SimpleNamespace(**kwargs))
        self.sdk.hf_hub_url = MagicMock(return_value="https://huggingface.co/datasets/SZLHOLDINGS/lean-theorem-tree/resolve/" + PARENT + "/README.md")
        self.sdk_utils.build_hf_headers = MagicMock(return_value={"Authorization": "Bearer SIMULATED"})
        self.File = type("RepoFile", (), {})
        self.Folder = type("RepoFolder", (), {})
        self.sdk_api.RepoFile, self.sdk_api.RepoFolder = self.File, self.Folder
        modules = {"huggingface_hub": self.sdk, "huggingface_hub.hf_api": self.sdk_api,
                   "huggingface_hub.utils": self.sdk_utils}
        self.modules = patch.dict(sys.modules, modules)
        self.modules.start()
        self.addCleanup(self.modules.stop)
        self.provider = publication.HubProvider()

    def test_sdk_identity_head_and_write_authority_are_explicitly_typed(self):
        self.sdk.HfApi.assert_called_once_with(endpoint="https://huggingface.co", token=True)
        self.api.repo_info.return_value = SimpleNamespace(sha=PARENT)
        self.assertEqual(self.provider.head(), PARENT)
        self.api.repo_info.assert_called_once_with(publication.TARGET, repo_type="dataset", revision="main")
        self.provider.authorize_write()
        self.api.auth_check.assert_called_once_with(publication.TARGET, repo_type="dataset", write=True)

    def test_single_sdk_commit_has_only_readme_expected_parent_and_no_pr(self):
        self.api.create_commit.return_value = SimpleNamespace(oid=COMMIT)
        self.assertEqual(self.provider.commit_readme(CARD, PARENT), COMMIT)
        args, kwargs = self.api.create_commit.call_args
        self.assertEqual(args, (publication.TARGET,))
        self.assertEqual(kwargs["repo_type"], "dataset")
        self.assertEqual(kwargs["revision"], "main")
        self.assertEqual(kwargs["parent_commit"], PARENT)
        self.assertIs(kwargs["create_pr"], False)
        self.assertEqual(len(kwargs["operations"]), 1)
        operation = kwargs["operations"][0]
        self.assertEqual(operation.path_in_repo, "README.md")
        self.assertEqual(operation.path_or_fileobj, CARD)
        self.sdk.CommitOperationAdd.assert_called_once_with(path_in_repo="README.md", path_or_fileobj=CARD)

    def test_paginated_tree_adapter_accepts_folders_and_ordinary_blobs_only(self):
        item = self.File()
        item.path, item.size, item.blob_id = "README.md", len(CARD), publication.blob_oid(CARD)
        item.lfs, item.xet_hash = None, None
        self.api.list_repo_tree.return_value = iter([self.Folder(), item])
        self.assertEqual(list(self.provider.files(PARENT)),
                         [publication.FileSpec(item.path, item.size, item.blob_id)])
        self.api.list_repo_tree.assert_called_once_with(publication.TARGET, repo_type="dataset",
                                                        revision=PARENT, recursive=True)
        for entry in [object(), item]:
            if entry is item:
                item.lfs = {"size": 1}
            self.api.list_repo_tree.return_value = iter([entry])
            with self.assertRaises(publication.PublicationError):
                list(self.provider.files(PARENT))
        item.lfs, item.xet_hash = None, "unsupported-xet-content"
        self.api.list_repo_tree.return_value = iter([item])
        with self.assertRaises(publication.PublicationError):
            list(self.provider.files(PARENT))

    def test_http_bounded_read_and_declared_length_are_enforced(self):
        for length, body, expected_error in [(str(len(CARD)), CARD, False),
                                             (str(len(CARD) + 1), CARD, True),
                                             ("not-a-length", CARD, True),
                                             (None, CARD + b"oversize", True)]:
            response = SimpleNamespace(headers={} if length is None else {"Content-Length": length},
                                       read=MagicMock(return_value=body))
            context = MagicMock()
            context.__enter__.return_value = response
            opener = MagicMock()
            opener.open.return_value = context
            with patch.object(publication.urllib.request, "build_opener", return_value=opener):
                if expected_error:
                    with self.assertRaises(publication.PublicationError):
                        self.provider.read("README.md", PARENT, len(CARD))
                else:
                    self.assertEqual(self.provider.read("README.md", PARENT, len(CARD)), CARD)
                    response.read.assert_called_once_with(len(CARD) + 1)
                    request = opener.open.call_args.args[0]
                    self.assertEqual(request.get_header("Authorization"), "Bearer SIMULATED")
                    self.assertEqual(opener.open.call_args.kwargs["timeout"], 30)

    def test_adapter_auth_failure_is_not_retried(self):
        self.api.auth_check.side_effect = PermissionError("SIMULATED 401")
        with self.assertRaises(PermissionError):
            self.provider.authorize_write()
        self.assertEqual(self.api.auth_check.call_count, 1)


if __name__ == "__main__":
    unittest.main()
