#!/usr/bin/env python3
"""One-target, README-only manual publisher; default is read-only checking.

Protected-source admission and authority must be established by the operator.
Local Git identity and an explicit flag do not prove protected admission. This
program does not deploy, qualify Lean proofs, or verify the hosted viewer.
"""
from __future__ import annotations

import argparse
import base64
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
from typing import Iterable, Protocol
import urllib.parse
import urllib.request
import uuid

SOURCE_REPOSITORY = "szl-holdings/lutar-lean"
SOURCE_PATH = "huggingface/datasets/lean-theorem-tree/README.md"
TARGET = "SZLHOLDINGS/lean-theorem-tree"
REPO_TYPE = "dataset"
CARD_SHA256 = "80efac6d64d5cef24ef75b14a428d22281923942eb4e38f02b359666e03e775d"
IMPORT_SHA256 = "6a11e1311a2c09b49829d650e1a17fe8b66d3de7cea72b1759c5c430bd55c019"
DATA_SHA256 = "85d4a58c08123d7aa26a180b819a3a84e8045c63afe76e4179b21b1056f0cb04"
SELECTOR = (b"configs:\n- config_name: default\n  data_files:\n"
            b"  - split: train\n    path: data/lean_theorem_tree.json\n"
            b"  field: declarations\n")
REQUIRED = {".gitattributes", "README.md", "SZL_ESTATE_MANAGED.json",
            "data/lean_theorem_tree.json"}
MAX_FILES = 128
MAX_FILE_BYTES = 256 * 1024
MAX_TREE_BYTES = 2 * 1024 * 1024
MAX_JOURNAL_BYTES = 512 * 1024
SHA1 = re.compile(r"[0-9a-f]{40}\Z")


class PublicationError(RuntimeError):
    """Safe, non-secret explanation of a failed admission or verification."""


def require_revision(value: str) -> str:
    if not isinstance(value, str) or not SHA1.fullmatch(value):
        raise PublicationError("an exact lowercase 40-character revision is required")
    return value


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def blob_oid(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def timestamp() -> str:
    return datetime.now(timezone.utc).isoformat()


def strict_json(raw: bytes, limit: int = MAX_FILE_BYTES) -> dict:
    """Bounded JSON object with duplicate-member and non-finite-number rejection."""
    if len(raw) > limit:
        raise PublicationError("native metadata exceeds the bounded read contract")

    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise PublicationError("ambiguous duplicate native metadata member")
            result[key] = value
        return result

    def non_finite(_):
        raise PublicationError("non-finite native metadata number refused")

    try:
        value = json.loads(raw.decode("utf-8"), object_pairs_hook=unique,
                           parse_constant=non_finite)
    except (UnicodeError, ValueError) as exc:
        raise PublicationError("native metadata is not a valid bounded JSON object") from exc
    if not isinstance(value, dict):
        raise PublicationError("native metadata must be one JSON object")
    return value


def verify_native_source(source: "SourceCard") -> None:
    """Fresh native REST reads, not CI admission, independent proof, or authority."""
    def read(path):
        try:
            result = subprocess.run(
                ["gh", "api", "--hostname", "github.com", "--method", "GET", path],
                check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30,
            )
        except (OSError, subprocess.SubprocessError) as exc:
            raise PublicationError("native protected-source read is unavailable") from exc
        return strict_json(result.stdout)

    branch = read(f"repos/{SOURCE_REPOSITORY}/branches/main")
    commit_binding = branch.get("commit")
    if (branch.get("name") != "main" or branch.get("protected") is not True
            or not isinstance(commit_binding, dict)
            or commit_binding.get("sha") != source.revision):
        raise PublicationError("native main moved or its protection is not established")
    commit = read(f"repos/{SOURCE_REPOSITORY}/git/commits/{source.revision}")
    verification = commit.get("verification")
    if (commit.get("sha") != source.revision or not isinstance(verification, dict)
            or verification.get("verified") is not True
            or verification.get("reason") != "valid"):
        raise PublicationError("native exact-main commit signature is not verified valid")
    blob = read(f"repos/{SOURCE_REPOSITORY}/contents/{SOURCE_PATH}?ref={source.revision}")
    if (blob.get("path") != SOURCE_PATH or blob.get("type") != "file"
            or blob.get("sha") != source.blob or blob.get("encoding") != "base64"
            or type(blob.get("size")) is not int or blob["size"] != len(source.content)
            or not isinstance(blob.get("content"), str)):
        raise PublicationError("native source blob binding is incomplete or different")
    try:
        content = base64.b64decode(blob["content"].replace("\n", ""), validate=True)
    except (ValueError, UnicodeError) as exc:
        raise PublicationError("native source blob encoding is invalid") from exc
    if content != source.content:
        raise PublicationError("native source blob bytes differ from the frozen card")
    final_branch = read(f"repos/{SOURCE_REPOSITORY}/branches/main")
    final_commit = final_branch.get("commit")
    if (final_branch.get("name") != "main" or final_branch.get("protected") is not True
            or not isinstance(final_commit, dict) or final_commit.get("sha") != source.revision):
        raise PublicationError("native main moved during exact source-path verification")


@dataclass(frozen=True)
class SourceCard:
    revision: str
    blob: str
    content: bytes
    repository: str = SOURCE_REPOSITORY
    path: str = SOURCE_PATH

    def validate(self) -> None:
        require_revision(self.revision)
        require_revision(self.blob)
        if self.repository != SOURCE_REPOSITORY or self.path != SOURCE_PATH:
            raise PublicationError("canonical Git source binding mismatch")
        if not isinstance(self.content, bytes) or sha256(self.content) != CARD_SHA256:
            raise PublicationError("source card is not the admitted config-only candidate")
        if blob_oid(self.content) != self.blob:
            raise PublicationError("source Git blob differs from the exact candidate bytes")
        front, separator, _ = self.content.partition(b"\n---\n")
        if (not self.content.startswith(b"---\n") or not separator
                or self.content.count(SELECTOR) != 1
                or SELECTOR.rstrip(b"\n") not in front
                or sha256(self.content.replace(SELECTOR, b"", 1)) != IMPORT_SHA256):
            raise PublicationError("source card is not solely the reviewed YAML selector")


def load_git_source(root: Path, revision: str, expected_blob: str) -> SourceCard:
    """Read immutable card objects with the supported Git fsmonitor hook disabled."""
    require_revision(revision)
    require_revision(expected_blob)

    def git(*args: str) -> bytes:
        try:
            result = subprocess.run(["git", "-c", "core.fsmonitor=false", "-C", str(root), *args],
                                    check=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE, timeout=20)
        except (OSError, subprocess.SubprocessError) as exc:
            raise PublicationError("canonical Git source read is unavailable") from exc
        return result.stdout

    # Git <= 2.35 can interpret the boolean 'false' as a hook path. Refuse
    # unsupported/unknown versions before any repository read, especially status.
    version = re.fullmatch(rb"git version ([0-9]+)\.([0-9]+)\.[0-9]+(?:[ .-][^\r\n]*)?",
                           git("--version").strip())
    if version is None or (int(version[1]), int(version[2])) < (2, 36):
        raise PublicationError("Git 2.36 or newer with a recognized version is required")

    remote = git("config", "--get", "remote.origin.url").decode("utf-8").strip()
    if remote not in {"https://github.com/szl-holdings/lutar-lean",
                      "https://github.com/szl-holdings/lutar-lean.git",
                      "git@github.com:szl-holdings/lutar-lean.git"}:
        raise PublicationError("origin is not the canonical source repository")
    if git("symbolic-ref", "--short", "HEAD").strip() != b"main":
        raise PublicationError("manual publication requires the admitted main checkout")
    if git("rev-parse", "HEAD").strip().decode() != revision:
        raise PublicationError("checkout HEAD differs from the frozen admitted source")
    if git("status", "--porcelain=v1", "--untracked-files=all"):
        raise PublicationError("manual source checkout has tracked, staged, or untracked changes")
    if git("cat-file", "-t", revision).strip() != b"commit":
        raise PublicationError("source revision is not a commit")
    object_name = f"{revision}:{SOURCE_PATH}"
    actual_blob = git("rev-parse", object_name).strip().decode()
    if actual_blob != expected_blob:
        raise PublicationError("Git source path does not identify the expected blob")
    size = git("cat-file", "-s", object_name).strip()
    if not size.isdigit() or int(size) > MAX_FILE_BYTES:
        raise PublicationError("Git source card exceeds the bounded byte contract")
    source = SourceCard(revision, actual_blob, git("cat-file", "blob", object_name))
    source.validate()
    verify_native_source(source)
    return source


@dataclass(frozen=True)
class FileSpec:
    path: str
    size: int
    blob: str


class Provider(Protocol):
    repo_id: str
    repo_type: str

    def head(self) -> str: ...
    def files(self, revision: str) -> Iterable[FileSpec]: ...
    def read(self, path: str, revision: str, limit: int) -> bytes: ...
    def authorize_write(self) -> None: ...
    def commit_readme(self, content: bytes, expected_parent: str) -> str: ...


def snapshot(api: Provider, revision: str) -> tuple[dict, dict[str, bytes]]:
    """Consume the entire provider iterator; partial pages are never a snapshot."""
    require_revision(revision)
    specs: dict[str, FileSpec] = {}
    total = 0
    for spec in api.files(revision):
        path = spec.path
        if (not isinstance(path, str) or not path or "\\" in path
                or len(path.encode("utf-8")) > 512 or any(ord(char) < 32 for char in path)
                or path.startswith("/") or str(PurePosixPath(path)) != path
                or any(part in {".", "..", ""} for part in path.split("/"))
                or path in specs):
            raise PublicationError("unsafe or duplicate provider path")
        require_revision(spec.blob)
        if type(spec.size) is not int or not 0 <= spec.size <= MAX_FILE_BYTES:
            raise PublicationError("provider file exceeds the bounded ordinary-blob contract")
        specs[path] = spec
        total += spec.size
        if len(specs) > MAX_FILES or total > MAX_TREE_BYTES:
            raise PublicationError("provider tree exceeds the closed bounded read contract")
    if not REQUIRED.issubset(specs):
        raise PublicationError("complete provider map lacks required preserved files")
    result, content = {}, {}
    for path in sorted(specs):
        spec = specs[path]
        raw = api.read(path, revision, spec.size)
        if not isinstance(raw, bytes) or len(raw) != spec.size or blob_oid(raw) != spec.blob:
            raise PublicationError("immutable provider bytes differ from the native blob map")
        content[path] = raw
        result[path] = {"sha256": sha256(raw), "size": len(raw), "blob": spec.blob}
    if result["data/lean_theorem_tree.json"]["sha256"] != DATA_SHA256:
        raise PublicationError("data differs from the qualified unchanged declaration snapshot")
    return result, content


def durable_create(path: Path, data: bytes) -> None:
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(fd, "wb") as output:
        output.write(data)
        output.flush()
        os.fsync(output.fileno())


def encode(record: dict) -> bytes:
    return (json.dumps(record, sort_keys=True, indent=2) + "\n").encode("utf-8")


def durable_update(path: Path, record: dict) -> None:
    # Never truncate the pending journal. A failed replacement leaves that fence.
    if path.stat().st_size > MAX_JOURNAL_BYTES:
        raise PublicationError("publication journal exceeds its bounded owner-evidence contract")
    previous = strict_json(path.read_bytes(), MAX_JOURNAL_BYTES)
    if previous.get("attempt_id") != record.get("attempt_id"):
        raise PublicationError("publication journal ownership changed; evidence preserved")
    temporary = path.with_name(path.name + "." + uuid.uuid4().hex + ".tmp")
    durable_create(temporary, encode(record))
    os.replace(temporary, path)


def check_journal(path: Path) -> None:
    if path.exists():
        # No journal is silently reset, including completed/partially-written ones.
        raise PublicationError("existing publication journal requires owner reconciliation; no replay")


def require_plain_state(path: Path) -> None:
    """Reject symlinks and all Windows reparse points without version-dependent APIs."""
    for component in (path, *path.parents):
        try:
            information = component.lstat()
        except FileNotFoundError:
            continue
        if stat.S_ISLNK(information.st_mode):
            raise PublicationError("publication state ancestry contains a symlink")
        if os.name == "nt":
            attributes = getattr(information, "st_file_attributes", None)
            if type(attributes) is not int:
                raise PublicationError("Windows publication state reparse checking is unavailable")
            if attributes & getattr(stat, "FILE_ATTRIBUTE_REPARSE_POINT", 0x400):
                raise PublicationError("publication state ancestry contains a Windows reparse point")


def publish(api: Provider, source: SourceCard, expected_parent: str, state_dir: Path,
            *, apply: bool = False, authorized: bool = False) -> dict:
    source.validate()
    require_revision(expected_parent)
    if api.repo_id != TARGET or api.repo_type != REPO_TYPE:
        raise PublicationError("fixed typed dataset target mismatch")
    if apply and not authorized:
        raise PublicationError("manual provider write requires explicit existing owner authority")
    state_dir = Path(state_dir)
    if not state_dir.is_absolute():
        raise PublicationError("canonical publication state requires an absolute lexical path")
    require_plain_state(state_dir)
    journal = state_dir / "lean-theorem-tree.publication.json"
    lock = state_dir / "lean-theorem-tree.writer.lock"
    check_journal(journal)
    lock_bytes = None
    pending = False
    journal_owned = False
    record = None
    try:
        if apply:
            state_dir.mkdir(parents=True, exist_ok=True)
            lock_bytes = encode({"nonce": uuid.uuid4().hex, "target": TARGET,
                                 "created_at": timestamp(), "source": source.revision})
            try:
                durable_create(lock, lock_bytes)
            except FileExistsError as exc:
                raise PublicationError("existing sole-writer lock requires its owner's action") from exc
            check_journal(journal)  # Close the race before the lock was acquired.
        if api.head() != expected_parent:
            raise PublicationError("provider main differs from the expected parent")
        before, content = snapshot(api, expected_parent)
        if before["README.md"]["sha256"] not in {IMPORT_SHA256, CARD_SHA256}:
            raise PublicationError("concurrent card changes are not eligible for replacement")
        result = {"evidence_class": "MEASURED", "target": TARGET, "repo_type": REPO_TYPE,
                  "source_repository": SOURCE_REPOSITORY, "source_revision": source.revision,
                  "source_blob": source.blob, "source_card_sha256": CARD_SHA256,
                  "expected_parent": expected_parent, "before": before,
                  "provider_writes": 0, "viewer_verified": False,
                  "protected_admission_verified_by_this_program": False}
        if content["README.md"] == source.content:
            result["status"] = "NO_CHANGE"
            return result
        if not apply:
            result["status"] = "CHECK_ONLY"
            return result
        api.authorize_write()  # Actual exact-target provider write authorization check.
        # Snapshot downloads can take time; refresh source main/signature/blob
        # again at the write boundary rather than relying on initial CLI load.
        verify_native_source(source)
        if api.head() != expected_parent:
            raise PublicationError("provider head advanced after the authority preflight")
        record = dict(result, schema="szl.lean-card-publication/v1", status="PENDING",
                      allowed_paths=["README.md"], started_at=timestamp(),
                      authorization="DECLARED", publication="UNKNOWN",
                      attempt_id=uuid.uuid4().hex, provider_writes="UNKNOWN",
                      planned_write_attempts=1, provider_call_returned="UNKNOWN")
        # From this point onward, failures retain both journal and sole-writer lock.
        pending = True
        durable_create(journal, encode(record))
        journal_owned = True
        native_commit = require_revision(api.commit_readme(source.content, expected_parent))
        record["provider_commit"] = native_commit
        record["provider_call_returned"] = True
        record["provider_writes"] = 1
        durable_update(journal, record)
        after, _ = snapshot(api, native_commit)
        if set(after) != set(before):
            raise PublicationError("publication changed the complete provider file set")
        for path in before:
            expected = ({"sha256": CARD_SHA256, "size": len(source.content),
                         "blob": source.blob} if path == "README.md" else before[path])
            if after[path] != expected:
                raise PublicationError("publication readback exceeds README-only exact-byte scope")
        if api.head() != native_commit:
            raise PublicationError("provider main advanced during immutable readback")
        record.update(status="VERIFIED", publication="MEASURED", after=after,
                      verified_at=timestamp(), unknown_write=False)
        durable_update(journal, record)
        pending = False
        return record
    except BaseException as exc:
        if pending and journal_owned and record is not None:
            record.update(status="UNKNOWN", publication="UNKNOWN", unknown_write=True,
                          provider_writes="UNKNOWN",
                          exception_class=type(exc).__name__, stopped_at=timestamp())
            # Never expose an exception message that might contain a token or URL.
            try:
                durable_update(journal, record)
            except BaseException:
                pass  # Existing pending/partial journal and lock remain; no retry.
        raise
    finally:
        if lock_bytes is not None and not pending:
            # Do not remove another writer's lock, even on a preflight failure.
            if lock.exists() and lock.read_bytes() == lock_bytes:
                lock.unlink()


class SameOriginRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, request, response, code, message, headers, newurl):
        origin = urllib.parse.urlsplit(newurl)
        if origin.scheme != "https" or origin.netloc != "huggingface.co":
            raise PublicationError("cross-origin provider download redirect refused")
        return super().redirect_request(request, response, code, message, headers, newurl)


class HubProvider:
    """Real SDK adapter; no creation, deletion, restart, job, or upload-folder path."""
    repo_id = TARGET
    repo_type = REPO_TYPE

    def __init__(self):
        from huggingface_hub import HfApi
        self.api = HfApi(endpoint="https://huggingface.co", token=True)

    def head(self) -> str:
        return require_revision(self.api.repo_info(TARGET, repo_type=REPO_TYPE, revision="main").sha)

    def files(self, revision: str) -> Iterable[FileSpec]:
        from huggingface_hub.hf_api import RepoFile, RepoFolder
        for entry in self.api.list_repo_tree(TARGET, repo_type=REPO_TYPE,
                                            revision=revision, recursive=True):
            if isinstance(entry, RepoFolder):
                continue
            if (not isinstance(entry, RepoFile) or entry.lfs is not None
                    or getattr(entry, "xet_hash", None) is not None):
                raise PublicationError("non-ordinary provider blob requires separate qualification")
            yield FileSpec(entry.path, entry.size, entry.blob_id)

    def read(self, path: str, revision: str, limit: int) -> bytes:
        from huggingface_hub import hf_hub_url
        from huggingface_hub.utils import build_hf_headers
        url = hf_hub_url(TARGET, path, repo_type=REPO_TYPE, revision=revision,
                        endpoint="https://huggingface.co")
        request = urllib.request.Request(url, headers=build_hf_headers(token=True))
        opener = urllib.request.build_opener(SameOriginRedirect())
        with opener.open(request, timeout=30) as response:
            size = response.headers.get("Content-Length")
            if size is not None and (not size.isdigit() or int(size) > limit):
                raise PublicationError("provider response exceeds the expected immutable byte length")
            raw = response.read(limit + 1)
            if len(raw) > limit:
                raise PublicationError("provider response exceeded the bounded byte read")
            return raw

    def authorize_write(self) -> None:
        self.api.auth_check(TARGET, repo_type=REPO_TYPE, write=True)

    def commit_readme(self, content: bytes, expected_parent: str) -> str:
        from huggingface_hub import CommitOperationAdd
        result = self.api.create_commit(
            TARGET, repo_type=REPO_TYPE, revision="main", parent_commit=expected_parent,
            operations=[CommitOperationAdd(path_in_repo="README.md", path_or_fileobj=content)],
            commit_message="fix(dataset): select unchanged theorem declarations",
            commit_description="README-only config from admitted canonical lutar-lean source.",
            create_pr=False,
        )
        return result.oid


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--source-blob", required=True)
    parser.add_argument("--expected-parent", required=True)
    parser.add_argument("--state-dir", type=Path, required=True,
                        help="Existing canonical private owner state; never switch paths to evade a fence")
    parser.add_argument("--publish", action="store_true")
    parser.add_argument("--authorized", action="store_true",
                        help="Explicit operator confirmation of pre-established protected admission and authority")
    args = parser.parse_args(argv)
    try:
        source = load_git_source(args.repo_root, args.source_sha, args.source_blob)
        result = publish(HubProvider(), source, args.expected_parent, args.state_dir,
                         apply=args.publish, authorized=args.authorized)
        print(json.dumps(result, sort_keys=True, indent=2))
        return 0
    except BaseException as exc:
        message = str(exc) if isinstance(exc, PublicationError) else "native operation unavailable; inspect retained owner evidence"
        print(json.dumps({"evidence_class": "BLOCKED", "exception_class": type(exc).__name__,
                          "reason": message, "operational_completion": False}))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
