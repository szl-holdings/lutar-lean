#!/usr/bin/env python3
"""Anchor a cosign-signed proof-milestone snapshot into szl-holdings/szl-lake.

Runs in lutar-lean CI (anchor-szl-lake.yml) after the snapshot artifact has been
downloaded from a GREEN build run and signed with `cosign attest-blob`
(keyless OIDC, DSSE in-toto). This script:

  1. Cross-checks the cosign Sigstore bundle: the DSSE in-toto subject digest MUST
     equal the snapshot sha256, the signing certificate SAN identity MUST be a
     lutar-lean workflow, and the OIDC issuer MUST be GitHub Actions. (No fabricated
     signatures: if any check fails we abort.)
  2. Builds an append-only DSSE Khipu receipt (schema szl.khipu.receipt/v1) that
     embeds the snapshot, the verified source-run pointer, and the full cosign
     bundle (base64) plus parsed Rekor/identity material for offline verification.
  3. chain_index advances by exactly one over the existing lutar-lean chain
     (genesis count 0 -> first receipt chain_index 1, prev_hash null). Idempotent:
     if this (kind, kernel_commit, snapshot) is already anchored, it is a no-op.
  4. Appends the receipt to BOTH surfaces:
       * HF dataset SZLHOLDINGS/szl-lake : khipu/lutar_lean_receipts.ndjson (canonical)
       * GitHub szl-holdings/szl-lake     : data/khipu/lutar_lean_receipts.ndjson
         + updates the front-door lake_index.json (per-kind `anchors` pointer +
           `latest_anchor`; the legacy `theorem_u_anchor` pointer is preserved and
           only refreshed when kind == theorem-u)
     The GitHub commit is GitHub-signed via GraphQL createCommitOnBranch with a
     DCO Signed-off-by trailer (main requires signed commits + DCO).
  5. Re-reads the HF NDJSON and asserts the new receipt is present and the chain
     advanced by exactly one.

Originally Theorem-U-specific; now generalized so ANY green proof milestone can be
anchored on the same append-only chain. The honesty labeling is carried verbatim,
per-snapshot, from the snapshot's own honesty block -- never a blanket "proven".
"""
from __future__ import annotations

import argparse
import base64
import datetime as _dt
import hashlib
import json
import os
import urllib.error
import urllib.request

HF_REPO = "SZLHOLDINGS/szl-lake"
GH_REPO = "szl-holdings/szl-lake"
HF_NDJSON = "khipu/lutar_lean_receipts.ndjson"
GH_NDJSON = "data/khipu/lutar_lean_receipts.ndjson"
GH_INDEX = "lake_index.json"
# Append-only floor read by szl-lake's verify-anchor-receipts.yml. Bumped to the
# new chain length in the SAME signed commit that appends a receipt (see
# bump_baseline_floor + main); never lowered.
GH_BASELINE = ".github/verify-anchor-receipts-baseline.json"
BASELINE_COMMENT = (
    "Append-only floor for the anchor ledger (khipu/lutar_lean_receipts.ndjson). "
    "verify-anchor-receipts.yml fails LOUDLY if either surface drops below this "
    "many receipts, so a wiped or truncated ledger can never pass green with "
    "'nothing to check'. AUTO-MAINTAINED: lutar-lean's anchor_szl_lake.py raises "
    "this to the new chain length in the SAME signed commit that appends a receipt "
    "(chain_index N => min_receipts N); never lowered."
)
# Per-theorem anchor manifests land at the SAME relative path on both surfaces so
# the GitHub and HF copies are byte-identical.
THEOREMS_DIR = "attestations/innovations/theorems"

THEOREM_ANCHOR_SCHEMA = "szl.lake.theorem-anchors/v1"

GH_OIDC_ISSUER = "https://token.actions.githubusercontent.com"
IDENTITY_PREFIX = "https://github.com/szl-holdings/lutar-lean/"

DEFAULT_PREDICATE_TYPE = "https://szl-holdings/theorem-u-anchor/v1"

# DCO / commit identity (org-owner token).
COMMIT_NAME = os.environ.get("ANCHOR_COMMIT_NAME", "Lutar, Stephen P.")
COMMIT_EMAIL = os.environ.get("ANCHOR_COMMIT_EMAIL", "stephenlutar2@gmail.com")

UA = "szl-lake-anchor/2.0"


def _utcnow() -> str:
    return _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def canonical_hash(obj) -> str:
    return _sha256_bytes(json.dumps(obj, sort_keys=True, separators=(",", ":")).encode())


def get_milestone(snapshot: dict) -> dict:
    """Return the milestone block, tolerating the legacy `theorem_u` key."""
    return snapshot.get("milestone") or snapshot.get("theorem_u") or {}


def find_existing_anchor(existing: list, receipt_kind: str,
                         kernel_commit: str, snapshot_sha: str):
    """Return the already-anchored receipt matching the idempotency tuple
    (kind, kernel_commit, snapshot_sha), or None.

    Anchoring is a no-op when this returns a record, so a re-run never
    double-appends the same milestone. Extracted as a pure helper so the
    idempotency contract is unit-testable (test_anchor_and_snapshot.py).
    """
    for rec in existing:
        if (rec.get("kind") == receipt_kind
                and rec.get("kernel_commit") == kernel_commit
                and rec.get("subject", {}).get("sha256") == snapshot_sha):
            return rec
    return None


def chain_position(existing: list):
    """Return (chain_index, prev_hash) for the next receipt on the chain.

    chain_index advances by exactly one (genesis count 0 -> first receipt 1);
    prev_hash is the previous tail's receipt_id (None at genesis). Pure helper
    so the chain math is unit-testable (test_anchor_and_snapshot.py).
    """
    chain_index = len(existing) + 1
    prev_hash = existing[-1].get("receipt_id") if existing else None
    return chain_index, prev_hash


def baseline_floor(existing_raw) -> int:
    """Return the current `min_receipts` floor from the raw baseline JSON (0 if
    absent/malformed). Pure helper -> unit-testable."""
    try:
        doc = json.loads(existing_raw) if existing_raw else {}
        return int(doc.get("min_receipts", 0)) if isinstance(doc, dict) else 0
    except (ValueError, TypeError):
        return 0


def bump_baseline_floor(existing_raw, chain_index: int):
    """Return the updated baseline JSON string when the append-only floor must
    rise to `chain_index`, else None (idempotent / already at-or-above).

    The floor in szl-lake's `.github/verify-anchor-receipts-baseline.json`
    (`min_receipts`) defeats the "empty ledger passes green with nothing to check"
    failure mode: verify-anchor-receipts.yml fails loud if either surface drops
    below it. It is APPEND-ONLY -- this NEVER lowers the floor and only ever
    returns a higher one. Preserves any other keys in the file and refreshes the
    `_comment` to document the auto-maintenance. Pure helper so the never-lower
    contract is unit-testable.
    """
    try:
        doc = json.loads(existing_raw) if existing_raw else {}
    except (ValueError, TypeError):
        doc = {}
    if not isinstance(doc, dict):
        doc = {}
    if chain_index <= baseline_floor(existing_raw):
        return None
    doc["_comment"] = BASELINE_COMMENT
    doc["min_receipts"] = chain_index
    return json.dumps(doc, indent=2, ensure_ascii=False) + "\n"


# --------------------------------------------------------------------------- #
# cosign bundle inspection
# --------------------------------------------------------------------------- #
def parse_cosign_bundle(bundle: dict, snapshot_sha: str) -> dict:
    """Validate the Sigstore bundle and extract verification material.

    Aborts (raises) on any mismatch -- this is the no-fabricated-signature gate.
    """
    vm = bundle.get("verificationMaterial") or {}

    # Certificate (single leaf or chain).
    cert_b64 = None
    if "certificate" in vm and vm["certificate"].get("rawBytes"):
        cert_b64 = vm["certificate"]["rawBytes"]
    elif "x509CertificateChain" in vm:
        certs = vm["x509CertificateChain"].get("certificates") or []
        if certs:
            cert_b64 = certs[0].get("rawBytes")
    if not cert_b64:
        raise SystemExit("::error::cosign bundle has no signing certificate")

    san_uris, oidc_issuer = _cert_identity(base64.b64decode(cert_b64))
    matching = [u for u in san_uris if u.startswith(IDENTITY_PREFIX)]
    if not matching:
        raise SystemExit(
            f"::error::cert SAN identity is not a lutar-lean workflow: {san_uris}")
    if oidc_issuer and oidc_issuer != GH_OIDC_ISSUER:
        raise SystemExit(f"::error::unexpected OIDC issuer in cert: {oidc_issuer}")

    # DSSE in-toto subject digest must equal the snapshot sha256.
    env = bundle.get("dsseEnvelope") or {}
    payload_b64 = env.get("payload")
    payload_type = env.get("payloadType")
    if not payload_b64:
        raise SystemExit("::error::cosign bundle has no DSSE envelope payload")
    statement = json.loads(base64.b64decode(payload_b64))
    subj_digests = [
        s.get("digest", {}).get("sha256")
        for s in statement.get("subject", [])
    ]
    if snapshot_sha not in subj_digests:
        raise SystemExit(
            f"::error::DSSE subject digest {subj_digests} != snapshot sha256 {snapshot_sha}")

    # Rekor transparency log entry.
    rekor_log_index = None
    rekor_integrated_time = None
    tlog = vm.get("tlogEntries") or []
    if tlog:
        rekor_log_index = tlog[0].get("logIndex")
        rekor_integrated_time = tlog[0].get("integratedTime")

    return {
        "mode": "cosign-keyless-oidc",
        "dsse": True,
        "payload_type": payload_type,
        "predicate_type": statement.get("predicateType"),
        "fulcio_identity": matching[0],
        "fulcio_san_uris": san_uris,
        "oidc_issuer": oidc_issuer or GH_OIDC_ISSUER,
        "rekor_log_index": rekor_log_index,
        "rekor_integrated_time": rekor_integrated_time,
        "bundle_media_type": bundle.get("mediaType"),
    }


def _cert_identity(der: bytes):
    """Return (san_uris, oidc_issuer) from a Fulcio leaf certificate."""
    try:
        from cryptography import x509
        from cryptography.x509.oid import ExtensionOID, ObjectIdentifier
    except Exception as exc:  # pragma: no cover
        raise SystemExit(f"::error::cryptography unavailable to parse cert: {exc}")
    cert = x509.load_der_x509_certificate(der)
    san_uris: list[str] = []
    try:
        san = cert.extensions.get_extension_for_oid(
            ExtensionOID.SUBJECT_ALTERNATIVE_NAME).value
        san_uris = list(san.get_values_for_type(x509.UniformResourceIdentifier))
    except Exception:
        pass
    oidc_issuer = None
    # Fulcio OIDC issuer (v2) OID 1.3.6.1.4.1.57264.1.8, else legacy .1.1.
    for oid in ("1.3.6.1.4.1.57264.1.8", "1.3.6.1.4.1.57264.1.1"):
        try:
            ext = cert.extensions.get_extension_for_oid(ObjectIdentifier(oid))
            raw = ext.value.value
            # v2 is a DER UTF8String; strip the 2-byte tag/len if present.
            if len(raw) > 2 and raw[0] == 0x0C:
                raw = raw[2:]
            oidc_issuer = raw.decode("utf-8", "replace")
            break
        except Exception:
            continue
    return san_uris, oidc_issuer


# --------------------------------------------------------------------------- #
# HF dataset I/O
# --------------------------------------------------------------------------- #
def hf_read_ndjson(token: str) -> list[dict]:
    url = f"https://huggingface.co/datasets/{HF_REPO}/raw/main/{HF_NDJSON}"
    req = urllib.request.Request(url, headers={"Authorization": f"Bearer {token}", "User-Agent": UA})
    try:
        with urllib.request.urlopen(req, timeout=60) as r:
            body = r.read().decode("utf-8")
    except urllib.error.HTTPError as e:
        if e.code == 404:
            return []
        raise
    return [json.loads(l) for l in body.splitlines() if l.strip()]


def hf_upload(token: str, content: str, commit_msg: str) -> None:
    from huggingface_hub import HfApi
    import tempfile
    api = HfApi(token=token)
    with tempfile.NamedTemporaryFile("w", suffix=".ndjson", delete=False, encoding="utf-8") as tf:
        tf.write(content)
        tmp = tf.name
    api.upload_file(
        path_or_fileobj=tmp,
        path_in_repo=HF_NDJSON,
        repo_id=HF_REPO,
        repo_type="dataset",
        commit_message=commit_msg,
    )


def hf_upload_file(token: str, path_in_repo: str, content: str, commit_msg: str) -> None:
    """Upload an arbitrary text file to the HF dataset (used for theorem manifests)."""
    from huggingface_hub import HfApi
    import tempfile
    api = HfApi(token=token)
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False, encoding="utf-8") as tf:
        tf.write(content)
        tmp = tf.name
    api.upload_file(
        path_or_fileobj=tmp,
        path_in_repo=path_in_repo,
        repo_id=HF_REPO,
        repo_type="dataset",
        commit_message=commit_msg,
    )


# --------------------------------------------------------------------------- #
# Per-theorem anchor manifest (every CI-green theorem -> szl-lake)
# --------------------------------------------------------------------------- #
def build_theorem_manifest(snapshot: dict, snapshot_sha: str, kind: str,
                           kernel_commit: str, receipt_id: str, chain_index: int,
                           verify_cmd: str):
    """Build the deterministic per-theorem anchor manifest from the snapshot.

    Returns (relpath, manifest_str) or (None, None) when the snapshot carries no
    verified_theorems block. The manifest carries NO timestamp so its bytes depend
    only on the (idempotent) snapshot + chain position -- making the GitHub and HF
    copies byte-identical and a re-anchor of the same milestone reproducible.
    """
    vt = snapshot.get("verified_theorems") or {}
    theorems = vt.get("theorems") or []
    if not theorems:
        return None, None
    rel = f"{THEOREMS_DIR}/{kernel_commit or snapshot_sha}.json"
    manifest = {
        "schema": THEOREM_ANCHOR_SCHEMA,
        "organ": "lutar-lean",
        "milestone_kind": kind,
        "kernel_commit": kernel_commit,
        "kernel_commit_short": snapshot.get("kernel_commit_short", ""),
        "branch": snapshot.get("branch", ""),
        "snapshot_sha256": snapshot_sha,
        "receipt_id": receipt_id,
        "chain_index": chain_index,
        "doctrine": vt.get("doctrine") or snapshot.get("honesty", {}).get("doctrine", "v11"),
        "source": vt.get("source"),
        "source_sha256": vt.get("source_sha256"),
        "count": vt.get("count", len(theorems)),
        "honesty": snapshot.get("honesty", {}),
        "theorems": theorems,
        "github_path": rel,
        "hf_path": rel,
        "verify_cmd": verify_cmd,
    }
    manifest_str = json.dumps(manifest, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    return rel, manifest_str


# --------------------------------------------------------------------------- #
# GitHub szl-lake I/O (signed commit via GraphQL)
# --------------------------------------------------------------------------- #
def gh_api(token: str, method: str, path: str, body=None):
    url = f"https://api.github.com{path}"
    data = json.dumps(body).encode() if body is not None else None
    req = urllib.request.Request(url, data=data, method=method, headers={
        "Authorization": f"Bearer {token}", "User-Agent": UA,
        "Accept": "application/vnd.github+json",
        "Content-Type": "application/json",
    })
    try:
        with urllib.request.urlopen(req, timeout=60) as r:
            return r.status, json.loads(r.read().decode())
    except urllib.error.HTTPError as e:
        return e.code, json.loads(e.read().decode() or "{}")


def gh_get_raw(token: str, path: str, ref: str = "main"):
    url = f"https://api.github.com/repos/{GH_REPO}/contents/{path}?ref={ref}"
    req = urllib.request.Request(url, headers={
        "Authorization": f"Bearer {token}", "User-Agent": UA,
        "Accept": "application/vnd.github.raw",
    })
    try:
        with urllib.request.urlopen(req, timeout=60) as r:
            return r.read().decode("utf-8")
    except urllib.error.HTTPError as e:
        if e.code == 404:
            return None
        raise


def gh_graphql(token: str, query: str, variables: dict):
    req = urllib.request.Request(
        "https://api.github.com/graphql",
        data=json.dumps({"query": query, "variables": variables}).encode(),
        method="POST",
        headers={"Authorization": f"Bearer {token}", "User-Agent": UA,
                 "Content-Type": "application/json"},
    )
    with urllib.request.urlopen(req, timeout=60) as r:
        return json.loads(r.read().decode())


def gh_signed_commit(token: str, additions: list[dict], message: str) -> str:
    """Create a GitHub-signed commit on szl-lake main with file additions."""
    st, ref = gh_api(token, "GET", f"/repos/{GH_REPO}/git/ref/heads/main")
    if st != 200:
        raise SystemExit(f"::error::cannot read szl-lake main ref: {st} {ref}")
    head_oid = ref["object"]["sha"]
    q = """
    mutation($input: CreateCommitOnBranchInput!) {
      createCommitOnBranch(input: $input) { commit { oid url } }
    }"""
    variables = {"input": {
        "branch": {"repositoryNameWithOwner": GH_REPO, "branchName": "main"},
        "message": {"headline": message.split("\n")[0],
                    "body": "\n".join(message.split("\n")[1:]).strip()},
        "fileChanges": {"additions": additions},
        "expectedHeadOid": head_oid,
    }}
    res = gh_graphql(token, q, variables)
    if res.get("errors"):
        raise SystemExit(f"::error::createCommitOnBranch failed: {res['errors']}")
    return res["data"]["createCommitOnBranch"]["commit"]["url"]


# --------------------------------------------------------------------------- #
def _self_test() -> int:
    """Offline self-test for the per-theorem manifest (no network/cosign/build)."""
    snap = {
        "kind": "theorem-u",
        "kernel_commit": "deadbeef" * 5,
        "kernel_commit_short": "deadbeefdead",
        "branch": "main",
        "honesty": {"doctrine": "v11"},
        "verified_theorems": {
            "schema": "szl.lake.verified-theorems/v1",
            "source": "VERIFIED_THEOREMS.generated.md",
            "source_sha256": "a" * 64,
            "doctrine": "v11",
            "count": 2,
            "theorems": [
                {"file": "Lutar/Uniqueness.lean", "name": "lambda_satisfiesAxioms",
                 "signature": "lambda_satisfiesAxioms ... : LutarAxioms (\u039b k)"},
                {"file": "Lutar/Uniqueness/TheoremU.lean", "name": "TheoremU_LambdaUnique",
                 "signature": "TheoremU_LambdaUnique ... : LambdaEquiv \u03a6 \u03a8"},
            ],
        },
    }
    ok = True

    def chk(cond, msg):
        nonlocal ok
        if not cond:
            ok = False
            print(f"SELF-TEST FAIL: {msg}")

    rel1, m1 = build_theorem_manifest(snap, "f" * 64, "theorem-u",
                                      snap["kernel_commit"], "rid123", 7, "cosign verify ...")
    rel2, m2 = build_theorem_manifest(snap, "f" * 64, "theorem-u",
                                      snap["kernel_commit"], "rid123", 7, "cosign verify ...")
    chk(rel1 == rel2 == f"{THEOREMS_DIR}/{snap['kernel_commit']}.json", f"manifest path: {rel1}")
    chk(m1 == m2, "manifest must be deterministic (byte-identical re-build)")
    obj = json.loads(m1)
    chk(obj["schema"] == THEOREM_ANCHOR_SCHEMA, "schema")
    chk(obj["count"] == 2 and len(obj["theorems"]) == 2, "theorem count")
    chk(obj["receipt_id"] == "rid123", "receipt_id link")
    chk(obj["github_path"] == obj["hf_path"] == rel1, "github/hf paths must match (byte-identical)")
    chk("timestamp" not in obj and "anchored_at_utc" not in obj,
        "manifest must carry NO timestamp (deterministic/byte-identical)")
    rel0, m0 = build_theorem_manifest({"verified_theorems": {"theorems": []}},
                                      "x", "k", "c", "r", 1, "v")
    chk(rel0 is None and m0 is None, "empty theorem set -> no manifest")
    rel_n, m_n = build_theorem_manifest({}, "x", "k", "c", "r", 1, "v")
    chk(rel_n is None and m_n is None, "missing verified_theorems -> no manifest")
    print("SELF-TEST: PASS" if ok else "SELF-TEST: FAILED")
    return 0 if ok else 1


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--snapshot", default=None)
    ap.add_argument("--bundle", default=None)
    ap.add_argument("--source-run-id", default=None)
    ap.add_argument("--source-run-url", default="")
    ap.add_argument("--source-workflow", default="Lake build (gate + numbers)")
    ap.add_argument("--predicate-type", default=DEFAULT_PREDICATE_TYPE,
                    help="cosign attestation predicate type used to sign the snapshot")
    ap.add_argument("--self-test", action="store_true",
                    help="run offline manifest self-tests (no network/cosign/build) and exit")
    args = ap.parse_args()

    if args.self_test:
        return _self_test()
    missing = [f"--{n.replace('_', '-')}" for n in ("snapshot", "bundle", "source_run_id")
               if not getattr(args, n)]
    if missing:
        ap.error("the following arguments are required: " + ", ".join(missing))

    gh_token = os.environ["SZL_LAKE_TOKEN"]
    hf_token = os.environ["HF_LAKE_TOKEN"]

    with open(args.snapshot, "rb") as fh:
        snap_bytes = fh.read()
    snapshot = json.loads(snap_bytes)
    snapshot_sha = _sha256_bytes(snap_bytes)
    with open(args.bundle, "r", encoding="utf-8") as fh:
        bundle_raw = fh.read()
    bundle = json.loads(bundle_raw)

    kind = snapshot.get("kind", "theorem-u")
    milestone = get_milestone(snapshot)
    receipt_kind = f"{kind}-anchor"

    signing = parse_cosign_bundle(bundle, snapshot_sha)
    signing["bundle_b64"] = base64.b64encode(bundle_raw.encode()).decode()
    predicate_type = signing.get("predicate_type") or args.predicate_type
    signing["verify_cmd"] = (
        "cosign verify-blob-attestation --new-bundle-format "
        f"--bundle <bundle> --type {predicate_type} "
        f"--certificate-identity-regexp '^{IDENTITY_PREFIX}' "
        f"--certificate-oidc-issuer '{GH_OIDC_ISSUER}' {os.path.basename(args.snapshot)}")

    kernel_commit = snapshot.get("kernel_commit", "")
    numbers = snapshot.get("lean_numbers", {}).get("numbers", {})

    # ---- chain state + idempotency -------------------------------------- #
    existing = hf_read_ndjson(hf_token)
    already = find_existing_anchor(existing, receipt_kind, kernel_commit, snapshot_sha)
    if already is not None:
        print(f"already anchored: kind={kind} kernel_commit={kernel_commit} "
              f"chain_index={already.get('chain_index')} receipt_id={already.get('receipt_id')}")
        print(f"::notice::idempotent no-op (HF chain length stays {len(existing)})")
        return 0
    prev_count = len(existing)
    chain_index, prev_hash = chain_position(existing)

    # ---- build receipt --------------------------------------------------- #
    milestone_status = milestone.get("status", "")
    receipt = {
        "schema": "szl.khipu.receipt/v1",
        "organ": "lutar-lean",
        "kind": receipt_kind,
        "milestone_kind": kind,
        "milestone_title": milestone.get("title", kind),
        "milestone_status": milestone_status,
        "chain_index": chain_index,
        "prev_hash": prev_hash,
        "timestamp": _utcnow(),
        "kernel_commit": kernel_commit,
        "kernel_commit_short": snapshot.get("kernel_commit_short", ""),
        "branch": snapshot.get("branch", ""),
        "source_run": {
            "id": str(args.source_run_id),
            "conclusion": "success",
            "workflow": args.source_workflow,
            "url": args.source_run_url,
        },
        "subject": {
            "name": os.path.basename(args.snapshot),
            "sha256": snapshot_sha,
            "snapshot": snapshot,
        },
        "doctrine": snapshot.get("honesty", {}).get("doctrine", "v11"),
        "numbers": {
            "declarations": numbers.get("declarations"),
            "axioms_unique": numbers.get("axioms_unique"),
            "sorries_noncomment": numbers.get("sorries_noncomment"),
        },
        "honesty": snapshot.get("honesty", {}),
        "signing": signing,
    }
    # Backward-compatible aliases for the original Theorem-U receipt shape so any
    # consumer keyed on these keys keeps working for the theorem-u lane.
    if kind == "theorem-u":
        receipt["theorem_u_status"] = milestone_status or "REAL-conditional"
        receipt["lambda_status"] = (
            "Conjecture_1 (OPEN; unconditional uniqueness machine-checked FALSE)")
    receipt["receipt_id"] = canonical_hash(receipt)
    line = json.dumps(receipt, sort_keys=True, ensure_ascii=False)

    # ---- per-theorem anchor manifest (every CI-green theorem) ------------ #
    manifest_rel, manifest_str = build_theorem_manifest(
        snapshot, snapshot_sha, kind, kernel_commit,
        receipt["receipt_id"], chain_index, signing["verify_cmd"])
    vt_count = (snapshot.get("verified_theorems") or {}).get("count", 0)

    # ---- append to HF (canonical) --------------------------------------- #
    hf_content = ("\n".join(json.dumps(r, sort_keys=True, ensure_ascii=False)
                            for r in existing) + ("\n" if existing else "") + line + "\n")
    hf_upload(hf_token, hf_content,
              f"anchor: {kind} snapshot {kernel_commit[:12]} (chain_index {chain_index})")
    print(f"HF appended: kind={kind} chain_index={chain_index} receipt_id={receipt['receipt_id']}")
    if manifest_str is not None:
        hf_upload_file(hf_token, manifest_rel, manifest_str,
                       f"anchor: {kind} verified-theorems manifest "
                       f"{kernel_commit[:12]} ({vt_count} theorems)")
        print(f"HF manifest written: {manifest_rel} ({vt_count} theorems)")

    # ---- append to GitHub front-door (signed commit) -------------------- #
    gh_existing = gh_get_raw(gh_token, GH_NDJSON) or ""
    gh_new = (gh_existing + ("" if gh_existing.endswith("\n") or not gh_existing else "\n")
              + line + "\n")

    # Preserve the EXISTING front-door schema verbatim; ADD only per-kind anchor
    # pointers. Idempotent (set, not increment) so a re-run never double-counts. We
    # deliberately do NOT invent a `szl.lake.index/v1`/khipu_receipt_counts shape
    # here -- that lives in data/lake_index.json and is maintained by the
    # HF->GitHub sync, not us.
    idx_raw = gh_get_raw(gh_token, GH_INDEX)
    index = json.loads(idx_raw) if idx_raw else {
        "canonical_source": f"https://huggingface.co/datasets/{HF_REPO}",
        "doctrine": "v11",
    }
    pointer = {
        "kind": kind,
        "title": milestone.get("title", kind),
        "status": milestone_status,
        "kernel_commit": kernel_commit,
        "kernel_commit_short": snapshot.get("kernel_commit_short", ""),
        "chain_index": chain_index,
        "receipt_id": receipt["receipt_id"],
        "snapshot_sha256": snapshot_sha,
        "verified_run_url": args.source_run_url,
        "doctrine": snapshot.get("honesty", {}).get("doctrine", "v11"),
        "headline_decls": milestone.get("headline_decls", []),
        "signing": {
            "mode": signing["mode"],
            "predicate_type": predicate_type,
            "fulcio_identity": signing["fulcio_identity"],
            "oidc_issuer": signing["oidc_issuer"],
            "rekor_log_index": signing["rekor_log_index"],
        },
        "hf_receipt": f"datasets/{HF_REPO} :: {HF_NDJSON}",
        "github_receipt": GH_NDJSON,
        "anchored_at_utc": _utcnow(),
    }
    # Generic, per-kind pointer map + latest pointer (new, additive).
    anchors = index.get("anchors")
    if not isinstance(anchors, dict):
        anchors = {}
    anchors[kind] = pointer
    index["anchors"] = anchors
    index["latest_anchor"] = pointer
    index["latest_anchored_at_utc"] = pointer["anchored_at_utc"]
    # Legacy Theorem-U pointer: preserve existing keys, refresh only for theorem-u.
    if kind == "theorem-u":
        legacy = index.get("theorem_u_anchor")
        legacy = dict(legacy) if isinstance(legacy, dict) else {}
        legacy.update({
            "kernel_commit": kernel_commit,
            "kernel_commit_short": snapshot.get("kernel_commit_short", ""),
            "chain_index": chain_index,
            "receipt_id": receipt["receipt_id"],
            "snapshot_sha256": snapshot_sha,
            "verified_run_url": args.source_run_url,
            "status": (f"{milestone_status} (Theorem U); "
                       "Conjecture 1 OPEN / machine-checked FALSE"),
            "doctrine": snapshot.get("honesty", {}).get("doctrine", "v11"),
            "headline_decls": milestone.get("headline_decls", []),
            "signing": pointer["signing"],
            "hf_receipt": pointer["hf_receipt"],
            "github_receipt": GH_NDJSON,
        })
        index["theorem_u_anchor"] = legacy
        index["theorem_u_anchored_at_utc"] = pointer["anchored_at_utc"]
    # Per-theorem anchor pointer (additive; set, not increment -> idempotent).
    if manifest_str is not None:
        index["verified_theorems"] = {
            "kind": kind,
            "kernel_commit": kernel_commit,
            "kernel_commit_short": snapshot.get("kernel_commit_short", ""),
            "count": vt_count,
            "chain_index": chain_index,
            "receipt_id": receipt["receipt_id"],
            "snapshot_sha256": snapshot_sha,
            "doctrine": snapshot.get("honesty", {}).get("doctrine", "v11"),
            "source_sha256": (snapshot.get("verified_theorems") or {}).get("source_sha256"),
            "manifest_github": manifest_rel,
            "manifest_hf": f"datasets/{HF_REPO} :: {manifest_rel}",
            "anchored_at_utc": pointer["anchored_at_utc"],
        }
    index_str = json.dumps(index, indent=2, ensure_ascii=False) + "\n"

    additions = [
        {"path": GH_NDJSON, "contents": base64.b64encode(gh_new.encode()).decode()},
        {"path": GH_INDEX, "contents": base64.b64encode(index_str.encode()).decode()},
    ]
    if manifest_str is not None:
        additions.append({"path": manifest_rel,
                          "contents": base64.b64encode(manifest_str.encode()).decode()})

    # ---- bump the verify-anchor-receipts append-only floor (atomic) ------ #
    # The floor lives in szl-lake but the in-CI GITHUB_TOKEN there cannot write
    # main (signed-commits ruleset) and the org blocks Actions from opening PRs.
    # This anchor already writes szl-lake main with the org-owner SZL_LAKE_TOKEN,
    # so we raise the floor to the new chain length in the SAME signed commit that
    # appends the receipt -- there is never a window where the receipt exists but
    # the floor lags. Append-only: bump_baseline_floor never lowers it.
    baseline_raw = gh_get_raw(gh_token, GH_BASELINE)
    baseline_prev = baseline_floor(baseline_raw)
    baseline_str = bump_baseline_floor(baseline_raw, chain_index)
    baseline_bumped = baseline_str is not None
    if baseline_bumped:
        additions.append({"path": GH_BASELINE,
                          "contents": base64.b64encode(baseline_str.encode()).decode()})
        print(f"baseline floor bump: min_receipts {baseline_prev} -> {chain_index}")
    else:
        print(f"::notice::baseline floor already >= chain_index "
              f"({baseline_prev} >= {chain_index}); no bump")
    baseline_now = chain_index if baseline_bumped else baseline_prev

    # Doctrine-preserving one-liner for the team confirmation; per-snapshot status
    # is carried verbatim and NEVER inflated to a blanket "proven".
    if kind == "theorem-u":
        honesty_note = ("Theorem U REAL-conditional; "
                        "Conjecture 1 OPEN / machine-checked FALSE")
    else:
        honesty_note = (f"{kind} status: {milestone_status or 'see per-snapshot honesty block'} "
                        f"(carried verbatim)")

    baseline_msg_line = (f"verify-anchor-receipts floor: min_receipts {baseline_prev} -> {chain_index}\n"
                         if baseline_bumped else
                         f"verify-anchor-receipts floor: min_receipts unchanged ({baseline_prev})\n")
    msg = (f"anchor: {kind} snapshot {kernel_commit[:12]} into szl-lake "
           f"(chain_index {chain_index})\n\n"
           f"Cosign-keyless DSSE receipt for the kernel-verified {kind} snapshot.\n"
           f"Milestone status: {milestone_status or 'n/a'} (per-snapshot honesty carried verbatim).\n"
           f"{baseline_msg_line}"
           f"receipt_id={receipt['receipt_id']}\n"
           f"snapshot_sha256={snapshot_sha}\n\n"
           f"Signed-off-by: {COMMIT_NAME} <{COMMIT_EMAIL}>")
    commit_url = gh_signed_commit(gh_token, additions, msg)
    print(f"GitHub front-door committed: {commit_url}")

    # ---- verify HF chain advanced by exactly one ------------------------ #
    after = hf_read_ndjson(hf_token)
    if len(after) != prev_count + 1:
        raise SystemExit(f"::error::HF chain length {len(after)} != expected {prev_count + 1}")
    last = after[-1]
    if last.get("receipt_id") != receipt["receipt_id"] or last.get("chain_index") != chain_index:
        raise SystemExit("::error::HF tail receipt does not match the anchored receipt")
    print(f"::notice::VERIFIED: HF chain {prev_count} -> {len(after)} "
          f"(chain_index advanced by 1 to {chain_index})")

    # Emit machine-readable summary for the workflow step.
    with open("anchor_result.json", "w", encoding="utf-8") as fh:
        json.dump({
            "kind": kind, "kernel_commit": kernel_commit, "chain_index": chain_index,
            "receipt_id": receipt["receipt_id"], "snapshot_sha256": snapshot_sha,
            "hf_chain_length": len(after), "github_commit": commit_url,
            "fulcio_identity": signing["fulcio_identity"],
            "rekor_log_index": signing["rekor_log_index"],
            "verified_theorems_count": vt_count,
            "verified_theorems_manifest": manifest_rel,
            "milestone_kind": kind,
            "milestone_title": milestone.get("title", kind),
            "milestone_status": milestone_status,
            "doctrine": snapshot.get("honesty", {}).get("doctrine", "v11"),
            "honesty_note": honesty_note,
            "baseline_min_receipts": baseline_now,
            "baseline_bumped": baseline_bumped,
        }, fh, indent=2)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
