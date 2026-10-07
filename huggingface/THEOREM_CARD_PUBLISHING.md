# Manual theorem-card publication

This is the narrow publisher for the already reviewed configuration repair in
`huggingface/datasets/lean-theorem-tree/README.md`. It has exactly one typed
destination: dataset `SZLHOLDINGS/lean-theorem-tree`. Its sole provider write is
`README.md`. It does not publish `lean-proofs-v1`, data, model weights, receipts,
workflows, licenses, repository settings, or an entire folder. No automatic
workflow is introduced.

## Admission before use

The source, publisher, and tests must first pass the existing protected GitHub
admission path. Refresh native main/reviews/checks/signatures, the canonical
publisher ownership, and the complete Hub baseline immediately before use.
Resolve any competing or uncertain write through its existing owner. Do not
use this manual publisher to bypass an existing publisher or release hold.

The program verifies canonical origin, clean local `main`, exact checkout HEAD,
the immutable source Git blob, the reviewed card hash, and config-only
preservation. It then uses bounded native GitHub REST reads to require current
main equal to that frozen revision, native `protected: true`, a verified-valid
exact-commit signature, and the identical source blob bytes. Ambiguous or
unavailable native source-path-at-revision binding is refused; a locally
supplied blob cannot substitute for the canonical path's actual native blob.
Current main/protection is checked again after that path read. Unavailable
metadata fails closed. Those checks **do not prove effective full
branch-policy satisfaction, required-check acceptance, evaluation, independent
proof, or operator authority**. A protected flag or current-main signature is
not release qualification. The `--authorized` flag is an
explicit operator confirmation of already established authority, not a forged
approval or a substitute for native admission. Run only the source-admitted
publisher from the admitted main checkout; invoking an unadmitted local copy is
not publication authorization.

Use a trusted installed Git executable, version 2.36 or newer. Every local Git
command explicitly disables `core.fsmonitor`; older or unrecognized versions
are refused before checkout reads. Older Git can interpret the boolean `false`
as a hook command rather than disabling the monitor. This control follows
[Git's documented version boundary](https://git-scm.com/docs/git-config#Documentation/git-config.txt-corefsmonitor).
Immutable card bytes are read from Git objects, not from the working-tree card.
The private checkout and its local configuration remain operator-controlled;
this is not a sandbox for an untrusted Git executable or a concurrently mutated
local repository.

The pinned repair card is SHA-256
`80efac6d64d5cef24ef75b14a428d22281923942eb4e38f02b359666e03e775d`.
The unchanged declaration JSON is SHA-256
`85d4a58c08123d7aa26a180b819a3a84e8045c63afe76e4179b21b1056f0cb04`.
Any different source card, data bytes, or concurrent card prose is a review hold,
not a reason to change these pins or use the stale whole-card Hub proposal #2.
Historical Lean counts and proof scope do not change.

## Read-only check, then one authorized write

Use an already-installed, admitted Python/Hub SDK environment. Do not install
dependencies, copy credentials, or buy services merely to run this publisher.
It uses the existing SDK authentication for its intended service and checks
exact-target write permission before a mutation. There is no token CLI argument.

Supply the refreshed immutable Git revision, exact source-card Git blob, and
current Hub parent. Angle-bracket values below are placeholders, not defaults:

```powershell
python -I -B scripts/publish_hf_theorem_card.py --source-sha <admitted-main-sha> --source-blob <exact-card-git-blob> --expected-parent <fresh-hub-main-sha> --state-dir <canonical-private-owner-state>
```

Default checking performs bounded reads and emits a check result to stdout; it
does not authorize publication, write a receipt on GET, or create state files.
After independent native protected-admission/ownership qualification, the same
command with `--publish --authorized` performs at most one SDK commit call with
the expected Hub parent. Native GitHub main/protection/signature/blob reads are
repeated at the write boundary after the possibly lengthy Hub snapshot, then
Hub main is refreshed immediately before the pending journal and CAS commit.
A matching README is a no-op, not a new publication.

## Preserved state and uncertainty

All invocations for this target must use its **same existing canonical private
state directory**. It must not be a symlink/junction, including its ancestry.
The state path must be absolute and lexical; resolving away links or selecting
a relative path is not permitted.
Windows uses native reparse attributes, not a version-dependent junction helper;
an unavailable capability fails closed. All Windows reparse points are denied.
Keep this directory outside tracked/public content. A different directory does
not revoke the existing owner or make an uncertain write retryable.

This lock is **filesystem-scoped**, not a distributed lock, global provider
lease, or signed publication receipt. The operator must use one preassigned
canonical owner state and ensure no competing publisher owns the same target.
The private state and its ancestry must also remain under that owner's control
during the operation; the initial link/reparse checks do not establish safety
against another local actor concurrently replacing directories.
Never select a new state path to bypass retained evidence. Publication eligibility
remains unestablished until protected admission, native checks, explicit existing
authority, and provider readback qualify this exact source and attempt.

The writer exclusively creates `lean-theorem-tree.writer.lock`. It persists and
flushes `lean-theorem-tree.publication.json` before calling the provider. Journal
updates are staged, flushed, and atomically replaced; pending evidence is never
truncated. Both locks and journals are owner-bound. There is no stale-lock
expiry, auto-reset, delete/retry command, or uncertainty replay path.

Any provider-call, native-revision, or readback exception after the pending fence
leaves the journal `UNKNOWN` (or the original `PENDING` if journaling also failed)
and retains the writer lock. The provider may already have accepted the write.
Exception messages/credentials are not copied into the journal. An existing
journal of any status, even malformed or already verified, prevents replay.
Owner reconciliation must inspect the exact native parent/commit/complete maps
and retain the old evidence; do not delete it or invent a new state directory.
The offline harness qualifies caught process-error fencing, not power-loss,
forced-reboot, or crash recovery. Files are flushed with `fsync`, but parent
directories are not flushed; persistence of directory entries and atomic
replacements across a power loss remains **UNKNOWN**. This is not an
independently certified storage system. After any such interruption the existing
owner must reconcile native provider state and retained evidence before another
attempt; never infer absence of a write from a missing local file alone.

The provider tree is fully consumed, bounded to 128 files, 256 KiB per ordinary
Git blob, and 2 MiB in total. LFS/Xet-backed content is outside this narrow lane.
Each downloaded raw file must match its declared size and native Git blob;
cross-origin redirects are refused before forwarding authentication. All before
and immutable after files are SHA-256 hashed. Successful readback requires the
same complete file set and byte-identical non-README files, the exact candidate
README, and current main equal to the returned native commit. A managed receipt
is preserved but is not ingested as declaration data.

## Verification boundary

```powershell
python -I -B -m unittest discover -s tests -p 'test_hf_theorem_card_publication.py' -v
python -I -B -m unittest discover -s tests -p 'test_hf_theorem_dataset_config.py' -v
```

The new publication harness uses explicit synthetic fixtures and a fake provider
to exercise fail-closed, immutable-byte, CAS, sole-writer, and once-only behavior.
It patches fixture hashes only inside tests; no production pin is relaxed. Those
tests are not provider authorization, hosted execution, or scientific proof.
Run the existing real-card preservation tests separately. After native
publication, independently refresh the Hub revision/configuration, replay the
269 unchanged declarations in streaming and non-streaming modes, and inspect
the real dataset viewer before closing issue #310. The publisher deliberately
reports `viewer_verified: false` and never claims whole-estate completion.
