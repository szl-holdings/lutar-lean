# Conjecture Factory — provenance & disclosure policy

The Conjecture Factory is a new-math-problem pipeline: it generates a candidate
conjecture, screens it for novelty, **cryptographically timestamps** it into the
signed DSSE Khipu `szl-lake` ledger, grades its difficulty by a **real** bounded
solver run, and releases it in ordered stages.

This document is the authoritative description of *what each receipt means* and
*what it does not mean*. It is written to the honesty doctrine **v11**: a
generated conjecture is **OPEN** until a solution is independently verified. The
pipeline never fabricates a signature, a novelty score, or a difficulty grade.

## What a disclosure attests — and what it does not

A Conjecture Factory disclosure is a cryptographic timestamp over the conjecture's
canonical statement, its novelty screen, and its difficulty grade at a point in
time. The cosign keyless signature attests the **timestamp and the content** — it
is **not** evidence that the conjecture is true, original, or hard. In particular:

- A disclosure receipt does **not** make the conjecture a theorem. It stays OPEN.
- A `novel-candidate` verdict is an advisory screen, not a proof of originality.
- An `OPEN` grade means *searched-to-budget with no counterexample found* — never
  a proof of truth.

## Pipeline stages

| Step | Script | Output schema |
|------|--------|---------------|
| 1. Intake | `conjecture_intake.py` | `szl.conjecture.candidate/v1` |
| 2. Novelty screen | `conjecture_novelty.py` | `szl.conjecture.novelty/v1` |
| 3. Difficulty grade | `conjecture_grader.py` | `szl.conjecture.grade/v1` |
| 4. Disclosure snapshot | `build_conjecture_snapshot.py` | `szl.conjecture.disclosure/v1` |
| 5. Anchor (sign + ledger) | `anchor_szl_lake.py` (generic) | `szl.khipu.receipt/v1` |
| 6. Staged release gate | `conjecture_release.py` | `szl.conjecture.release/v1` |

Every script is standard-library-only and ships an offline `--self-test`.

### 1. Intake — canonical identity

The candidate is normalised to `szl.conjecture.candidate/v1`. The statement is
canonicalised (whitespace-collapsed) and hashed with SHA-256; the candidate id is
`cf-<sha256(canonical_statement)[:12]>`, so the **same statement always yields the
same id**. The taxonomy is forced to `OPEN`; any attempt to declare a candidate
`PROVEN` / `REAL` / `VERIFIED` is rejected at intake.

### 2. Novelty screen — honest prior-art labels

Novelty is screened by character 5-gram **shingle Jaccard** similarity against a
local corpus of known problems (`conjectures/corpus/`). An optional `--online`
pass queries arXiv and Crossref. Every external source carries an explicit
**live / cached / unreachable** label; an unreachable source **never** counts as
confirmation of novelty. Verdicts are `possible-duplicate`, `novel-candidate`, or
`inconclusive` (e.g. an empty corpus while offline yields `inconclusive`, never a
false `novel-candidate`).

### 3. Difficulty grade — a real solver run

Grading runs a **real** bounded ensemble (exhaustive + random sampler) over the
candidate's executable predicate, which exposes `domain()`, `holds(x)`, a `FINITE`
flag, and an optional `sample(rng)`. Verdicts:

- **REFUTED** — a concrete counterexample (witness) was found. Reproducible.
- **VERIFIED-FINITE** — the finite domain was exhausted with no counterexample.
  This certifies **only** the enumerated finite domain, not the conjecture in
  general.
- **OPEN** — the search budget was spent with no counterexample. Not a proof.
- **UNREACHABLE** — no executable predicate, so no grade could be computed.
  Reported honestly; it is **not** evidence the conjecture is true or hard.

Predicate soundness contract: `holds(x)` returns `False` only with certain
evidence of a violation; inconclusive bounded runs assert no counterexample. The
grader therefore can never fabricate a witness.

### 4. Disclosure snapshot

`build_conjecture_snapshot.py` assembles `szl.conjecture.disclosure/v1`
(`kind = conjecture-disclosure`): `milestone.status = OPEN`,
`milestone.kernel_only = false`, the per-snapshot `honesty` block carries
`doctrine = v11`, and the intake, novelty, and grade records are embedded. A
conjecture is **not** a kernel build, so the snapshot deliberately carries **no**
`lean_numbers`. The builder refuses to assemble a `solution`-stage disclosure for
a candidate that was not actually resolved.

### 5. Anchor — signed Khipu ledger record

Anchoring reuses the **generic** `anchor_szl_lake.py` and the **same** cosign
keyless OIDC mechanism already used for proof-milestone anchors — **no new signing
key is introduced and no signing happens off-CI**. The snapshot is signed with
`cosign attest-blob` (DSSE in-toto, predicate type
`https://szl-holdings/conjecture-disclosure/v1`), verified in-CI, then appended as
an `szl.khipu.receipt/v1` record (`kind = conjecture-disclosure-anchor`) to both
ledger surfaces (the Hugging Face NDJSON canonical chain and the GitHub
front-door index). Each receipt advances `chain_index` by one, links to the
previous receipt's id, and embeds the full snapshot. Anchoring is **idempotent**:
re-anchoring the same snapshot at the same commit is a no-op.

Because a conjecture disclosure is explicitly **not** kernel-only, the conjecture
workflow does **not** apply the Theorem-U kernel-only gate.

#### Disclosure-ledger record format

```
{
  "schema": "szl.khipu.receipt/v1",
  "organ": "lutar-lean",
  "kind": "conjecture-disclosure-anchor",
  "milestone_kind": "conjecture-disclosure",
  "milestone_title": "<conjecture title>",
  "milestone_status": "OPEN",
  "chain_index": <n>,
  "prev_hash": "<previous receipt_id or null>",
  "timestamp": "<UTC>",
  "subject": { "name": "...", "sha256": "...", "snapshot": { ... } },
  "honesty": { "doctrine": "v11", ... },
  "signing": { "predicate_type": "...", "bundle_b64": "...", "verify_cmd": "..." },
  "receipt_id": "<canonical hash of the receipt>"
}
```

Each receipt is **self-verifiable**: the embedded `signing.bundle_b64` can be
checked with the recorded `cosign verify-blob-attestation` command.

### 6. Staged release

Disclosure is released in ordered stages, gated on the ledger as the single
source of truth (`conjecture_release.py`):

- **teaser** — title + statement hash only; always permitted (it commits to no
  gated content).
- **statement** — the full problem statement; permitted **only** once a
  disclosure receipt for this candidate exists in `szl-lake`, i.e. the statement
  has been cryptographically timestamped. This is what prevents a
  "publish-first-timestamp-later" priority dispute.
- **solution** — the worked solution; permitted **only** when the candidate has
  been genuinely resolved (grade `REFUTED` or `VERIFIED-FINITE`, or an
  externally-verified proof). An `OPEN` conjecture can never reach this stage —
  doctrine v11 forbids presenting an open problem as solved. Stages cannot be
  skipped.

## Honesty summary

- Generated conjectures are **OPEN** until independently verified.
- Signatures attest **timestamp + content**, never truth.
- Novelty and difficulty are advisory, computed by real screens/runs; external
  prior-art sources are labelled live / cached / unreachable.
- No signature, score, or grade is ever fabricated; no off-CI signing; no new key.
