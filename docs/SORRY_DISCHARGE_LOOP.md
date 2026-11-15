# The Sorry-Discharge Loop — attempt contract and wiring

**Owner directive (2026-11-15):** "wire it all up ... use all math and evolve it
push the frontier then leverage and harness it through our stack and anatomy
and brain." This document is the executable answer of the math core: the loop
that turns this repository's 67 gated open `sorry`s into a self-proving
curriculum for the estate's frontier models, with mechanical verification and a
human PhD gate. No one else has a governed corpus that generates its own
proof-discharge curriculum, verifies attempts against its own pinned kernel,
and ratchets monotonically toward sorry-free.

## The loop, end to end

```
lutar-lean corpus (locked-8 kernel + experimental scope, sorry-gate baseline 67)
  |
  |  tools/export_sorry_challenges.py  (scope identical to count_sorries.py)
  v
SZLHOLDINGS/sorry-discharge-challenges-v1  (machine-readable challenge set)
  |
  |  frontier models attempt discharge (v4 Nemotron lane, brain-navigator
  |  orchestration; an honest ABSTAIN is a valid outcome — measurement-honesty
  |  doctrine applies to proofs exactly as it applies to answers)
  v
candidate proofs -> proposals/ scratch mirror (existing PR #244 pattern)
  |
  |  VERIFICATION (mechanical, fail-closed): rebuild the REAL file on the
  |  pinned toolchain; checks: (1) `lake build` green on the touched module,
  |  (2) axiom count does not increase, (3) sorry count strictly decreases,
  |  (4) no `native_decide`/unsafe escapes introduced.
  v
verified candidate -> receipts (khipu ledger append under the existing
  szl-lake-ledger/lutar-lean lock) -> PhD gate (proposals/ flow, human review)
  |
  |  promotion: corpus PR; sorry-gate baseline ratchets 67 -> 66 -> ... -> 0
  v
discharged proof becomes new SFT material (lean-proofs corpus regen)
  -> trains the NEXT frontier generation -> more discharges. Evolution.
```

## Challenge row contract (exporter output)

Each row of `challenges.jsonl`: `{id, file, decl_kind, decl, header,
block_text, file_imports}`. `block_text` is a comment-stripped excerpt; it is
READING material only. **Verification never uses the excerpt** — an attempt is
verified only against the real file at the manifest's `kernel_head` on the
manifest's `toolchain`.

## Attempt contract (what a model submits)

```json
{
  "challenge_id": "sdc1-<hash>",
  "attempt_kind": "PROOF" | "ABSTAIN",
  "candidate": "<Lean term/tactic block replacing the sorry>",
  "abstain_reason": "<required when attempt_kind=ABSTAIN>",
  "proposer": "<model id + revision + card>",
  "self_reported_confidence": 0.0
}
```

Rules, fail-closed:
1. **ABSTAIN is first-class.** A wrong proof is worse than no proof. The estate
   battery's abstention discipline applies verbatim: a model that never abstains
   is not honest, and a hallucinated `sorry` replacement that does not compile
   is recorded as a failed attempt in the receipt, never silently dropped.
2. **No new axioms.** A discharge that adds an axiom is not a discharge.
3. **No `native_decide`, `decide` on unchecked numerals beyond Mathlib's
   support, `Trust`, or unsafe casts.** The red-test suite (Red_Axiom,
   Red_NativeDecide, Red_Sorry) stays red.
4. **One sorry per attempt** — a candidate may replace only its target's sorry.
5. **Receipts before review.** Every attempt (PROOF or ABSTAIN) appends a
   receipt to the khipu ledger BEFORE PhD review, so the attempt history is
   append-only and auditable.
6. **The sorry-gate is the ratchet.** Promotion PRs must strictly decrease the
   gated count; the scoreboard in SORRIES.md is updated in the same commit.

## Why this is the wiring the estate was missing

- **Math core -> frontier lane:** the challenge set is a ready-made eval +
  curriculum for the Nemotron v4/v5 line training RIGHT NOW (nemo-r8-v4), and
  for lean-proofs-trained successors. It converts "the model knows Lean" into
  "the model moves the scoreboard".
- **Frontier lane -> math core:** discharged proofs (PhD-gated) ratchet the
  corpus toward sorry-free and regenerate SFT data — the corpus evolves with
  the models, and the models evolve with the corpus.
- **Brain:** brain-navigator schedules and budgets attempts (the corpus already
  formalizes its belief update, `Lutar/Innovations/round9/BrainBeliefUpdate.lean`).
- **Anatomy:** every attempt and receipt is a governed artifact like every other
  estate artifact — same ledger, same doctrine, same visibility.
- **Putnam & materials frontier:** the same contract covers the Putnam
  DEMO->REAL campaign and the two Materials-roadmap sorries
  (PDDInjective, PACBayesMaterials) — the highest-value open targets travel
  the same rails.

## Publishing status (honest)

This PR adds the exporter, the contract, and the dataset CARD SOURCE only.
No Hub write happens from this repository (same standing rule as
huggingface/README.md): the first `sorry-discharge-challenges-v1` publication
is an owner-gated dispatch after the exporter output is reviewed. The dataset
card source lives at `huggingface/datasets/sorry-discharge-challenges-v1/README.md`.
