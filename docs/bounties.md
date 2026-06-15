<!-- SPDX-License-Identifier: Apache-2.0 -->

# Bounties — claim, verify, merge

This kernel publishes its **genuinely OPEN** problems as a machine-readable bounty
board under [`bounties/`](../bounties/), one YAML file per problem. The board is the
actionable companion to the honest OPEN list in
[`README.md`](../README.md) and [`BOUNTY.md`](../BOUNTY.md): the honesty doctrine
keeps OPEN problems clearly *un-proved*, and this doc explains how an external
contributor turns one into a verified result.

**Doctrine v11.** A bounty is an OPEN problem. An OPEN conjecture is never
represented as proved. A submission only counts when the kernel verifies it (REAL):
kernel-checked, zero `sorry`, in-policy axioms.

## The current board

| Bounty | What is OPEN |
|--------|--------------|
| [`conjecture-1-lambda-uniqueness`](../bounties/conjecture-1-lambda-uniqueness.yaml) | Λ **unconditional** uniqueness — **Conjecture 1**, NOT a theorem. The conditional CUT-2 result is already proven; the unconditional gap (missing bisymmetry / continuity assumption — the candidate **A6 bisymmetry** strengthening) is open. Unconditional uniqueness under the bare axioms is machine-checked **FALSE** (the `min`/`maxAgg` counterexample). |
| [`conjecture-2-khipu-bft-safety`](../bounties/conjecture-2-khipu-bft-safety.yaml) | Khipu Byzantine quorum safety — **Conjecture 2**. The conditional (honest-non-equivocation) form is proven; the unconditional obligation `ubuntu_quorum_safety` is open. |

Nothing already proved is listed. The conditional/locked results (the 8 LOCKED
formulas, the CUT-2 conditional Λ result, the Wave 23 conditional BFT result) are
**not** bounties — see [`PROVEN_FORMULAS.md`](../PROVEN_FORMULAS.md).

## How to claim a bounty

There is no "reservation" step — bounties are won by a verifying proof, not by
calling dibs. To work on one:

1. **Read the bounty YAML.** It pins the exact target theorem, its file and repo,
   the acceptance criteria, and where the submission goes (`submission.intake_repo`).
2. **Announce intake (optional).** For the Λ bounty you may `POST` your submission
   metadata to the live intake webhook in the bounty YAML. You get a hash-chained
   **Khipu intake receipt**. This acknowledges *intake only* — it does not decide
   eligibility.
3. **Open a pull request** to the bounty's `intake_repo` that discharges the target
   `sorry`. The submission template lives in the intake repo
   (`submissions/SUBMISSION_TEMPLATE.md` for `lambda-bounty`).

## The verification bar (must become REAL)

A submission is judged **only** by CI — the sole, automated, no-bypass arbiter named
in each YAML's `verification.arbiter`. It must satisfy every item in the YAML's
`acceptance_criteria`, which always include:

1. **Builds.** `lake build` is green on the pinned Lean + Mathlib toolchain.
2. **Zero `sorry`.** No `sorry` / `sorryAx` anywhere in the target and its
   dependencies.
3. **In-policy axioms only.** `#print axioms <target>` is a subset of the allowlist
   `[propext, Quot.sound, Classical.choice]`.
4. **No new trust.** No new `axiom` declarations and no `native_decide` escape
   hatches; the numbers-drift gate stays green.

Only when all of these pass does the OPEN problem **become REAL** — i.e. a
kernel-checked result. Until then it stays an OPEN conjecture and the proof gate
stays red. For Conjecture 1, that red `verify-proof` state on `lambda-bounty` `main`
is the deliberate public signal that the conjecture is still open.

## The merge process

1. **CI runs automatically** on the PR. A red gate means the bounty is not met —
   feedback is the CI log itself.
2. **CI green ⇒ eligible.** A maintainer (`CODEOWNERS`) reviews for scope and
   honesty: that the discharged statement is the published target, that any added
   structural hypothesis (e.g. bisymmetry / continuity) is a stated theorem premise
   rather than a smuggled global axiom, and that no claim overstates what was proved.
3. **Merge + promote.** On merge, the result is promoted out of the OPEN list: the
   bounty YAML `status` flips from `OPEN` to `AWARDED`, the relevant README/STATUS
   rows are updated, and the new kernel-checked result is recorded in
   `PROVEN_FORMULAS.md`. The founder-set reward is paid as published in the bounty
   repo's pinned issue.

## Honesty rules for the board

- Every bounty is OPEN until the kernel verifies the proof. Do not describe an OPEN
  conjecture as proved.
- Λ unconditional uniqueness is **Conjecture 1**, never a theorem; Khipu
  unconditional BFT safety is **Conjecture 2**.
- The board never invents a monetary figure — `reward.amount` is `founder-set` and
  the real number is published by the founder in the bounty repo.
- Adding a bounty = adding a YAML under `bounties/` that passes
  [`scripts/check_bounties.py`](../scripts/check_bounties.py) in CI.

*Co-Authored-By: Forge (SZL agent) · Doctrine v11.*
