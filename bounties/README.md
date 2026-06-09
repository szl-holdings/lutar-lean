<!-- SPDX-License-Identifier: Apache-2.0 -->

# Open-Problem Bounty Board

Machine-readable bounties for the **genuinely OPEN** problems in this kernel. One
YAML file per bounty. Each entry is an honest open problem under public axiom audit —
nothing already proved is listed here, and no OPEN item is described as proved.

| Bounty | Status | Intake |
|--------|:------:|--------|
| [`conjecture-1-lambda-uniqueness`](./conjecture-1-lambda-uniqueness.yaml) — Λ unconditional uniqueness (Conjecture 1, NOT a theorem) | **OPEN** | [`szl-holdings/lambda-bounty`](https://github.com/szl-holdings/lambda-bounty) |
| [`conjecture-2-khipu-bft-safety`](./conjecture-2-khipu-bft-safety.yaml) — Khipu Byzantine quorum safety (Conjecture 2) | **OPEN** | [`szl-holdings/lutar-lean`](https://github.com/szl-holdings/lutar-lean) |

How to claim, the verification bar, and the merge flow are in
[`docs/bounties.md`](../docs/bounties.md). The YAML schema is validated in CI by
[`scripts/check_bounties.py`](../scripts/check_bounties.py)
(workflow: `.github/workflows/bounties.yml`).

*Doctrine v11. A bounty clears only when the kernel verifies the proof (REAL):
kernel-checked, zero `sorry`, in-policy axioms.*
