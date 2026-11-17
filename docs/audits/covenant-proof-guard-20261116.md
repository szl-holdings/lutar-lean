# Covenant proof guard and revision-bound verification

## Scope

Baseline: `lutar-lean@5e8a92917d2d4bfeb371a2372f87a4c7660d996d`.

The DenyMonotonic module proves properties of its abstract policy state
machine. It contains twelve public theorems and is imported by the library
root. Printing six axiom lists was useful diagnostic output, but did not
enforce the claimed empty axiom sets. The canonical number counter excludes
the experimental Covenant scope, while the separate placeholder counter
counts the literal `sorry` token.

This change adds verification of the existing model. It does not change
the policy definitions, theorem statements or proof bodies. It does not
establish a refinement from deployed code to Lean, classify real requests,
authorize an operation, deploy a service, qualify a model, or add a formula
to the locked eight. Lambda remains Conjecture 1.

## Guard

`tools/lean/CovenantGuard.lean` checks the types of all twelve public
theorems and asks `Lean.collectAxioms` for their transitive dependencies.
Every axiom set must be empty. Custom axioms, `sorryAx`, and additional
trust assumptions therefore fail, even when ordinary Lean compilation
would accept a declared assumption.

Seven independent controls inspect the transition definitions directly:
benign operations start in soft denial; the three hard classes start in
hard denial; the approval transition has its intended three cases; one
benign approval releases; zero approvals do not release; a representative
hard-denied sequence does not release; an already released state stays
released. These controls supplement the quantified public theorems.

## Mutation controls

`.github/scripts/check_covenant_guard.py` resolves the compiler selected
by the committed toolchain and checks its reported version. It compiles
disposable copies of the source and guard with a separate module search
path and build directory. No checkout source or shared dependency cache
is edited. The five cases are:

| Case | Required observation |
| --- | --- |
| Clean source | Source and guard exit zero; all twelve axiom records and both completion markers are present |
| Custom axiom in benign release proof | Source compiles; the guard rejects the named custom axiom with nonzero exit |
| `admit` in benign release proof | Source compiles; the guard rejects `sorryAx` with nonzero exit |
| Hard-deny approval changed to release | The original quantified proof fails compilation at the hard-deny transition |
| Benign entry changed directly to release | Public proofs still compile; the guard rejects the changed default state |

A timeout, absent exit code, missing tool, or unrelated error does not count
as a detected mutant. Each invocation retains its native exit and log digest.

## Revision-bound receipt

From a clean committed checkout, run:

```sh
python scripts/verify_covenant.py --repo-path . --output-dir .cache/covenant-verification-new-run
```

The output directory must be new. The wrapper records HEAD, Git tree,
tracked-file status, hashes and committed-blob matches for the proof,
guard, verification scripts, workflow, library root, toolchain and manifest
before and after execution. It records the version commands, mutation
runner exit codes, UTC times and log hashes. Only a complete successful
sequence against unchanged committed inputs receives PASS.

Missing execution evidence produces UNKNOWN and a nonzero wrapper exit.
Dirty source, input mismatch, source drift or a failed command cannot receive
PASS. The receipt and mutation logs are separate artifacts. Generated build
logs may be untracked; all required verification inputs must be tracked and
match HEAD.

The Lake build workflow now invokes this wrapper and uploads the evidence.
Its existing whole-library build, reference-vector check, locked-eight
guard and other gates remain in place. The new receipt explicitly covers
only Covenant source re-elaboration and mutation rejection. It does not
relabel an earlier workstation build log as evidence for a newer revision.

The digest detects content changes; it is not an independent signature.
Source and logs are not replaced by absent-error matching or stale markers.

## Verification

`tests/test_covenant_receipts.py` covers complete success, incomplete
execution, missing exits, nonzero native exits, timeouts, missing final
snapshots, changed revisions, changed input bytes and dirty source.
The canonical declaration/axiom/placeholder baseline is unchanged.
