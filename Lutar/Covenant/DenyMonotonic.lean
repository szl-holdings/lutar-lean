/-!
# DenyMonotonic - the hard-deny ABSORBING-STATE core of the Memory Covenant v0.4

Spec 2.1 (szl-frontier docs/COVENANT_V0_4_COUNTERSIGN_SPEC_2026-11-15.md, merged
c1b66ec): this abstract policy state machine models hard-deny as an ABSORBING
state. For every starting hard-deny state, no finite sequence of the defined
approveStep transition reaches release. The operation classes are model inputs;
this module does not classify real-world requests.

HONESTY LEDGER (spec 2.2 / 2.3 - proved vs conjecture, never blurred):

  * denyMonotonic below is a PROVED theorem (Lean 4 core only, Mathlib-FREE).
    It verifies the abstract transitions defined in this module.

  * Lambda (uniqueness) is NOT required for DenyMonotonic (spec 2.2) and is
    NOT asserted here. Lambda UNCONDITIONAL uniqueness STAYS Conjecture 1
    (machine-checked FALSE). Byzantine BFT safety stays Khipu Conjecture 2.

  * Software gates remain the enforcement (spec 2.3). No refinement proof
    connects deployed gate code, witness verification or request classification
    to this model. Runtime correspondence requires separate evidence.

  * Read-only adjudication is a separate runtime contract. No deployment,
    authorization or adjudication guarantee follows solely from this module.

EXPERIMENTAL scope: registered under EXPERIMENTAL_SCOPES as Lutar/Covenant/
in .github/scripts/lean_numbers.py - additive, NOT folded into the locked v11
baseline; .github/data/lean_numbers.json is NOT bumped by this pack.
NO proof placeholder; NO new declared axiom. tools/lean/CovenantGuard.lean
checks all twelve theorem types and rejects every nonempty transitive axiom
set. The #print axioms ledger below is supplementary output, not the gate.
The locked-proven set STAYS EXACTLY 8
{F1, F4, F7, F11, F12, F18, F19, F22}.
-/

namespace Lutar.Covenant

/-- Operation classes of the covenant policy core (spec 2.1). The three
hard-deny classes are recon, foreignWrite, weaponize; everything else is
benign. -/
inductive OpClass
  | benign
  | recon
  | foreignWrite
  | weaponize
  deriving DecidableEq, Repr

/-- The policy states (spec 2.1): release, softDeny, hardDeny. hardDeny is
the ABSORBING state; approvals may lift softDeny to release but can NEVER
move hardDeny. -/
inductive PolicyState
  | release
  | softDeny
  | hardDeny
  deriving DecidableEq, Repr

/-- The gate: entry policy state of each operation class. The three covenant
hard-deny classes enter at hardDeny; everything else enters at softDeny
(deny-by-default: an approval can still lift it, and benign does lift). -/
def gate : OpClass -> PolicyState
  | .benign => .softDeny
  | .recon => .hardDeny
  | .foreignWrite => .hardDeny
  | .weaponize => .hardDeny

/-- One approval step: lifts softDeny to release, keeps release, and NEVER
lifts hardDeny (the absorbing case). -/
def approveStep : PolicyState -> PolicyState
  | .release => .release
  | .softDeny => .release
  | .hardDeny => .hardDeny

/-- approvals n s: the state after a sequence of n approval steps. -/
def approvals : Nat -> PolicyState -> PolicyState
  | 0, s => s
  | n + 1, s => approvals n (approveStep s)

/-- **DenyMonotonic (spec 2.1 absorbing-state core).** For every policy state
and every number of approval steps, a hard deny stays a hard deny: NO
sequence of approvals lifts the hard deny. -/
theorem denyMonotonic (n : Nat) (s : PolicyState) (h : s = PolicyState.hardDeny) :
    approvals n s = PolicyState.hardDeny := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih => exact ih (approveStep s) (by subst h; rfl)

/-- Spec 2.1 in the gate's own terms: an operation hard-denied AT THE GATE is
never released by any sequence of approvals. -/
theorem denyMonotonic_of_hardDenied (n : Nat) (c : OpClass)
    (h : gate c = PolicyState.hardDeny) :
    approvals n (gate c) = PolicyState.hardDeny :=
  denyMonotonic n (gate c) h

theorem denyMonotonic_recon (n : Nat) :
    approvals n (gate OpClass.recon) = PolicyState.hardDeny :=
  denyMonotonic_of_hardDenied n _ rfl

theorem denyMonotonic_foreignWrite (n : Nat) :
    approvals n (gate OpClass.foreignWrite) = PolicyState.hardDeny :=
  denyMonotonic_of_hardDenied n _ rfl

theorem denyMonotonic_weaponize (n : Nat) :
    approvals n (gate OpClass.weaponize) = PolicyState.hardDeny :=
  denyMonotonic_of_hardDenied n _ rfl

/-- Sequence fidelity: a LIST of approval steps (one per element), folded
left. Same absorbing guarantee as approvals. -/
def approveSeq (as : List Nat) (s : PolicyState) : PolicyState :=
  as.foldl (fun acc _ => approveStep acc) s

theorem denyMonotonic_seq (as : List Nat) (s : PolicyState)
    (h : s = PolicyState.hardDeny) :
    approveSeq as s = PolicyState.hardDeny := by
  induction as generalizing s with
  | nil => exact h
  | cons a as ih => exact ih (approveStep s) (by subst h; rfl)

theorem denyMonotonic_seq_recon (as : List Nat) :
    approveSeq as (gate OpClass.recon) = PolicyState.hardDeny :=
  denyMonotonic_seq as _ rfl

theorem denyMonotonic_seq_foreignWrite (as : List Nat) :
    approveSeq as (gate OpClass.foreignWrite) = PolicyState.hardDeny :=
  denyMonotonic_seq as _ rfl

theorem denyMonotonic_seq_weaponize (as : List Nat) :
    approveSeq as (gate OpClass.weaponize) = PolicyState.hardDeny :=
  denyMonotonic_seq as _ rfl

/-- The constructors hardDeny and release are distinct. No order or lattice
structure is defined or claimed here. -/
theorem hardDeny_ne_release :
    Not ((PolicyState.hardDeny : PolicyState) = PolicyState.release) := by
  decide

/-- A hard-denied operation NEVER reaches release, for any approval count. -/
theorem release_ne_of_hardDenied (n : Nat) (c : OpClass)
    (h : gate c = PolicyState.hardDeny) :
    Not (approvals n (gate c) = PolicyState.release) := by
  rw [denyMonotonic_of_hardDenied n c h]
  exact hardDeny_ne_release

/-- Positive control (spec 2.3 - the state machine is not a wall against the
benign): a benign operation IS released by one approval. Denial pressure is
reserved for the three hard classes; deny-by-default softDeny lifts cleanly. -/
theorem benign_lifts_with_one_approval :
    approvals 1 (gate OpClass.benign) = PolicyState.release := rfl

/- Supplementary axiom output. CovenantGuard enforces empty axiom sets for
all twelve public theorems; printing an axiom set alone is not a check. -/
#print axioms denyMonotonic
#print axioms denyMonotonic_of_hardDenied
#print axioms denyMonotonic_seq
#print axioms hardDeny_ne_release
#print axioms release_ne_of_hardDenied
#print axioms benign_lifts_with_one_approval

end Lutar.Covenant
