/-!
# DenyMonotonic - the hard-deny ABSORBING-STATE core of the Memory Covenant v0.4

Spec 2.1 (szl-frontier docs/COVENANT_V0_4_COUNTERSIGN_SPEC_2026-11-15.md, merged
c1b66ec): the policy lattice must model hard-deny as an ABSORBING state - for
all policy states, if an operation is hard-denied (recon / foreign-write /
weaponize), then NO sequence of approvals lifts the deny.

HONESTY LEDGER (spec 2.2 / 2.3 - proved vs conjecture, never blurred):

  * denyMonotonic below is a PROVED theorem (Lean 4 core only, Mathlib-FREE).
    It machine-checks the POLICY SEMANTICS the software gates implement.

  * Lambda (uniqueness) is NOT required for DenyMonotonic (spec 2.2) and is
    NOT asserted here. Lambda UNCONDITIONAL uniqueness STAYS Conjecture 1
    (machine-checked FALSE). Byzantine BFT safety stays Khipu Conjecture 2.

  * This theorem is NOT the enforcement. The software gates
    (khipu-consensus v0.4 witness countersign + receipt tree + recall gate,
    fail-closed, UNKNOWN never PASS) remain the enforcement (spec 2.3). This
    module machine-checks that the gate semantics they implement cannot be
    lifted by approval pressure.

  * Read-only adjudication (spec 4) inherits this: a RELEASE never lifts a
    hard deny; adjudication is read-only.

EXPERIMENTAL scope: registered under EXPERIMENTAL_SCOPES as Lutar/Covenant/
in .github/scripts/lean_numbers.py - additive, NOT folded into the locked v11
baseline; .github/data/lean_numbers.json is NOT bumped by this pack.
NO sorry; NO new declared axiom; kernel-clean (see the #print axioms ledger at
the end of this file). locked-proven set STAYS EXACTLY 8
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

/-- The policy lattice (spec 2.1): release, softDeny, hardDeny. hardDeny is
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

/-- The absorbing state is strictly below release: no definitional slippage
between hardDeny and release. -/
theorem hardDeny_ne_release :
    Not ((PolicyState.hardDeny : PolicyState) = PolicyState.release) := by
  decide

/-- A hard-denied operation NEVER reaches release, for any approval count. -/
theorem release_ne_of_hardDenied (n : Nat) (c : OpClass)
    (h : gate c = PolicyState.hardDeny) :
    Not (approvals n (gate c) = PolicyState.release) := by
  rw [denyMonotonic_of_hardDenied n c h]
  exact hardDeny_ne_release

/-- Honesty counterweight (spec 2.3 - the lattice is not a wall against the
benign): a benign operation IS released by one approval. Denial pressure is
reserved for the three hard classes; deny-by-default softDeny lifts cleanly. -/
theorem benign_lifts_with_one_approval :
    approvals 1 (gate OpClass.benign) = PolicyState.release := rfl

/- Axiom ledger (kernel-clean receipt; every entry must report a subset of
{propext, Classical.choice, Quot.sound} - expected here: NO axiom dependency). -/
#print axioms denyMonotonic
#print axioms denyMonotonic_of_hardDenied
#print axioms denyMonotonic_seq
#print axioms hardDeny_ne_release
#print axioms release_ne_of_hardDenied
#print axioms benign_lifts_with_one_approval

end Lutar.Covenant
