import Lean
import Lutar.Covenant.DenyMonotonic

/-!
Fail-closed checks for the abstract Covenant policy state machine.
All twelve published theorems must retain their types and empty axiom sets.
These checks do not establish correspondence with a deployed runtime.
-/
namespace CovenantGuard
open Lutar.Covenant

-- Typed contracts reject weakening a published statement to a trivial truth.
example (n : Nat) (s : PolicyState) (h : s = .hardDeny) :
    approvals n s = .hardDeny := denyMonotonic n s h
example (n : Nat) (c : OpClass) (h : gate c = .hardDeny) :
    approvals n (gate c) = .hardDeny := denyMonotonic_of_hardDenied n c h
example (n : Nat) : approvals n (gate .recon) = .hardDeny :=
  denyMonotonic_recon n
example (n : Nat) : approvals n (gate .foreignWrite) = .hardDeny :=
  denyMonotonic_foreignWrite n
example (n : Nat) : approvals n (gate .weaponize) = .hardDeny :=
  denyMonotonic_weaponize n
example (as : List Nat) (s : PolicyState) (h : s = .hardDeny) :
    approveSeq as s = .hardDeny := denyMonotonic_seq as s h
example (as : List Nat) : approveSeq as (gate .recon) = .hardDeny :=
  denyMonotonic_seq_recon as
example (as : List Nat) : approveSeq as (gate .foreignWrite) = .hardDeny :=
  denyMonotonic_seq_foreignWrite as
example (as : List Nat) : approveSeq as (gate .weaponize) = .hardDeny :=
  denyMonotonic_seq_weaponize as
example : (PolicyState.hardDeny : PolicyState) ≠ .release := hardDeny_ne_release
example (n : Nat) (c : OpClass) (h : gate c = .hardDeny) :
    approvals n (gate c) ≠ .release := release_ne_of_hardDenied n c h
example : approvals 1 (gate .benign) = .release := benign_lifts_with_one_approval

-- Independent positive and negative controls inspect the definitions directly.
theorem benign_starts_denied : gate .benign = .softDeny := rfl
theorem hard_classes_start_denied :
    [gate .recon, gate .foreignWrite, gate .weaponize] =
      [.hardDeny, .hardDeny, .hardDeny] := rfl
theorem approval_transition_control :
    [approveStep .release, approveStep .softDeny, approveStep .hardDeny] =
      [.release, .release, .hardDeny] := rfl
theorem benign_release_control : approvals 1 (gate .benign) = .release := rfl
theorem zero_approval_control : approvals 0 (gate .benign) = .softDeny := rfl
theorem hard_sequence_control :
    approveSeq [0, 1, 42] (gate .recon) ≠ .release := by decide
theorem released_sequence_control :
    approveSeq [0, 1, 42] .release = .release := rfl

open Lean Elab Command
run_cmd do
  let names := [
    ``Lutar.Covenant.denyMonotonic,
    ``Lutar.Covenant.denyMonotonic_of_hardDenied,
    ``Lutar.Covenant.denyMonotonic_recon,
    ``Lutar.Covenant.denyMonotonic_foreignWrite,
    ``Lutar.Covenant.denyMonotonic_weaponize,
    ``Lutar.Covenant.denyMonotonic_seq,
    ``Lutar.Covenant.denyMonotonic_seq_recon,
    ``Lutar.Covenant.denyMonotonic_seq_foreignWrite,
    ``Lutar.Covenant.denyMonotonic_seq_weaponize,
    ``Lutar.Covenant.hardDeny_ne_release,
    ``Lutar.Covenant.release_ne_of_hardDenied,
    ``Lutar.Covenant.benign_lifts_with_one_approval]
  unless names.length == 12 do
    throwError "COVENANT_GUARD: expected twelve public theorem declarations"
  for name in names do
    let axioms ← collectAxioms name
    unless axioms.isEmpty do
      throwError "COVENANT_AXIOM_GATE {name}: expected no axioms, got {axioms}"
    logInfo m!"COVENANT_AXIOMS {name} 0"
  let controls := [
    ``benign_starts_denied, ``hard_classes_start_denied,
    ``approval_transition_control, ``benign_release_control,
    ``zero_approval_control, ``hard_sequence_control,
    ``released_sequence_control]
  for name in controls do
    let axioms ← collectAxioms name
    unless axioms.isEmpty do
      throwError "COVENANT_CONTROL_AXIOM_GATE {name}: {axioms}"
  logInfo "COVENANT_CONTROLS_OK 7"
  logInfo "COVENANT_GUARD_OK 12"
end CovenantGuard
