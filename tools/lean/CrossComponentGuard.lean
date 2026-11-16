import Lean
import Lutar.Doctrine.CrossComponentInvariant

/-
Semantic regression gate for the composite formal specification.
This file is outside Lutar/ and does not change the locked-eight inventory.
It does not establish deployed runtime refinement or empirical model quality.
-/
namespace CrossComponentGuard
open Lutar.Doctrine Lutar.HUKLLA Lutar.OVERWATCH Lutar.DPI

theorem allow_iff (t : ExecutionTrace) (m : OverwatchMode) (op : Operation)
    (r : Receipt) (cap : Nat) :
    governanceAllow t m op r cap = true ↔
      isHaltEligible t = true ∧ m.allow op ∧ dpiAdmit r cap = true := by
  classical
  simp [governanceAllow, Bool.and_eq_true, and_assoc]

theorem rejects_unallowed (t : ExecutionTrace) (m : OverwatchMode) (op : Operation)
    (r : Receipt) (cap : Nat) (h : ¬ m.allow op) :
    governanceAllow t m op r cap = false := by
  simp [governanceAllow, h]

theorem rejects_write (t : ExecutionTrace) (r : Receipt) (cap : Nat)
    (path data : String) :
    governanceAllow t readOnlyMode (.write path data) r cap = false :=
  rejects_unallowed t readOnlyMode _ r cap (overwatch_rejects_write path data)

theorem rejects_exec (t : ExecutionTrace) (r : Receipt) (cap : Nat) (cmd : String) :
    governanceAllow t readOnlyMode (.exec cmd) r cap = false :=
  rejects_unallowed t readOnlyMode _ r cap (overwatch_rejects_exec cmd)

theorem allowed_operation_is_read_only (t : ExecutionTrace) (m : OverwatchMode)
    (op : Operation) (r : Receipt) (cap : Nat)
    (h : governanceAllow t m op r cap = true) : isWriteOperation op = false :=
  m.no_writes op ((allow_iff t m op r cap).mp h).2.1

/-- Tightening an operation policy cannot create a newly allowed operation. -/
theorem policy_refinement (t : ExecutionTrace) (strict broad : OverwatchMode)
    (op : Operation) (r : Receipt) (cap : Nat)
    (refines : ∀ x, strict.allow x → broad.allow x)
    (h : governanceAllow t strict op r cap = true) :
    governanceAllow t broad op r cap = true := by
  obtain ⟨ht, hm, hr⟩ := (allow_iff t strict op r cap).mp h
  exact (allow_iff t broad op r cap).mpr ⟨ht, refines op hm, hr⟩

/-- A refusal under a broader policy remains a refusal under a stricter one. -/
theorem denial_preserved_by_refinement (t : ExecutionTrace)
    (strict broad : OverwatchMode) (op : Operation) (r : Receipt) (cap : Nat)
    (refines : ∀ x, strict.allow x → broad.allow x)
    (h : governanceAllow t broad op r cap = false) :
    governanceAllow t strict op r cap = false := by
  cases hs : governanceAllow t strict op r cap with
  | false => rfl
  | true =>
    have hb := policy_refinement t strict broad op r cap refines hs
    simp [h] at hb

theorem rejects_ineligible (t : ExecutionTrace) (m : OverwatchMode) (op : Operation)
    (r : Receipt) (cap : Nat) (h : isHaltEligible t = false) :
    governanceAllow t m op r cap = false := by
  simp [governanceAllow, h]

theorem rejects_over_capacity (t : ExecutionTrace) (m : OverwatchMode) (op : Operation)
    (r : Receipt) (cap : Nat) (h : dpiAdmit r cap = false) :
    governanceAllow t m op r cap = false := by
  simp [governanceAllow, h]

def eligible : ExecutionTrace := ⟨1, true, true⟩
def oneByte : Receipt := ⟨1, by decide⟩

theorem positive_read_control :
    governanceAllow eligible readOnlyMode (.read "fixture") oneByte 8 = true := by
  apply doctrine_cross_invariant
  · norm_num [eligible, isHaltEligible, LAMBDA_FLOOR]
  · exact overwatch_read_admitted "fixture"
  · decide

theorem concrete_write_regression :
    governanceAllow eligible readOnlyMode (.write "fixture" "data") oneByte 8 = false :=
  rejects_write _ _ _ _ _

theorem concrete_exec_regression :
    governanceAllow eligible readOnlyMode (.exec "fixture") oneByte 8 = false :=
  rejects_exec _ _ _ _

open Lean Elab Command
run_cmd do
  let trust := [``propext, ``Classical.choice, ``Quot.sound]
  let names := [``allow_iff, ``rejects_unallowed, ``rejects_write, ``rejects_exec,
    ``allowed_operation_is_read_only, ``policy_refinement,
    ``denial_preserved_by_refinement, ``rejects_ineligible, ``rejects_over_capacity,
    ``positive_read_control, ``concrete_write_regression, ``concrete_exec_regression]
  for name in names do
    let axioms ← collectAxioms name
    let allowed := axioms.toList.all fun a => trust.contains a
    unless allowed do
      throwError "CROSS_COMPONENT_AXIOM_GATE: {name}: {axioms}"
    logInfo m!"CROSS_COMPONENT_GUARD {name}: {axioms}"
  logInfo "CROSS_COMPONENT_GUARD_OK 12"
end CrossComponentGuard
