/-
  Showcase.Frontier.CredoVerdictWitness
  =====================================
  EXPERIMENTAL. Mathlib-free. Sorry-free. No declared axiom.
  Compiles against leanprover/lean4:v4.18.0 core.

  AUTHOR NOTE (Doctrine v11):
    This is the discrete witness for the Credo Agent Governor → SZL map.
    Credo resolves harness events to allow | block | escalate | advise.
    SZL admits execution only on ALLOW. ADVISE is never authority.
    A hard DENY cannot be lifted by a later allow, escalate, or advise.

    This file says NOTHING about Λ uniqueness. Conjecture 1 stays OPEN.
    Locked-proven set stays EXACTLY 8. Lives OUTSIDE Lutar/ so
    lean_numbers.py does not count it.

  What is proved here (discrete shadows, not Credo's product):
    C1  advise never authorizes execution
    C2  a later allow cannot lift deny
    C3  escalate without a human principal does not execute
    C4  missing evidence does not authorize
    C5  a Λ-floor miss does not authorize (advisory gate, not a theorem of uniqueness)
-/
namespace Showcase.Frontier.CredoVerdictWitness

/-- Credo's four published harness outcomes. -/
inductive Credo where
  | allow
  | block
  | escalate
  | advise
deriving DecidableEq, Repr

/-- SZL decisions. ADVISE is recorded and is never an admission ticket. -/
inductive Szl where
  | ALLOW
  | DENY
  | REVIEW
  | ADVISE
deriving DecidableEq, Repr

/-- Execution is a boolean the kernel can check. Only ALLOW is true. -/
def mayExecute : Szl → Bool
  | .ALLOW => true
  | .DENY => false
  | .REVIEW => false
  | .ADVISE => false

/-- C1 raw: ADVISE cannot authorize. -/
theorem advise_never_executes : mayExecute .ADVISE = false := rfl

/-- Deny never executes. -/
theorem deny_never_executes : mayExecute .DENY = false := rfl

/-- Review never executes (held for a human). -/
theorem review_never_executes : mayExecute .REVIEW = false := rfl

/-- Only ALLOW executes. -/
theorem execute_iff_allow (v : Szl) : mayExecute v = true ↔ v = .ALLOW := by
  cases v <;> decide

/-- Map Credo → SZL under the fail-closed flags.

    human     = a named natural-person principal is present
    evidence  = required evidence items are present
    floorMiss = Λ advisory floor was missed (NOT a uniqueness proof)
    hardDeny  = a prior DENY is already on the session
-/
def mapCredo (c : Credo) (human evidence floorMiss hardDeny : Bool) : Szl :=
  if hardDeny then .DENY
  else if !evidence then
    match c with
    | .block => .DENY
    | _ => .REVIEW
  else if floorMiss then
    match c with
    | .block => .DENY
    | _ => .REVIEW
  else
    match c with
    | .allow => .ALLOW
    | .block => .DENY
    | .escalate => if human then .REVIEW else .DENY
    | .advise => .ADVISE

/-- C2: a prior hard DENY stays DENY no matter what Credo says next. -/
theorem hard_deny_unliftable (c : Credo) (human evidence floorMiss : Bool) :
    mapCredo c human evidence floorMiss true = .DENY := by
  cases c <;> cases human <;> cases evidence <;> cases floorMiss <;> rfl

/-- C2 companion: execution stays false after a hard DENY. -/
theorem hard_deny_never_executes (c : Credo) (human evidence floorMiss : Bool) :
    mayExecute (mapCredo c human evidence floorMiss true) = false := by
  rw [hard_deny_unliftable]; rfl

/-- C1: an advise event, with complete evidence and no floor miss, is ADVISE
    and does not execute. -/
theorem advise_is_advise :
    mapCredo .advise true true false false = .ADVISE := rfl

theorem advise_does_not_execute :
    mayExecute (mapCredo .advise true true false false) = false := rfl

/-- C3: escalate without a human principal is DENY. -/
theorem escalate_without_human_is_deny :
    mapCredo .escalate false true false false = .DENY := rfl

/-- C3 companion: escalate with a human principal is REVIEW, still no execute. -/
theorem escalate_with_human_is_review :
    mapCredo .escalate true true false false = .REVIEW := rfl

theorem escalate_never_executes (human : Bool) :
    mayExecute (mapCredo .escalate human true false false) = false := by
  cases human <;> decide

/-- C4: missing evidence never yields ALLOW. -/
theorem missing_evidence_not_allow (c : Credo) (human floorMiss hardDeny : Bool) :
    mapCredo c human false floorMiss hardDeny ≠ .ALLOW := by
  cases c <;> cases human <;> cases floorMiss <;> cases hardDeny <;> decide

/-- C5: a Λ-floor miss never yields ALLOW. This is an admission rule,
    not a proof that Λ is unique. Conjecture 1 stays open. -/
theorem floor_miss_not_allow (c : Credo) (human evidence hardDeny : Bool) :
    mapCredo c human evidence true hardDeny ≠ .ALLOW := by
  cases c <;> cases human <;> cases evidence <;> cases hardDeny <;> decide

/-- Clean allow path: complete evidence, no floor miss, no hard deny. -/
theorem allow_path :
    mapCredo .allow true true false false = .ALLOW := rfl

theorem allow_path_executes :
    mayExecute (mapCredo .allow true true false false) = true := rfl

/-- Block is DENY and the artifact of the refusal. -/
theorem block_is_deny :
    mapCredo .block true true false false = .DENY := rfl

#print axioms advise_never_executes
#print axioms deny_never_executes
#print axioms review_never_executes
#print axioms execute_iff_allow
#print axioms hard_deny_unliftable
#print axioms hard_deny_never_executes
#print axioms advise_is_advise
#print axioms advise_does_not_execute
#print axioms escalate_without_human_is_deny
#print axioms escalate_with_human_is_review
#print axioms escalate_never_executes
#print axioms missing_evidence_not_allow
#print axioms floor_miss_not_allow
#print axioms allow_path
#print axioms allow_path_executes
#print axioms block_is_deny

end Showcase.Frontier.CredoVerdictWitness
