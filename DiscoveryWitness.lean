/-
================================================================================
  DiscoveryWitness.lean
  SZL Holdings — machine-checked witness logic for the a11oy Proof-to-Discovery
  engine (szl.discovery/v1 receipts, band: SZLHOLDINGS/wave-logs discovery/).

  Doctrine posture: EXPERIMENTAL / additive. This file is NOT folded into the
  locked Doctrine-v11 baseline (749/14/163) and does NOT change the locked-proven
  set {F1,F4,F7,F11,F12,F18,F19,F22}. It lives OUTSIDE Lutar/ so it is NOT
  counted by .github/scripts/lean_numbers.py and does not touch the locked
  Doctrine-v11 baseline. Built (and kernel-checked) by `lake build` (default).

  Mathlib-free, core Lean only (house precedent: FrontierShowcase libs) — the
  witness decision logic needs nothing beyond the Lean kernel itself; a smaller
  dependency surface is the stronger posture for a witness. Zero `sorry`.

  HONEST SCOPE (no overclaim): this file kernel-checks the ENGINE'S DECISION
  LOGIC — the fail-closed structure of the verdict pipeline — NOT the evidence
  itself, NOT any trained model, and NOT the independent witness. The
  independently_witnessed question remains OWNER-GATED by doctrine; the witness
  theorem below machine-checks exactly that: while it is UNRESOLVED, no
  candidate can be PROMOTION_ELIGIBLE.
================================================================================
-/

namespace DiscoveryWitness

/-- Verdict of one justification question, mirroring szl.discovery/v1. -/
inductive WVerdict : Type
  | PROVEN
  | REFUTED
  | UNRESOLVED
deriving DecidableEq, Repr

/-- The four justification questions every candidate must answer, mirroring
the a11oy Proof-to-Discovery loop. -/
inductive JQuestion : Type
  | training_completed_validly
  | final_artifact_present
  | measured_improvement
  | independently_witnessed
deriving DecidableEq, Repr

/-- Aggregate engine action for a candidate. -/
inductive WAction : Type
  | PROMOTION_ELIGIBLE
  | HOLD
deriving DecidableEq, Repr

/-- Engine decision rule: a candidate is PROMOTION_ELIGIBLE iff EVERY
justification question is PROVEN and the reward verdict is RECOMMENDED.
Publication itself remains owner-gated downstream of this decision.
Each question is an explicit decidable equality so the rule elaborates in
core Lean with no classical instances. -/
def decide (v : JQuestion → WVerdict) (recommended : Prop) [Decidable recommended] :
    WAction :=
  if v JQuestion.training_completed_validly = WVerdict.PROVEN
      ∧ v JQuestion.final_artifact_present = WVerdict.PROVEN
      ∧ v JQuestion.measured_improvement = WVerdict.PROVEN
      ∧ v JQuestion.independently_witnessed = WVerdict.PROVEN ∧ recommended then
    WAction.PROMOTION_ELIGIBLE
  else
    WAction.HOLD

/-- **Fail-closed (TH-DW1).** Any question that is not PROVEN — REFUTED or
UNRESOLVED — forces HOLD, regardless of the reward verdict. This is the
core fail-closed invariant of the estate, machine-checked. -/
theorem fail_closed (v : JQuestion → WVerdict) (recommended : Prop)
    [Decidable recommended] (q0 : JQuestion) (hq0 : v q0 ≠ WVerdict.PROVEN) :
    decide v recommended = WAction.HOLD := by
  unfold decide
  split
  · rename_i h
    cases q0 with
    | training_completed_validly => exact absurd h.1 hq0
    | final_artifact_present => exact absurd h.2.1 hq0
    | measured_improvement => exact absurd h.2.2.1 hq0
    | independently_witnessed => exact absurd h.2.2.2.1 hq0
  · rfl

/-- **No promotion without recommendation (TH-DW2).** Even with every question
PROVEN, a candidate that is not RECOMMENDED holds. -/
theorem hold_unrecommended (v : JQuestion → WVerdict) (recommended : Prop)
    [Decidable recommended] (hr : ¬recommended) :
    decide v recommended = WAction.HOLD := by
  unfold decide
  split
  · rename_i h
    exact absurd h.2.2.2.2 hr
  · rfl

/-- Verdict from an evidence channel: `some` receipt present (content validated
upstream by the engine) is PROVEN; `none` — no receipt — is UNRESOLVED.
This mirrors the engine: absence of a reward/hbfinal receipt is UNRESOLVED. -/
def verdictFromEvidence {α : Type} (e : Option α) : WVerdict :=
  match e with
  | none => WVerdict.UNRESOLVED
  | some _ => WVerdict.PROVEN

/-- **Absence of evidence is never proof (TH-DW3).** A channel with no receipt
maps to UNRESOLVED — the engine may never turn a missing receipt into PROVEN,
so the candidate cannot pass on silence. -/
theorem absence_is_unresolved {α : Type} (e : Option α) (h : e = none) :
    verdictFromEvidence e = WVerdict.UNRESOLVED := by
  rw [h]
  rfl

/-- **The witness gate (TH-DW4).** While independently_witnessed is UNRESOLVED
— its standing state until the owner commissions an independent witness — no
candidate can be PROMOTION_ELIGIBLE, no matter how strong the other evidence.
This machine-checks the doctrine: promotion is owner-gated at the witness leg. -/
theorem witness_gate_blocks_promotion (v : JQuestion → WVerdict)
    (recommended : Prop) [Decidable recommended]
    (hw : v JQuestion.independently_witnessed = WVerdict.UNRESOLVED) :
    decide v recommended = WAction.HOLD := by
  apply fail_closed v recommended JQuestion.independently_witnessed
  rw [hw]
  decide

/-- **Completeness of the rule (TH-DW5).** If all four questions are ever
PROVEN (including an owner-commissioned witness) AND the reward verdict is
RECOMMENDED, the rule yields PROMOTION_ELIGIBLE — the gate blocks, it does not
permanently seal. -/
theorem eligible_when_all_proven_and_recommended (v : JQuestion → WVerdict)
    (recommended : Prop) [Decidable recommended]
    (hall : ∀ q, v q = WVerdict.PROVEN) (hr : recommended) :
    decide v recommended = WAction.PROMOTION_ELIGIBLE := by
  unfold decide
  split
  · rfl
  · rename_i h
    exact absurd (And.intro (hall _) (And.intro (hall _)
      (And.intro (hall _) (And.intro (hall _) hr)))) h

end DiscoveryWitness
