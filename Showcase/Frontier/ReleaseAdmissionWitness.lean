import Lean
/-!
# ReleaseAdmissionWitness — source-bound, noncompensatory admission
Experimental Lean/Core specification. This is NOT a proof of an actual GitHub,
Hugging Face, or production implementation. Boolean attestations are external
observations, and string equality is NOT cryptographic verification.

The trusted gate is a meet (AND) of required conditions. Neither historic
success nor a high advisory Lambda score can compensate for a failed gate.
No new axiom declarations; no proof placeholders. Not in the locked eight.
-/

namespace Lutar.ReleaseAdmission

/-- Observations are supplied by an external, source-authenticated reader.
    SHA strings are opaque identities here, NOT cryptographic proofs. -/
structure Snapshot where
  sourceSHA : String
  checkedSHA : String
  publishedSHA : String
  runtimeSHA : String
  requiredCIGreen : Bool
  signatureVerified : Bool
  evidenceFresh : Bool
  runtimeHealthy : Bool
  ownerApproved : Bool
  maintenanceOpen : Bool
  deriving Repr, DecidableEq

/-- A release-admission certificate, *conditional* on witnessed input facts.
    Its fields prevent CI green from standing in for a live signed release. -/
structure Admission (s : Snapshot) : Prop where
  ciExact : s.checkedSHA = s.sourceSHA
  publisherExact : s.publishedSHA = s.sourceSHA
  runtimeExact : s.runtimeSHA = s.sourceSHA
  ci : s.requiredCIGreen = true
  signed : s.signatureVerified = true
  fresh : s.evidenceFresh = true
  healthy : s.runtimeHealthy = true
  approved : s.ownerApproved = true
  windowOpen : s.maintenanceOpen = true

/-- SHA mismatch enforces HOLD; the proof does not infer which source is newer. -/
theorem publisher_mismatch_holds (s : Snapshot)
    (h : s.sourceSHA ≠ s.publishedSHA) : ¬ Admission s := by
  intro admitted
  exact h admitted.publisherExact.symm

theorem runtime_mismatch_holds (s : Snapshot)
    (h : s.sourceSHA ≠ s.runtimeSHA) : ¬ Admission s := by
  intro admitted
  exact h admitted.runtimeExact.symm

theorem stale_ci_head_holds (s : Snapshot)
    (h : s.checkedSHA ≠ s.sourceSHA) : ¬ Admission s := by
  intro admitted
  exact h admitted.ciExact

theorem missing_required_ci_holds (s : Snapshot)
    (h : s.requiredCIGreen ≠ true) : ¬ Admission s := by
  intro admitted
  exact h admitted.ci

theorem missing_signature_holds (s : Snapshot)
    (h : s.signatureVerified ≠ true) : ¬ Admission s := by
  intro admitted
  exact h admitted.signed

theorem expired_evidence_holds (s : Snapshot)
    (h : s.evidenceFresh ≠ true) : ¬ Admission s := by
  intro admitted
  exact h admitted.fresh

theorem unhealthy_runtime_holds (s : Snapshot)
    (h : s.runtimeHealthy ≠ true) : ¬ Admission s := by
  intro admitted
  exact h admitted.healthy

theorem closed_window_holds (s : Snapshot)
    (h : s.maintenanceOpen ≠ true) : ¬ Admission s := by
  intro admitted
  exact h admitted.windowOpen

theorem missing_approval_holds (s : Snapshot)
    (h : s.ownerApproved ≠ true) : ¬ Admission s := by
  intro admitted
  exact h admitted.approved

/-- If admitted, publisher and running image are both bound to source SHA. -/
theorem published_matches_runtime (s : Snapshot) (h : Admission s) :
    s.publishedSHA = s.runtimeSHA :=
  h.publisherExact.trans h.runtimeExact.symm

/-- CI is for exactly the runtime source, not a historic successful attempt. -/
theorem checked_matches_runtime (s : Snapshot) (h : Admission s) :
    s.checkedSHA = s.runtimeSHA :=
  h.ciExact.trans h.runtimeExact.symm

/-- Lambda is advisory; missing mandatory evidence forces effective score zero.
    This proposition-level definition is not an executable release controller. -/
noncomputable def effectiveScore (s : Snapshot) (lambdaScore : Nat) : Nat := by
  classical
  exact if Admission s then lambdaScore else 0

theorem missing_signature_zeroes_score (s : Snapshot) (lambdaScore : Nat)
    (h : s.signatureVerified ≠ true) :
    effectiveScore s lambdaScore = 0 := by
  have hold : ¬ Admission s := missing_signature_holds s h
  simp [effectiveScore, hold]

theorem effective_score_not_above_lambda (s : Snapshot) (lambdaScore : Nat) :
    effectiveScore s lambdaScore ≤ lambdaScore := by
  classical
  by_cases h : Admission s
  · simp [effectiveScore, h]
  · simp [effectiveScore, h]

end Lutar.ReleaseAdmission
