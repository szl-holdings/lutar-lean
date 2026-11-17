import Lean
import Lutar.Axioms
import Lutar.Invariant
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

/-! ## Direct Lutar A1–A5 integration

This experimental bridge uses the repository's REAL `LutarAxioms` structure
and the existing geometric-mean implementation `Lutar.Λ`, rather than an
unrelated numeric proxy. A1–A5 do **not** imply uniqueness of `Λ`.
The evidence certificate remains an abstract hypothesis: no live signing,
provider readback or runtime-controller correctness is proved here.
-/

/-- Gate an arbitrary Lutar aggregator on the source-bound release admission
certificate. A non-admitted state produces zero, never an inflated score. -/
noncomputable def guardedLutar {k : Nat} (s : Snapshot)
    (Φ : Lutar.Aggregator k) (axes : Lutar.Axes k) : NNReal := by
  classical
  exact if Admission s then Φ axes else 0

theorem guardedLutar_zero_of_hold {k : Nat} (s : Snapshot)
    (Φ : Lutar.Aggregator k) (axes : Lutar.Axes k)
    (h : ¬ Admission s) :
    guardedLutar s Φ axes = 0 := by
  simp [guardedLutar, h]

theorem guardedLutar_equals_aggregator_when_admitted {k : Nat} (s : Snapshot)
    (Φ : Lutar.Aggregator k) (axes : Lutar.Axes k)
    (h : Admission s) :
    guardedLutar s Φ axes = Φ axes := by
  simp [guardedLutar, h]

/-- A1 is preserved by gating. A higher axis cannot lower the score, provided
the base aggregator satisfies Lutar's original monotonicity axiom. -/
theorem guardedLutar_monotone_of_axioms {k : Nat} (s : Snapshot)
    (Φ : Lutar.Aggregator k) (hA : Lutar.LutarAxioms Φ)
    (x y : Lutar.Axes k) (hxy : ∀ i, x i ≤ y i) :
    guardedLutar s Φ x ≤ guardedLutar s Φ y := by
  classical
  by_cases h : Admission s
  · simpa [guardedLutar, h] using (hA.A1 x y hxy)
  · simp [guardedLutar, h]

/-- A2 is preserved: for any nonnegative common scalar c, gating is
compatible with positive homogeneity. -/
theorem guardedLutar_homogeneous_of_axioms {k : Nat} (s : Snapshot)
    (Φ : Lutar.Aggregator k) (hA : Lutar.LutarAxioms Φ)
    (x : Lutar.Axes k) (c : NNReal) :
    guardedLutar s Φ (fun i => c * x i) = c * guardedLutar s Φ x := by
  classical
  by_cases h : Admission s
  · simpa [guardedLutar, h] using (hA.A2 c x)
  · simp [guardedLutar, h]

/-- A3 is retained on the admitted path, without a vacuous diagonal axiom. -/
theorem guardedLutar_diagonal_of_axioms {k : Nat} (s : Snapshot)
    (Φ : Lutar.Aggregator k) (hA : Lutar.LutarAxioms Φ)
    (h : Admission s) (c : NNReal) :
    guardedLutar s Φ (fun _ => c) = c := by
  classical
  simpa [guardedLutar, h] using (hA.A3.A3_normalize c)

/-- The actual Lutar geometric-mean aggregator, no invented replacement
formula. A1–A5 uniqueness remains Conjecture 1 / false unconditionally. -/
noncomputable def guardedLambda (s : Snapshot) (k : Nat)
    (axes : Lutar.Axes k) : NNReal :=
  guardedLutar s (Lutar.Λ k) axes

theorem guardedLambda_refuses_missing_signature (s : Snapshot) (k : Nat)
    (axes : Lutar.Axes k) (h : s.signatureVerified ≠ true) :
    guardedLambda s k axes = 0 := by
  have hhold : ¬ Admission s := missing_signature_holds s h
  simpa [guardedLambda] using
    (guardedLutar_zero_of_hold s (Lutar.Λ k) axes hhold)

end Lutar.ReleaseAdmission
