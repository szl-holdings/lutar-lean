/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 24 — Admissibility-Membership Certification (GPD Adm-certifier, formalized)

## Mission
Governed Post-Determinism (GPD) replaces byte-identical agreement with **certified
semantic admissibility**: the unit of agreement is membership in the admissibility
relation `Adm`, witnessed by a signed certificate. This file gives the FIRST Lean
formalization of that certifier as a *structure* and proves its core safety
property — a **single linearization point**: under one admissibility certificate,
at most one verdict can be quorum-committed (no split-brain admission).

It does this by REDUCTION to the already-proven Wave23 conditional Khipu BFT
safety theorem (`khipu_quorum_safety_conditional`). No new mathematics is claimed:
the certificate bundles exactly Wave23's runtime-checkable hypotheses
(`n ≥ 3f+1`, `|faulty| ≤ f`, honest non-equivocation realized by ECDSA-P256
cosignatures), and the linearizability property is their direct consequence.

## What is proven (placeholder-free; NO new `axiom` token; NO sorry)
- `AdmissibilityCertificate` — the GPD Adm-membership certifier as data: the
  charter, the fault bound, the signed-vote relation, and honest non-equivocation.
- `CertifiedCommit` — a verdict that a size-`≥ n−f` quorum has certified under a
  given certificate (the "signed execution certificate" connecting Wave23 to a
  committed action).
- `adm_certificate_agreement` — any two `CertifiedCommit`s under the SAME
  certificate decide the SAME verdict. (Reduction to Wave23.)
- `semantic_linearizability_point` — restatement as a linearizability invariant:
  the committed verdict is well-defined (single linearization point); two
  admissible commits cannot disagree.
- `certified_commit_subsingleton` — the type of committed verdicts under one
  certificate is a subsingleton (at most one value), the GPD "one admitted
  outcome" guarantee.

## Honesty / scope (Doctrine v11/v12, LOCKED)
- EXPERIMENTAL (`Lutar.Wave24`). NOT folded into the LOCKED v11 baseline. The
  locked-proven set STAYS EXACTLY 5 `{F1,F11,F12,F18,F19}`. Λ stays Conjecture 1.
- The result is **CONDITIONAL** — it inherits Wave23's hypotheses verbatim
  (the certificate IS those hypotheses). UNCONDITIONAL BFT safety stays
  **Conjecture 2**. This is the safety half of linearizability (agreement on the
  committed value); full linearizability (real-time order + liveness, Conjecture 3)
  is NOT claimed here.
- OPEN OBSTRUCTION (honest, documented — NOT a theorem, NOT a sorry):
  Epistemic State Replication lineage-retention asks for a Verifiable Semantic
  Rollback whose receipt PROVABLY retains the failure-cause lineage across a
  rollback. The precise obstruction is that rollback over the `opaque
  canonicalHistory` kernel form (untouched by Wave23) is not yet a structure-
  preserving morphism on the receipt DAG — there is no in-tree lemma that a
  rolled-back history refines the pre-rollback lineage. We state this as the
  next frontier; we do NOT assert it.
- Known-theorem composition only (PBFT/HotStuff agreement via Wave23). NO new
  declared axiom, NO proof placeholder, NO `native_decide`. Intended axiom
  footprint per decl `⊆ {propext, Classical.choice, Quot.sound}` — to be
  confirmed by CI `#print axioms` / lake kernel-check before any merge.

## Citations (real)
- Herlihy & Wing, "Linearizability: A Correctness Condition for Concurrent
  Objects", ACM TOPLAS 12(3), 1990, doi:10.1145/78969.78972 (linearization point).
- Castro & Liskov, "Practical Byzantine Fault Tolerance", OSDI 1999 (agreement).
- Yin et al., "HotStuff", PODC 2019 (signed quorum certificates).
- Wave23 (`Lutar/Wave23/QuorumSafety.lean`) — the conditional safety theorem
  this file certifies.

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/
import Lutar.Wave23.QuorumSafety

namespace Lutar.Wave24.AdmissibilityCertificate

open Lutar.Wave23.QuorumSafety

variable {n : ℕ}

/-! ## §1 The GPD Adm-membership certifier, as data -/

/-- **Admissibility certificate (GPD Adm-membership certifier).** Bundles exactly
the runtime-checkable hypotheses of Wave23 conditional safety: the Ubuntu charter
`n ≥ 3f+1`, the fault bound `|faulty| ≤ f`, the signed-vote RELATION (faulty
organs MAY equivocate), and honest non-equivocation (realized at runtime by
ECDSA-P256 cosignatures — one valid signed allow per honest organ per action).
This is GPD's `Adm` certifier made into compilable data. -/
structure AdmissibilityCertificate (n : ℕ) (Verdict : Type) where
  /-- Byzantine fault budget. -/
  f : ℕ
  /-- Ubuntu charter `n ≥ 3f+1` (Lamport–Shostak–Pease necessity). -/
  charter : n ≥ 3 * f + 1
  /-- The actually-faulty organs. -/
  faulty : Finset (Fin n)
  /-- At most `f` organs are faulty. -/
  faulty_bound : faulty.card ≤ f
  /-- Signed-vote relation; faulty organs may satisfy it for several verdicts. -/
  votes : Fin n → Verdict → Prop
  /-- Honest organs do not equivocate (the weakest checkable hypothesis). -/
  honest : HonestNonEquivocation faulty votes

/-- **Certified commit (signed execution certificate).** A verdict that a quorum
`Q` of size `≥ n − f` has certified under the certificate `cert` — i.e. every
organ in `Q` signed `verdict`. This is the object Wave23 connects to a committed,
receipt-anchored action. -/
structure CertifiedCommit {Verdict : Type} (cert : AdmissibilityCertificate n Verdict) where
  /-- The certifying quorum. -/
  Q : Finset (Fin n)
  /-- Quorum size meets the `n − f` certificate threshold. -/
  quorum : Q.card ≥ n - cert.f
  /-- The verdict this quorum commits. -/
  verdict : Verdict
  /-- Every organ in the quorum signed this verdict. -/
  certifies : ∀ o ∈ Q, cert.votes o verdict

/-! ## §2 Single linearization point (safety of admissibility) -/

/-- **Admissibility agreement (THEOREM, by reduction to Wave23).** Any two commits
certified under the SAME admissibility certificate decide the SAME verdict. The
certificate cannot admit two conflicting outcomes. -/
theorem adm_certificate_agreement {Verdict : Type}
    (cert : AdmissibilityCertificate n Verdict)
    (c₁ c₂ : CertifiedCommit cert) :
    c₁.verdict = c₂.verdict :=
  khipu_quorum_safety_conditional cert.f cert.charter cert.faulty cert.faulty_bound
    c₁.Q c₂.Q c₁.quorum c₂.quorum cert.votes cert.honest
    c₁.verdict c₂.verdict c₁.certifies c₂.certifies

/-- **Semantic linearization point (THEOREM).** Restatement of agreement as a
linearizability invariant: under one admissibility certificate the committed
verdict is well-defined — there is a single linearization point, so two admissible
commits can never disagree. This is the safety half of linearizability for
post-deterministic (GPD) admission. Full linearizability (real-time order +
liveness) is Conjecture 3 and NOT claimed. -/
theorem semantic_linearizability_point {Verdict : Type}
    (cert : AdmissibilityCertificate n Verdict)
    (c₁ c₂ : CertifiedCommit cert) :
    c₁.verdict = c₂.verdict :=
  adm_certificate_agreement cert c₁ c₂

/-- **Subsingleton of committed verdicts (COROLLARY).** Under a fixed certificate,
the committed verdict is unique up to the data of which quorum certified it: any
two certified commits carry equal verdicts. This is the GPD "one admitted
outcome" guarantee expressed as a `Subsingleton` on the verdict projection. -/
theorem certified_commit_subsingleton {Verdict : Type}
    (cert : AdmissibilityCertificate n Verdict) :
    ∀ c₁ c₂ : CertifiedCommit cert, c₁.verdict = c₂.verdict :=
  fun c₁ c₂ => adm_certificate_agreement cert c₁ c₂

#print axioms adm_certificate_agreement
#print axioms semantic_linearizability_point
#print axioms certified_commit_subsingleton

end Lutar.Wave24.AdmissibilityCertificate
