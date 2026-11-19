/-
Copyright (c) 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Covenant/ReceiptChain.lean - Memory Covenant receipt-chain soundness core

Additive EXPERIMENTAL file inside the registered `Lutar/Covenant` scope
(lean_numbers.py EXPERIMENTAL_SCOPES, the DenyMonotonic pack class): NOT
wired into Lutar.lean, NOT folded into the locked v11 baseline (locked-proven
stays exactly 8 {F1,F4,F7,F11,F12,F18,F19,F22}). No baseline file is edited;
Lutar/Covenant/DenyMonotonic.lean is not touched.

Competitive anchor (estate competitive watch 2026-11-19): the agent-memory
field is shipping receipt-shaped surface without formal memory semantics.
Agent Receipts protocol (agentreceipts.ai, tooling obsigna.dev, Nov 6 2026):
Ed25519-signed W3C-VC receipts, hash-chained, TOOL-CALL scope only. Zep Agent
Skills run-citations (versioned, restorable, not tamper-evident). IETF
Internet-Draft "The Agent Record" (Aug 2026): RFC 6962-style witness-countersigned
logs with memory-integrity hash commitments. SCITT. NOBODY formalizes
MEMORY-OPERATION receipt semantics. This module is the covenant answer at the
math layer: the deny-by-default policy core (spec 2.1) BOUND to a tamper-evident
receipt chain over governed memory write/recall operations, with countersigned
head verification soundness (the `obsigna receipt verify` shape).

## What is proven (Lean 4 core only, NO Mathlib import, no open obligation, NO new axiom)
- denyMonotonic: local restatement of the hard-deny ABSORBING-STATE core
  (import-free duplicate so this file stands alone under `lake env lean`, the
  same pattern as the Wave8 M2 pack).
- hardDenied_never_applied: the DENY-BY-DEFAULT MEMORY-PLANE theorem. A
  well-formed receipt for a hard-denied operation class NEVER records
  applied=true, for any approval count.
- chain_consistency / chain_tamper_evident: M2-class append-only consistency
  for covenant receipts (structured payloads); collision resistance is an
  explicit INJECTIVITY HYPOTHESIS, not a declared axiom.
- countersign_length_binding: an injective (idealized-unforgeability,
  binding direction) countersignature over (length, head) binds BOTH; heads
  must never be countersigned bare (cross-length boundary, honestly drawn).
- countersigned_head_consistency: verification soundness - two ledgers whose
  countersigned (length, head) records verify equal carry pointwise-identical
  receipt sequences.

## Honesty / scope
- Collision resistance and signature binding are idealized as explicit
  injectivity HYPOTHESES (Wave8 M2 posture; cf. PRF-injectivity-as-hypothesis
  in lean_numbers.py TE-3). Concrete SHA-256 / Ed25519 properties are empirical
  facts OUTSIDE this module. Injectivity models the BINDING direction only,
  not confidentiality.
- No refinement proof connects deployed gate code, or an obsigna-daemon-class
  signer, to this abstract model; runtime correspondence requires separate
  evidence (same honesty rule as DenyMonotonic spec 2.3).
- ONLY same-length chains are claimed (Fin n). Cross-length attacker models are
  handled by binding length INTO the countersigned record.
- Merkle-tree heads over memory-state commitments (the IETF Agent Record /
  RFC 6962 signed-tree-head direction, generalized audit paths) are the
  NOT-yet-formalized extension lane; this module covers the linear chain layer.
- The operation classes are MODEL INPUTS; this module does not classify real
  memory requests, and Lambda uniqueness stays Conjecture 1 (not asserted).

## Citations
- Agent Receipts protocol: https://agentreceipts.ai (tooling: https://obsigna.dev)
- IETF "The Agent Record": witness-countersigned event logs for agent memory:
  https://www.ietf.org/archive/id/draft-maintainer-1f916-agent-record-00.html
- RFC 6962 Certificate Transparency (signed tree heads, audit paths)
- Covenant spec: szl-frontier docs/COVENANT_V0_4_COUNTERSIGN_SPEC_2026-11-15.md

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/

namespace Lutar.Covenant.ReceiptChain

/-! ## 1. Policy core (spec 2.1, local restatement) -/

inductive OpClass
  | benign
  | recon
  | foreignWrite
  | weaponize
  deriving DecidableEq, Repr

inductive PolicyState
  | release
  | softDeny
  | hardDeny
  deriving DecidableEq, Repr

/-- The governed memory operation classes this receipt chain covers: writes and
recalls. Both are receipted: recall provenance is part of the audit surface,
not just writes. -/
inductive MemOp
  | write
  | recall
  deriving DecidableEq, Repr

/-- The gate: entry policy state of each operation class. The three covenant
hard-deny classes enter at hardDeny; everything else enters at softDeny
(deny-by-default: an approval can lift softDeny, and benign does lift). -/
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

def approvals : Nat -> PolicyState -> PolicyState
  | 0, s => s
  | n + 1, s => approvals n (approveStep s)

theorem denyMonotonic (n : Nat) (s : PolicyState) (h : s = PolicyState.hardDeny) :
    approvals n s = PolicyState.hardDeny := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih => exact ih (approveStep s) (by subst h; rfl)

theorem hardDeny_ne_release :
    Not ((PolicyState.hardDeny : PolicyState) = PolicyState.release) := by
  decide

/-- Positive control (the state machine is not a wall against the benign): a
benign operation IS released by one approval. -/
theorem benign_lifts_with_one_approval :
    approvals 1 (gate OpClass.benign) = PolicyState.release := rfl

/-! ## 2. Covenant receipts as chain payloads -/

/-- One governed memory operation receipt record: which operation, on whose
authority, over which memory key, whether it was ALLOWED to apply, and the
gate state recorded at write time plus the approval count that produced it. -/
structure ReceiptPayload where
  op : MemOp
  opClass : OpClass
  principal : Nat
  key : Nat
  applied : Bool
  approvalCount : Nat
  state : PolicyState
  deriving DecidableEq, Repr

/-- Receipt WELL-FORMEDNESS (the covenant runtime contract, idealized): the
recorded state is exactly the entry gate state after approvalCount approvals,
and NOTHING may record applied=true unless the state reached release. -/
def receiptWF (r : ReceiptPayload) : Prop :=
  r.state = approvals r.approvalCount (gate r.opClass) /\
  (r.applied = true -> r.state = PolicyState.release)

/-- **Deny-by-default memory-plane theorem.** A hard-denied operation class
can never produce a well-formed receipt that records applied=true, for any
approval count: the absorbing hardDeny state cannot reach release. This is
the property the tool-call-scope receipt protocols do not have: the policy
decision is bound INTO the receipt, so a denied memory write cannot be
retroactively recorded as applied. -/
theorem hardDenied_never_applied (r : ReceiptPayload)
    (hcls : gate r.opClass = PolicyState.hardDeny)
    (hwf1 : r.state = approvals r.approvalCount (gate r.opClass))
    (hwf2 : r.applied = true -> r.state = PolicyState.release) :
    r.applied = false := by
  cases hap : r.applied with
  | false => exact hap
  | true =>
    exfalso
    have hrel : r.state = PolicyState.release := hwf2 hap
    have hdn : approvals r.approvalCount (gate r.opClass) = PolicyState.hardDeny :=
      denyMonotonic r.approvalCount (gate r.opClass) hcls
    rw [hwf1, hdn] at hrel
    exact hardDeny_ne_release hrel

/-- Positive control: a benign write released by one approval IS a well-formed
applied receipt. Denial pressure is reserved for the hard classes. -/
theorem benign_write_wf_control :
    receiptWF
      { op := MemOp.write, opClass := OpClass.benign, principal := 0, key := 0,
        applied := true, approvalCount := 1, state := PolicyState.release } := by
  unfold receiptWF
  exact And.intro rfl (fun _ => rfl)

/-! ## 3. The receipt hash chain (M2 lift, Lean-core only) -/

/-- Local, Mathlib-free injectivity predicate (collision-resistance
idealization), same posture as Lutar/Wave8/HashChain.lean. -/
def Inj {a b : Type} (f : a -> b) : Prop := forall t u, f t = f u -> t = u

/-- A receipt chain over payload type P and hash type Hsh:
`seed` genesis hash; `payload` the n receipts; `H` the linking hash
H (prevHash, payload) = nextHash. -/
structure Chain (P Hsh : Type) (n : Nat) where
  seed    : Hsh
  payload : Fin n -> P
  H       : Prod Hsh P -> Hsh

/-- The published head hash of a chain: fold H over the payloads from the seed. -/
def headHash {P Hsh : Type} : (n : Nat) -> Chain P Hsh n -> Hsh
  | 0,     c => c.seed
  | n + 1, c =>
      c.H (headHash n
            { seed := c.seed, payload := fun i => c.payload i.castSucc, H := c.H },
           c.payload (Fin.last n))

/-- Chain consistency (M2 lift): two chains sharing seed and injective linking
hash, with equal published head hashes, carry identical receipt records at
every position. Induction on the chain length; the only nontrivial step peels
one H via injectivity. -/
theorem chain_consistency {P Hsh : Type}
    (H : Prod Hsh P -> Hsh) (hH : Inj H) (seed : Hsh) :
    forall (n : Nat) (p q : Fin n -> P),
      headHash n { seed := seed, payload := p, H := H }
        = headHash n { seed := seed, payload := q, H := H } ->
      forall i, p i = q i := by
  intro n
  induction n with
  | zero =>
      intro p q _ i
      exact (Fin.elim0 i)
  | succ n ih =>
      intro p q hroot i
      have hpair :
          (headHash n { seed := seed, payload := fun j => p j.castSucc, H := H },
           p (Fin.last n))
            = (headHash n { seed := seed, payload := fun j => q j.castSucc, H := H },
               q (Fin.last n)) := by
        apply hH
        simpa [headHash] using hroot
      have hroot_prime :
          headHash n { seed := seed, payload := fun j => p j.castSucc, H := H }
            = headHash n { seed := seed, payload := fun j => q j.castSucc, H := H } :=
        (Prod.ext_iff.mp hpair).1
      have hlast : p (Fin.last n) = q (Fin.last n) := (Prod.ext_iff.mp hpair).2
      have hrec := ih (fun j => p j.castSucc) (fun j => q j.castSucc) hroot_prime
      exact Fin.lastCases hlast hrec i

/-- Tamper-evidence corollary (M2 contrapositive): if two same-seed chains under
the same injective H differ at some position, their published head hashes
differ: a covenant ledger cannot be rewritten without detection. -/
theorem chain_tamper_evident {P Hsh : Type}
    (H : Prod Hsh P -> Hsh) (hH : Inj H) (seed : Hsh)
    (n : Nat) (p q : Fin n -> P) (i : Fin n) (hne : Not (p i = q i)) :
    Not (headHash n { seed := seed, payload := p, H := H }
          = headHash n { seed := seed, payload := q, H := H }) := by
  intro hroot
  exact hne (chain_consistency H hH seed n p q hroot i)

/-! ## 4. Countersigned head binding -/

/-- **Length binding.** An injective (idealized-unforgeability, binding
direction) countersignature over the record (length, head) binds BOTH
components: two ledgers whose countersigned head records verify equal claim
the same length and the same head hash. Countersigning a BARE head binds nothing
across lengths: heads must always be countersigned with (or inside, RFC
6962-style) their size. -/
theorem countersign_length_binding {Hs : Type} {Sig : Prod Nat Hs -> Nat}
    (hSig : Inj Sig) {n m : Nat} {r s : Hs}
    (h : Sig (n, r) = Sig (m, s)) : n = m /\ r = s :=
  Prod.ext_iff.mp (hSig h)

/-- **Countersigned-head verification soundness** (the `obsigna receipt verify`
shape). If the countersigned (length, head) records of two same-length receipt
ledgers verify equal under an injective signer, then the ledgers carry
pointwise-identical receipt records: a verifier that accepts the signature
accepts the whole history, and divergence in ANY receipt field (operation,
principal, key, applied flag, approval count, recorded state) forces a
signature mismatch. -/
theorem countersigned_head_consistency {P Hs : Type}
    (H : Prod Hs P -> Hs) (hH : Inj H) (seed : Hs)
    {Sig : Prod Nat Hs -> Nat} (hSig : Inj Sig)
    (n : Nat) (p q : Fin n -> P)
    (h : Sig (n, headHash n { seed := seed, payload := p, H := H })
          = Sig (n, headHash n { seed := seed, payload := q, H := H })) :
    forall i, p i = q i :=
  chain_consistency H hH seed n p q (Prod.ext_iff.mp (hSig h)).2

/-! ## Axiom audit (supplementary output, as in the DenyMonotonic pack) -/
#print axioms denyMonotonic
#print axioms hardDeny_ne_release
#print axioms benign_lifts_with_one_approval
#print axioms hardDenied_never_applied
#print axioms benign_write_wf_control
#print axioms chain_consistency
#print axioms chain_tamper_evident
#print axioms countersign_length_binding
#print axioms countersigned_head_consistency

end Lutar.Covenant.ReceiptChain
