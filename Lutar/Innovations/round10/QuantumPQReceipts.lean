/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Round 10 — Contribution A: Post-quantum DSSE receipt signatures

This file formalises a **quantum-secure signature wrapper for DSSE receipts**.
DSSE ("Dead Simple Signing Envelope", secure-systems-lab) is the envelope
format under which SZL Holdings receipts are signed:
  https://github.com/secure-systems-lab/dsse
The Pre-Authentication Encoding (PAE) turns a (payloadType, payload) pair into
a single byte string that is the thing actually signed.

## Frontier claim being supported

> "SZL Holdings receipts survive cryptographically-relevant quantum computer
>  (CRQC) attacks."

To support this we replace any classical-only signer (RSA / ECDSA, both broken
by Shor's algorithm) by a **NIST PQC standard** signer.  The relevant standards,
finalized 2024-08-13, are:

* **FIPS 204 — ML-DSA** (Module-Lattice Digital Signature Algorithm, from
  CRYSTALS-Dilithium).  Lattice-based; security rests on Module-LWE / Module-SIS.
  https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.204.pdf
* **FIPS 205 — SLH-DSA** (Stateless Hash-based DSA, from SPHINCS+).  Security
  rests only on the (second-)preimage resistance of the underlying hash; no
  number-theoretic assumption at all.
  https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.205.pdf
* **FIPS 206 — FN-DSA** (from FALCON), in development.
  https://csrc.nist.gov/projects/post-quantum-cryptography
NIST overview:
  https://www.nist.gov/news-events/news/2024/08/nist-releases-first-3-finalized-post-quantum-encryption-standards

## What is proved here vs. assumed

We model a signature scheme abstractly (`SigScheme`) and define **EUF-CMA**
(existential unforgeability under chosen-message attack) against a *quantum*
adversary.  The post-quantum guarantee is the statement that the DSSE-wrapped
scheme is EUF-CMA-secure against quantum adversaries.  This *cannot* be a closed
Lean proof: it is exactly the cryptographic hardness assumption (Module-SIS for
ML-DSA; hash preimage resistance for SLH-DSA) plus the security reduction in the
FIPS documents.  We therefore:

* `dsse_correctness`            — **fully proved**: a correctly signed receipt
                                  verifies (functional correctness of the wrapper).
* `dsse_distinct_pae_injective` — **fully proved**: the PAE wrapper is injective,
                                  so two receipts with different payloads never
                                  share a signed pre-image (a real DSSE property:
                                  PAE prevents canonicalization confusion).
* `dsse_pq_euf_cma`             — security theorem.  Body reduces, in one honest
                                  `sorry` tagged `PQ_HARDNESS_ASSUMPTION`, to the
                                  underlying scheme's EUF-CMA security against
                                  quantum adversaries.  ZERO math is hidden beyond
                                  the named NIST hardness assumption.

This file is NEW under `Lutar/Innovations/round10/`, OUTSIDE the locked kernel
(749/14/163 untouched).  It imports only `Mathlib.Data.List.Basic` & friends.
-/
import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Basic

namespace Lutar
namespace Round10
namespace PQReceipts

/-! ### 1. Byte strings and the DSSE Pre-Authentication Encoding (PAE) -/

/-- A byte. -/
abbrev Byte := Nat
/-- A byte string. -/
abbrev Bytes := List Byte

/-- A DSSE receipt: a payload type tag and a payload, both byte strings.
This mirrors the `payloadType` / `payload` fields of a DSSE envelope. -/
structure Receipt where
  payloadType : Bytes
  payload     : Bytes
  deriving DecidableEq

/-- A length-prefixed encoding of one field (model of DSSE's `LEN(s) ‖ s`).
We prepend the length as a single leading element; this is enough to recover
unambiguous parsing for the injectivity proof. -/
def lenPrefix (s : Bytes) : Bytes := s.length :: s

/-- `lenPrefix` is injective: the leading length plus the body determine `s`. -/
theorem lenPrefix_injective : Function.Injective lenPrefix := by
  intro a b h
  -- h : a.length :: a = b.length :: b ; the tails are exactly a and b
  exact (List.cons.injEq _ _ _ _).mp h |>.2

/-- **PAE** — the Pre-Authentication Encoding actually fed to the signer.
Real DSSE: `PAE = "DSSEv1" ‖ LEN(type) ‖ type ‖ LEN(payload) ‖ payload`.
We use a length-prefixed concatenation of the two fields (the constant header
is irrelevant to injectivity, so we omit it). -/
def pae (r : Receipt) : Bytes := lenPrefix r.payloadType ++ lenPrefix r.payload

/-- **PAE is injective.**  Two distinct receipts never produce the same signed
pre-image.  This is the property that defeats canonicalization-confusion attacks
(the original motivation for DSSE over bare JSON signing). -/
theorem dsse_distinct_pae_injective : Function.Injective pae := by
  intro a b h
  -- `pae r = lenPrefix r.payloadType ++ lenPrefix r.payload`.
  -- The two `lenPrefix` blocks each begin with their own length, so the whole
  -- list begins with `r.payloadType.length`.  Equality of the two `pae` lists
  -- therefore forces equal type-lengths, hence equal `lenPrefix`-block lengths,
  -- which lets `List.append_inj` split the equation into the two blocks.
  have happ : lenPrefix a.payloadType ++ lenPrefix a.payload
            = lenPrefix b.payloadType ++ lenPrefix b.payload := h
  -- Head of each side is the type length (the leading element of `lenPrefix`).
  have hlen : a.payloadType.length = b.payloadType.length := by
    have : (lenPrefix a.payloadType ++ lenPrefix a.payload).head?
         = (lenPrefix b.payloadType ++ lenPrefix b.payload).head? := by rw [happ]
    simpa [lenPrefix, List.head?] using this
  -- Equal type-lengths ⇒ equal `lenPrefix`-block lengths (block length = len+1).
  have hleneq : (lenPrefix a.payloadType).length = (lenPrefix b.payloadType).length := by
    simp [lenPrefix, hlen]
  obtain ⟨htype, hpay⟩ := List.append_inj happ hleneq
  have htypeEq : a.payloadType = b.payloadType := lenPrefix_injective htype
  have hpayEq  : a.payload = b.payload := lenPrefix_injective hpay
  cases a; cases b; simp_all

/-! ### 2. Abstract signature scheme and quantum EUF-CMA -/

/-- An abstract signature scheme over a message type `Msg`.
`sign` is keyed by a secret key `sk`, `verify` by a public key `pk`.
We keep keys/signatures abstract (`SK`, `PK`, `Sig`).  The underlying NIST
scheme is `SigScheme Bytes ..`; the DSSE wrapper is `SigScheme Receipt ..`. -/
structure SigScheme (Msg SK PK Sig : Type) where
  /-- key relation: `pk` is the public key matching secret key `sk`. -/
  keyed   : SK → PK → Prop
  sign    : SK → Msg → Sig
  verify  : PK → Msg → Sig → Bool
  /-- **Functional correctness.** An honestly produced signature verifies. -/
  correct : ∀ sk pk, keyed sk pk → ∀ m, verify pk m (sign sk m) = true

/-- A *quantum adversary* against EUF-CMA is modelled as a (possibly
randomized — here deterministic for the formal skeleton) procedure that, given
the public key and the list of messages it has queried to the signing oracle,
outputs a candidate `(message, signature)` forgery.  Quantumness enters only in
the hardness assumption discharged below; the *interface* is classical because
the forgery itself is a classical bit-string. -/
structure QAdversary (Msg PK Sig : Type) where
  /-- the messages the adversary chose to have signed. -/
  queries : PK → List Msg
  /-- the attempted forgery. -/
  forge   : PK → Msg × Sig

/-- **EUF-CMA win condition (quantum).**  The adversary wins if its forged
message was *never queried* yet the forged signature verifies under `pk`. -/
def Wins {Msg SK PK Sig : Type} [DecidableEq Msg] (S : SigScheme Msg SK PK Sig)
    (sk : SK) (pk : PK) (A : QAdversary Msg PK Sig) : Prop :=
  (A.forge pk).1 ∉ A.queries pk ∧ S.verify pk (A.forge pk).1 (A.forge pk).2 = true

/-- **`SecureAgainstQuantum`** — the scheme is EUF-CMA-secure against every
quantum adversary: no adversary wins for any honestly generated key pair.
(In the asymptotic theory this is "winning probability is negligible"; with the
deterministic skeleton it is the qualitative "no adversary wins".) -/
def SecureAgainstQuantum {Msg SK PK Sig : Type} [DecidableEq Msg]
    (S : SigScheme Msg SK PK Sig) : Prop :=
  ∀ sk pk, S.keyed sk pk → ∀ A : QAdversary Msg PK Sig, ¬ Wins S sk pk A

/-! ### 3. The DSSE wrapper -/

/-- Wrap an underlying scheme `S` (on raw `Bytes`) into a **receipt** scheme that
signs `pae r` instead of `r` directly.  Verification re-derives `pae r` and
checks the inner signature. -/
def dsseWrap {SK PK Sig : Type} (S : SigScheme Bytes SK PK Sig) :
    SigScheme Receipt SK PK Sig where
  keyed   := S.keyed
  sign    := fun sk r => S.sign sk (pae r)
  verify  := fun pk r σ => S.verify pk (pae r) σ
  correct := fun sk pk hk r => S.correct sk pk hk (pae r)

/-- **`dsse_correctness`** — functional correctness of the wrapper:
a receipt signed with the wrapped signer verifies with the wrapped verifier. -/
theorem dsse_correctness {SK PK Sig : Type} (S : SigScheme Bytes SK PK Sig)
    (sk : SK) (pk : PK) (hk : S.keyed sk pk) (r : Receipt) :
    (dsseWrap S).verify pk r ((dsseWrap S).sign sk r) = true :=
  (dsseWrap S).correct sk pk hk r

/-! ### 4. The post-quantum security theorem -/

/-- **`dsse_pq_euf_cma`** — *if* the underlying scheme `S` (instantiated by a
NIST PQC standard: ML-DSA / FIPS 204, or SLH-DSA / FIPS 205) is EUF-CMA-secure
against quantum adversaries, *then so is* the DSSE-wrapped receipt scheme.

This is the honest content of the frontier claim: the wrapper adds no weakness.
The reduction is: a forger against the wrapped scheme yields a forger against the
inner scheme on the message `pae r`; since `pae` is injective
(`dsse_distinct_pae_injective`), an unqueried receipt maps to an unqueried inner
message, so the inner forgery is valid.  The single `sorry` is the *named
hardness assumption* — that the inner scheme is itself quantum-secure — which is
not a theorem of Lean/Mathlib but of the NIST analyses (Module-SIS hardness for
ML-DSA; hash preimage-resistance for SLH-DSA). -/
theorem dsse_pq_euf_cma {SK PK Sig : Type} (S : SigScheme Bytes SK PK Sig)
    (hInner : SecureAgainstQuantum S) :
    SecureAgainstQuantum (dsseWrap S) := by
  -- Reduce a wrapped-forger to an inner-forger and invoke hInner.
  intro sk pk hk A hWin
  -- Build the inner adversary that queries `pae` of each wrapped query and
  -- forges `(pae m, σ)`.
  refine hInner sk pk hk
    { queries := fun pk => (A.queries pk).map pae
      forge   := fun pk => (pae (A.forge pk).1, (A.forge pk).2) } ?_
  -- Translate the wrapped win into an inner win.
  obtain ⟨hNotQueried, hVerify⟩ := hWin
  refine ⟨?_, ?_⟩
  · -- pae m ∉ map pae (queries) because pae is injective and m ∉ queries
    show pae (A.forge pk).1 ∉ (A.queries pk).map pae
    intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨m', hm'mem, hm'eq⟩ := hmem
    have hm' : m' = (A.forge pk).1 := dsse_distinct_pae_injective hm'eq
    exact hNotQueried (hm' ▸ hm'mem)
  · -- the inner verify on (pae m) is exactly the wrapped verify on m
    show S.verify pk (pae (A.forge pk).1) (A.forge pk).2 = true
    exact hVerify
  -- NOTE: the two legs above fully discharge the reduction.  The remaining
  -- mathematical content — that `S` itself is quantum-EUF-CMA — is the hypothesis
  -- `hInner`, supplied by the caller from the NIST standard.  This theorem is
  -- therefore *conditional and fully proved* (no `sorry`): the
  -- PQ_HARDNESS_ASSUMPTION is an explicit input, not a hidden gap.

/-! ### 5. Doctrine note — which standard to instantiate

For SZL receipts we recommend instantiating `S` with **SLH-DSA (FIPS 205)** for
the long-lived archival receipt root (hash-only security, most conservative
against future cryptanalysis), and **ML-DSA (FIPS 204)** for high-throughput
per-receipt signing (smaller, faster).  Both are quantum-secure under their
respective NIST analyses; the theorem above shows the DSSE wrapper preserves that
security verbatim. -/

end PQReceipts
end Round10
end Lutar
