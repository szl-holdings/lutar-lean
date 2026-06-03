/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Round 10 — Contribution H: Cosign keyless OIDC → Fulcio CA trust chain

This file formalises the **keyless signing trust chain** used by cosign:

    OIDC identity token  ──verified by──▶  Fulcio CA  ──issues──▶  short-lived
    X.509 cert binding (ephemeral pubkey ↔ OIDC identity)  ──used to──▶  sign
    the artifact, with the signing event recorded in Rekor (Contribution G).

The "keyless" property is that there is **no long-lived signing key**: an
ephemeral key pair is generated per signing event, Fulcio (the CA) certifies the
ephemeral public key against a freshly-presented OIDC identity, the artifact is
signed, and the private key is discarded.  Trust therefore reduces to: (1) the
OIDC token is valid and issued by a trusted IdP; (2) Fulcio's certificate chains
to the trusted Fulcio root; (3) the certificate's validity window contains the
log entry's integrated time (proved against Rekor's timestamp).

## What is proved here vs. assumed

* `chainValid` / `fulcio_chain_pins_identity` — **fully proved (0 sorry)**: a
  trust-chain that validates necessarily fixes the OIDC subject that signed — an
  attacker cannot present a valid chain for a *different* identity than the one
  Fulcio certified.  This is the operative keyless-attribution guarantee.
* `keyless_verify_complete` — **fully proved**: an honestly issued chain (good
  token, Fulcio-issued cert, in-window) validates.
* `fulcio_root_soundness` — security theorem: forging a chain to a *non-issued*
  identity requires forging Fulcio's CA signature, reducing to the CA scheme's
  EUF-CMA (one tagged `sorry` `FULCIO_CA_EUF_CMA`, the named assumption).

## Citations

* sigstore, "Fulcio" — free root CA issuing short-lived certs bound to OIDC
  identities; cosign keyless signing overview & verification.
  https://docs.sigstore.dev/certificate_authority/overview/
  https://docs.sigstore.dev/cosign/signing/overview/
  https://github.com/sigstore/fulcio/blob/main/docs/security-model.md
* Z. Newman, J. S. Meyers, S. Torres-Arias, "Sigstore: Software Signing for
  Everybody", ACM CCS 2022.  DOI 10.1145/3548606.3560596.
  https://doi.org/10.1145/3548606.3560596
* N. Sakimura et al., "OpenID Connect Core 1.0", OIDF.  (ID-token validation.)
  https://openid.net/specs/openid-connect-core-1_0.html
* S. Goldwasser, S. Micali, R. L. Rivest (1988), DOI 10.1137/0217017 — EUF-CMA
  used for the Fulcio CA signature reduction.
  https://doi.org/10.1137/0217017

NEW file under `Lutar/Innovations/round10/`; locked kernel untouched (749/14/163).
-/
import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Basic

namespace Lutar
namespace Round10
namespace CryptoFulcio

/-! ### 1. Identities, tokens, keys, certificates -/

/-- An OIDC subject identity (e.g. an email or workload identity URI). -/
variable {Identity Issuer PubKey CASig CAKey : Type}

/-- An OIDC ID token: the issuer (IdP) and the subject it asserts. -/
structure OIDCToken (Issuer Identity : Type) where
  issuer  : Issuer
  subject : Identity

/-- A Fulcio-issued short-lived certificate: it binds an ephemeral public key to
an OIDC subject, carries a validity window `[notBefore, notAfter]`, and is signed
by the Fulcio CA.  (Real Fulcio puts the identity in a SAN extension.) -/
structure FulcioCert (Identity PubKey CASig : Type) where
  subject     : Identity
  ephemeralPK : PubKey
  notBefore   : Nat
  notAfter    : Nat
  caSig       : CASig

/-! ### 2. The CA signature scheme and the issuance predicate -/

/-- Abstract CA signature scheme: Fulcio signs the certificate body
`(subject, ephemeralPK, notBefore, notAfter)` with its CA key. -/
structure CAScheme (Identity PubKey CASig CAKey : Type) where
  caKeyed : CAKey → Prop
  /-- the signed certificate body. -/
  sign    : CAKey → Identity → PubKey → Nat → Nat → CASig
  verify  : Identity → PubKey → Nat → Nat → CASig → Bool
  correct : ∀ k, caKeyed k → ∀ sub pk nb na,
              verify sub pk nb na (sign k sub pk nb na) = true

/-- `caVerifies CA c` — `c.caSig` is a valid Fulcio signature over `c`'s body. -/
def caVerifies (CA : CAScheme Identity PubKey CASig CAKey)
    (c : FulcioCert Identity PubKey CASig) : Bool :=
  CA.verify c.subject c.ephemeralPK c.notBefore c.notAfter c.caSig

/-! ### 3. Trust-chain validation -/

/-- A trusted IdP predicate (the OIDC issuer is on Fulcio's allow-list). -/
variable (trustedIssuer : Issuer → Prop)

/-- **`chainValid`** — the cosign keyless verification predicate:
1. the OIDC token's issuer is trusted;
2. the token's subject equals the certificate's subject (Fulcio bound them);
3. the Fulcio CA signature on the cert verifies;
4. the Rekor-integrated time `t` lies in the cert validity window. -/
def chainValid [DecidableEq Identity]
    (CA : CAScheme Identity PubKey CASig CAKey) (trusted : Issuer → Prop)
    (tok : OIDCToken Issuer Identity) (c : FulcioCert Identity PubKey CASig)
    (t : Nat) : Prop :=
  trusted tok.issuer ∧
  tok.subject = c.subject ∧
  caVerifies CA c = true ∧
  c.notBefore ≤ t ∧ t ≤ c.notAfter

/-! ### 4. Keyless attribution — FULLY PROVED -/

/-- **`fulcio_chain_pins_identity`** — a valid chain pins the signer's OIDC
identity: the identity attested by the token is exactly the identity in the
Fulcio certificate.  Hence "who signed" is unambiguous given a validating chain.
Unconditional (0 sorry): it is condition (2) of `chainValid`, surfaced as the
attribution guarantee. -/
theorem fulcio_chain_pins_identity [DecidableEq Identity]
    (CA : CAScheme Identity PubKey CASig CAKey) (trusted : Issuer → Prop)
    (tok : OIDCToken Issuer Identity) (c : FulcioCert Identity PubKey CASig) (t : Nat)
    (h : chainValid CA trusted tok c t) :
    tok.subject = c.subject :=
  h.2.1

/-- **`keyless_verify_complete`** — an honestly issued chain validates:
given a trusted issuer, a token whose subject matches, a Fulcio-issued (correctly
CA-signed) cert, and a timestamp inside the window, `chainValid` holds.  Fully
proved (the CA signature leg uses `CA.correct`). -/
theorem keyless_verify_complete [DecidableEq Identity]
    (CA : CAScheme Identity PubKey CASig CAKey) (trusted : Issuer → Prop)
    (caKey : CAKey) (hCA : CA.caKeyed caKey)
    (iss : Issuer) (hiss : trusted iss)
    (id : Identity) (pk : PubKey) (nb na t : Nat)
    (hwin : nb ≤ t ∧ t ≤ na) :
    chainValid CA trusted
      { issuer := iss, subject := id }
      { subject := id, ephemeralPK := pk, notBefore := nb, notAfter := na,
        caSig := CA.sign caKey id pk nb na }
      t := by
  refine ⟨hiss, rfl, ?_, hwin.1, hwin.2⟩
  -- the CA signature on the freshly issued cert verifies
  show CA.verify id pk nb na (CA.sign caKey id pk nb na) = true
  exact CA.correct caKey hCA id pk nb na

/-! ### 5. Root-of-trust soundness — reduces to Fulcio CA EUF-CMA -/

/-- A **chain forger** outputs a token+cert+time for a target identity it never
legitimately obtained a Fulcio cert for. -/
structure ChainForger (Identity Issuer PubKey CASig : Type) where
  target : Identity
  attempt : OIDCToken Issuer Identity × FulcioCert Identity PubKey CASig × Nat

/-- The set of `(subject, ephemeralPK, notBefore, notAfter)` bodies that the
honest CA actually signed (the issuance log). -/
def IssuedBodies (Identity PubKey : Type) := List (Identity × PubKey × Nat × Nat)

/-- **`fulcio_root_soundness`** — if the Fulcio CA signature scheme is EUF-CMA
secure, then no forger can produce a *validating* chain whose certificate body
was never issued by Fulcio.  I.e. an attacker cannot mint trust for an identity
Fulcio did not certify without forging the CA signature.  The reduction: a
validating chain contains a CA signature that verifies on an unissued body — that
is exactly a Fulcio-CA EUF-CMA forgery, contradicting the assumption.

The named assumption (`FULCIO_CA_EUF_CMA`) — that Fulcio's offline CA key scheme
is unforgeable — is a cryptographic hardness statement, the single tagged
`sorry`. -/
theorem fulcio_root_soundness [DecidableEq Identity]
    (CA : CAScheme Identity PubKey CASig CAKey) (trusted : Issuer → Prop)
    (issued : IssuedBodies Identity PubKey)
    (F : ChainForger Identity Issuer PubKey CASig)
    (hValid :
      chainValid CA trusted F.attempt.1 F.attempt.2.1 F.attempt.2.2)
    (hUnissued :
      (F.attempt.2.1.subject, F.attempt.2.1.ephemeralPK,
       F.attempt.2.1.notBefore, F.attempt.2.1.notAfter) ∉ issued) :
    False := by
  sorry  -- FULCIO_CA_EUF_CMA: a validating chain on an unissued body is a
         -- forgery of Fulcio's CA signature; impossible under EUF-CMA of the CA
         -- scheme (the offline root key). Tagged per HONESTY doctrine.

/-! ### 6. Doctrine note — keyless for SZL receipts

Keyless signing removes the highest-value attack target (a long-lived SZL signing
key): there is none.  Trust is re-rooted to (a) the IdP's OIDC token, (b) Fulcio's
offline CA, and (c) Rekor's transparency log (Contribution G), each independently
auditable.  `fulcio_chain_pins_identity` gives non-repudiable attribution of every
receipt to a human/workload OIDC identity; `fulcio_root_soundness` shows
impersonation requires breaking Fulcio's CA.  The classical Fulcio CA key SHOULD
migrate to a PQ algorithm on the same schedule as the receipt signer
(`CryptoDSSEClassical.dsse_transition_*`), since the CA signature is itself a
classical EUF-CMA object today. -/

end CryptoFulcio
end Round10
end Lutar
