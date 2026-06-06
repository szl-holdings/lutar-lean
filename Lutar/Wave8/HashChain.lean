/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave8/HashChain.lean — M2: Hash-Chain Append-Only Consistency

A hash chain links entry `i` to its predecessor via `linkᵢ = H (prevHash, payloadᵢ)`.
Under the standard collision-resistance idealization (`H` injective), two chains
of the same length with equal *head hashes* (roots) must agree on every entry.
Equivalently: there is no way to rewrite any entry without either changing the
published root or exhibiting a hash collision — the append-only / tamper-evident
guarantee behind the Cannonico audit ledger.

## What is proven
- `headHash` — the fold producing the published root of a length-`n+1` chain.
- `hashchain_consistency` — equal roots + injective `H` ⟹ pointwise-equal entries
  (by induction on chain length; uses ONLY the injectivity hypothesis).
- `hashchain_tamper_evident` — contrapositive: if any entry differs, the roots
  differ (you cannot rewrite history undetected).

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave8`) — NOT in the LOCKED v11 baseline. Locked-proven
  stays exactly 5 {F1,F11,F12,F18,F19}. Λ untouched (Conjecture 1).
- Collision resistance is modeled as the HYPOTHESIS `Injective H` (idealized
  random-oracle assumption), passed explicitly — NOT a new global `axiom`.
  This is the standard formalization posture (cf. RFC 6962 audit paths).
- Lean-core only: no Mathlib import. `Inj` is a local definition. NO open obligation.
- Scope note: proves keyword/entry distinguishability under an ideal injective
  hash; it does NOT prove SHA-256's concrete collision resistance.

## Citations
- RFC 6962 (Certificate Transparency Merkle audit paths):
  https://datatracker.ietf.org/doc/html/rfc6962
- Certificate Transparency append-only model:
  https://certificate.transparency.dev/howctworks/
- GlassDB (VLDB 2023), append-only verifiable ledger:
  https://www.vldb.org/pvldb/vol16/p1359-ooi.pdf

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/

namespace Lutar.Wave8.HashChain

/-- Local, Mathlib-free injectivity predicate (collision-resistance idealization). -/
def Inj {α β : Type} (f : α → β) : Prop := ∀ ⦃a b : α⦄, f a = f b → a = b

/-- A hash chain over a payload type `P` and hash type `Hsh`:
  - `seed`   : the genesis hash (hash of the empty prefix);
  - `payload`: the payload at each of the `n` positions;
  - `H`      : the linking hash `H (prevHash, payload) = nextHash`. -/
structure Chain (P Hsh : Type) (n : Nat) where
  seed    : Hsh
  payload : Fin n → P
  H       : Hsh × P → Hsh

/-- The published head hash of a chain: fold `H` over the payloads from the seed. -/
def headHash {P Hsh : Type} : (n : Nat) → Chain P Hsh n → Hsh
  | 0,     c => c.seed
  | n + 1, c =>
      -- hash of (root of first n entries, last payload)
      c.H (headHash n
            { seed := c.seed, payload := fun i => c.payload i.castSucc, H := c.H },
           c.payload (Fin.last n))

/-- M2 — Append-only consistency. Two chains sharing the same seed and the same
injective linking hash `H`, whose published head hashes are equal, must carry
identical payloads at every position. Induction on the chain length; the only
nontrivial step peels one `H` via injectivity. -/
theorem hashchain_consistency {P Hsh : Type}
    (H : Hsh × P → Hsh) (hH : Inj H) (seed : Hsh) :
    ∀ (n : Nat) (p q : Fin n → P),
      headHash n { seed := seed, payload := p, H := H }
        = headHash n { seed := seed, payload := q, H := H } →
      ∀ i, p i = q i := by
  intro n
  induction n with
  | zero =>
      intro p q _ i; exact (Fin.elim0 i)
  | succ n ih =>
      intro p q hroot i
      -- Peel the outer H using injectivity.
      have hpair :
          (headHash n { seed := seed, payload := fun j => p j.castSucc, H := H },
           p (Fin.last n))
            = (headHash n { seed := seed, payload := fun j => q j.castSucc, H := H },
               q (Fin.last n)) := by
        apply hH
        simpa [headHash] using hroot
      have hroot' :
          headHash n { seed := seed, payload := fun j => p j.castSucc, H := H }
            = headHash n { seed := seed, payload := fun j => q j.castSucc, H := H } :=
        (Prod.ext_iff.mp hpair).1
      have hlast : p (Fin.last n) = q (Fin.last n) := (Prod.ext_iff.mp hpair).2
      -- Recurse on the truncated chains.
      have hrec := ih (fun j => p j.castSucc) (fun j => q j.castSucc) hroot'
      -- Case split: is `i` the last index or an earlier one?
      exact Fin.lastCases hlast hrec i

/-- M2 corollary — tamper-evidence (contrapositive). If two same-seed chains
under the same injective `H` differ at some position, their published head
hashes differ: history cannot be rewritten without detection. -/
theorem hashchain_tamper_evident {P Hsh : Type}
    (H : Hsh × P → Hsh) (hH : Inj H) (seed : Hsh)
    (n : Nat) (p q : Fin n → P) (i : Fin n) (hne : p i ≠ q i) :
    headHash n { seed := seed, payload := p, H := H }
      ≠ headHash n { seed := seed, payload := q, H := H } := by
  intro hroot
  exact hne (hashchain_consistency H hH seed n p q hroot i)

#print axioms hashchain_consistency
#print axioms hashchain_tamper_evident

end Lutar.Wave8.HashChain
