import Lutar.Covenant.ReceiptChain

/-! Conditional binding of linear receipt histories. Both histories use one
link function and seed. No concrete hash, signer, or network is verified. -/

namespace Showcase.WitnessQuorum

open Lutar.Covenant.ReceiptChain

/-- Recompute the original linear fold after restricting receipts to `[0,m)`. -/
def prefixHead {P S : Type} (H : S × P → S) (seed : S)
    {m n : Nat} (hm : m ≤ n) (p : Fin n → P) : S :=
  headHash m ⟨seed, fun i => p (i.castLE hm), H⟩

/-- Compare heads at the same checkpoint, even when the full histories have
different lengths. Nothing is asserted about receipts after that checkpoint. -/
theorem prefix_consistency {P S : Type} (H : S × P → S) (hH : Inj H) (seed : S)
    {m n₁ n₂ : Nat} (hm₁ : m ≤ n₁) (hm₂ : m ≤ n₂)
    (p : Fin n₁ → P) (r : Fin n₂ → P)
    (heq : prefixHead H seed hm₁ p = prefixHead H seed hm₂ r) :
    ∀ i : Fin m, p (i.castLE hm₁) = r (i.castLE hm₂) :=
  chain_consistency H hH seed m _ _ heq

/-- An identical signature value over `(length, head)` binds length and
payloads. The proof of length equality itself transports each `Fin` index.
An injective signer is not a signer that refuses to sign two distinct records. -/
theorem equal_signature_history {P S : Type} (H : S × P → S) (hH : Inj H) (seed : S)
    {Sig : Nat × S → Nat} (hSig : Inj Sig) {n m : Nat} (p : Fin n → P) (r : Fin m → P)
    (heq : Sig (n, headHash n ⟨seed, p, H⟩) = Sig (m, headHash m ⟨seed, r, H⟩)) :
    ∃ h : n = m, ∀ i : Fin n, p i = r (i.cast h) := by
  obtain ⟨hlen, _⟩ := countersign_length_binding hSig heq
  subst m
  exact ⟨rfl, countersigned_head_consistency H hH seed hSig n p r heq⟩

end Showcase.WitnessQuorum
