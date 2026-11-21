import Lutar.Wave10.QuorumIntersection

/-! Finite cardinality for membership and fault flags. This is not the
Mathlib `Finset` theorem and does not model votes, messages, or finality. -/

namespace Showcase.WitnessQuorum

open Lutar.Wave10.QuorumIntersection (Intersecting)

/-- Each index in the finite universe contributes exactly one Boolean bit. -/
def countFlags : {n : Nat} → (Fin n → Bool) → Nat
  | 0, _ => 0
  | n + 1, flags => (flags 0).toNat + countFlags (n := n) (fun i => flags i.succ)

def honestMember {n : Nat} (A B F : Fin n → Bool) (i : Fin n) : Bool :=
  A i && B i && !(F i)

/-- Each node pays for at most one ordinary membership; a double membership
is covered by a fault or by a genuine nonfaulty intersection member. -/
theorem membership_count_bound {n : Nat} (A B F : Fin n → Bool) :
    countFlags A + countFlags B ≤ n + countFlags F + countFlags (honestMember A B F) := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    have tail : countFlags (fun i : Fin n => A i.succ) + countFlags (fun i : Fin n => B i.succ) ≤
        n + countFlags (fun i : Fin n => F i.succ) +
          countFlags (fun i : Fin n => honestMember A B F i.succ) :=
      ih (fun i => A i.succ) (fun i => B i.succ) (fun i => F i.succ)
    have point : (A 0).toNat + (B 0).toNat ≤
        1 + (F 0).toNat + (honestMember A B F 0).toNat := by
      unfold honestMember
      cases A 0 <;> cases B 0 <;> cases F 0 <;> decide
    simp only [countFlags]
    omega

/-- Extract an actual finite index, not just a positive arithmetic remainder. -/
theorem exists_flag_of_count_pos {n : Nat} (flags : Fin n → Bool) (hp : 0 < countFlags flags) :
    ∃ i, flags i = true := by
  induction n with
  | zero => simp [countFlags] at hp
  | succ n ih =>
    cases h : flags 0 with
    | true => exact ⟨0, h⟩
    | false =>
      have ht : 0 < countFlags (fun i : Fin n => flags i.succ) := by
        simpa [countFlags, h] using hp
      obtain ⟨i, hi⟩ := ih _ ht
      exact ⟨i.succ, hi⟩

/-- The strict threshold forces one node in both quorums outside the fault set. -/
theorem quorum_honest_overlap {n q f : Nat} (A B F : Fin n → Bool)
    (ha : q ≤ countFlags A) (hb : q ≤ countFlags B) (hf : countFlags F ≤ f)
    (threshold : 2 * q > n + f) : ∃ i, A i = true ∧ B i = true ∧ F i = false := by
  have bound := membership_count_bound A B F
  obtain ⟨i, hi⟩ := exists_flag_of_count_pos (honestMember A B F) (by omega)
  exact ⟨i, by simpa [honestMember, Bool.and_assoc] using hi⟩

/-- The `3f+1` population and `2f+1` quorum size supply the threshold without
another assumption. Wave 10's `Intersecting` unfolds to an honest index witness. -/
theorem bft_honest_overlap (f : Nat) (A B F : Fin (3 * f + 1) → Bool)
    (ha : 2 * f + 1 ≤ countFlags A) (hb : 2 * f + 1 ≤ countFlags B) (hf : countFlags F ≤ f) :
    Intersecting (fun i => A i = true) (fun i => B i = true ∧ F i = false) :=
  quorum_honest_overlap A B F ha hb hf (by omega)

end Showcase.WitnessQuorum
