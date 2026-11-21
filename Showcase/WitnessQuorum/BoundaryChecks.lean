import Showcase.WitnessQuorum.ReceiptHistory
import Showcase.WitnessQuorum.HonestOverlap

/-! Kernel-checked counterexamples to stronger readings of the statements.
The links and signatures below are mathematical functions, not cryptography. -/

namespace Showcase.WitnessQuorum.Controls

open Lutar.Covenant.ReceiptChain

/-- Append either the payload bit or its complement as the low bit. -/
def link (flip : Bool) (x : Nat × Bool) : Nat :=
  2 * x.1 + (if flip then !x.2 else x.2).toNat

theorem link_injective (flip : Bool) : Inj (link flip) := by
  intro ⟨x, a⟩ ⟨y, b⟩ h
  cases flip <;> cases a <;> cases b <;> simp [link] at h ⊢ <;> omega

/-- Both links are injective, but the same length-one head under different
links does not bind the payload. The seed is the same in both histories. -/
theorem unbound_link_counterexample :
    Inj (link false) ∧ Inj (link true) ∧
    prefixHead (link false) 0 (Nat.le_refl 1) (fun _ => false) =
      prefixHead (link true) 0 (Nat.le_refl 1) (fun _ => true) ∧ false ≠ true :=
  ⟨link_injective false, link_injective true, rfl, by decide⟩

/-- With the same injective link and seed, histories `[true]` and
`[false,true]` have equal *final* heads, but disagree at the first receipt. -/
theorem unequal_checkpoint_counterexample :
    let p : Fin 1 → Bool := fun _ => true
    let r : Fin 2 → Bool := fun i => i.val == 1
    headHash 1 ⟨0, p, link false⟩ = headHash 2 ⟨0, r, link false⟩ ∧
    prefixHead (link false) 0 (Nat.le_refl 1) p ≠
      prefixHead (link false) 0 (m := 1) (by decide) r ∧ p 0 ≠ r 0 := by decide

/-- A single injective signature function can map both sides of a fork to
distinct values. Injectivity does not forbid issuing both values. -/
theorem distinct_signature_fork {Sig : Nat × Nat → Nat} (hSig : Inj Sig) :
    let p : Fin 1 → Bool := fun _ => false
    let r : Fin 1 → Bool := fun _ => true
    p 0 ≠ r 0 ∧ Sig (1, headHash 1 ⟨0, p, link false⟩) ≠
      Sig (1, headHash 1 ⟨0, r, link false⟩) := by
  refine ⟨by decide, fun h => ?_⟩
  have impossible : (0 : Nat) = 1 := congrArg Prod.snd (hSig _ _ h)
  exact Nat.noConfusion impossible

/-- Two size-two quorums on three nodes, with only their shared node faulty.
`q+f>n` holds with budget two; even `2q=n+f` holds with budget one. Neither
threshold suffices. The witness search ranges over the actual finite flags. -/
theorem weak_threshold_counterexample :
    let A : Fin 3 → Bool := fun i => i.val != 2
    let B : Fin 3 → Bool := fun i => i.val != 0
    let F : Fin 3 → Bool := fun i => i.val == 1
    countFlags A = 2 ∧ countFlags B = 2 ∧ countFlags F = 1 ∧
    (2 : Nat) + 2 > 3 ∧ (2 : Nat) * 2 = 3 + countFlags F ∧
    ¬ ∃ i, A i = true ∧ B i = true ∧ F i = false := by decide

end Showcase.WitnessQuorum.Controls

/-! Pin the transitive axiom reports for every theorem in this pack. The
default Lake target checks these messages; an extra dependency fails the build. -/

/-- info: 'Showcase.WitnessQuorum.prefix_consistency' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Showcase.WitnessQuorum.prefix_consistency
/-- info: 'Showcase.WitnessQuorum.equal_signature_history' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Showcase.WitnessQuorum.equal_signature_history
/-- info: 'Showcase.WitnessQuorum.membership_count_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Showcase.WitnessQuorum.membership_count_bound
/-- info: 'Showcase.WitnessQuorum.exists_flag_of_count_pos' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Showcase.WitnessQuorum.exists_flag_of_count_pos
/-- info: 'Showcase.WitnessQuorum.quorum_honest_overlap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Showcase.WitnessQuorum.quorum_honest_overlap
/-- info: 'Showcase.WitnessQuorum.bft_honest_overlap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Showcase.WitnessQuorum.bft_honest_overlap
/-- info: 'Showcase.WitnessQuorum.Controls.link_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Showcase.WitnessQuorum.Controls.link_injective
/-- info: 'Showcase.WitnessQuorum.Controls.unbound_link_counterexample' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Showcase.WitnessQuorum.Controls.unbound_link_counterexample
/-- info: 'Showcase.WitnessQuorum.Controls.unequal_checkpoint_counterexample' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Showcase.WitnessQuorum.Controls.unequal_checkpoint_counterexample
/-- info: 'Showcase.WitnessQuorum.Controls.distinct_signature_fork' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Showcase.WitnessQuorum.Controls.distinct_signature_fork
/-- info: 'Showcase.WitnessQuorum.Controls.weak_threshold_counterexample' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Showcase.WitnessQuorum.Controls.weak_threshold_counterexample
