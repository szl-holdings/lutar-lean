import Mathlib.Tactic
import Lutar.Composition.TH1_Composition

/-!
# R1Tests.lean
## Decidable Tests for R1 Composition Theorems

**Doctrine v6** — Canonical scanner reference.  
**Guarantee**: all tests use `decide` or `rfl`; no `sorry`.

Five concrete tests that exercise the R1 composition framework via
decidable evaluation. Each test is a `#check`-able proposition that
evaluates by kernel reduction alone.
-/

namespace Lutar.Composition.Tests

open Lutar.Composition

/-! ## Test 1: DoctrineLabel ordering is decidable -/

/-- Test 1: Bot ≤ L1 is decidably true. -/
theorem test1_bot_le_l1 : DoctrineLabel.Bot ≤ DoctrineLabel.L1 := by
  decide

/-! ## Test 2: Label ordering is NOT reflexively violated -/

/-- Test 2: L2 is not ≤ L1 (downgrade is rejected). -/
theorem test2_l2_not_le_l1 : ¬ (DoctrineLabel.L2 ≤ DoctrineLabel.L1) := by
  decide

/-! ## Test 3: DoctrinePredicate holds for exact match -/

/-- Test 3: DoctrinePredicate L2 L2 holds (threshold = label). -/
theorem test3_doctrine_predicate_exact :
    DoctrinePredicate DoctrineLabel.L2 DoctrineLabel.L2 := by
  decide

/-! ## Test 4: Composition of two L2-locked systems is L2-locked -/

/-- Build a concrete L2-locked system at threshold L1. -/
def exampleSystem : LutarSystem DoctrineLabel.L1 where
  inputLabel  := DoctrineLabel.L1
  outputLabel := DoctrineLabel.L2
  inputOk     := by decide
  outputOk    := by decide
  noDowngrade := by decide

/-- Test 4: The output of compose inherits the correct labels. -/
theorem test4_compose_labels :
    let S₁ := exampleSystem
    let S₂ := exampleSystem
    -- S₂.input = L1, S₁.output = L2; not compatible (L2 ≤ L1 is false)
    -- Use a system where output = input = L1 for compatibility
    let S_id : LutarSystem DoctrineLabel.L1 := {
      inputLabel  := DoctrineLabel.L1
      outputLabel := DoctrineLabel.L1
      inputOk     := by decide
      outputOk    := by decide
      noDowngrade := by decide
    }
    let h : Compatible S_id exampleSystem := by decide
    (compose S_id exampleSystem h).inputLabel = DoctrineLabel.L1 ∧
    (compose S_id exampleSystem h).outputLabel = DoctrineLabel.L2 := by
  constructor
  · rfl
  · rfl

/-! ## Test 5: Composition preserves doctrine — concrete instance -/

/-- Test 5: `composition_preserves_doctrine` holds on concrete systems
    at threshold `L1`, with S_id composed with exampleSystem. -/
theorem test5_composition_preserves_doctrine_concrete :
    let th := DoctrineLabel.L1
    let S_id : LutarSystem th := {
      inputLabel  := DoctrineLabel.L1
      outputLabel := DoctrineLabel.L1
      inputOk     := by decide
      outputOk    := by decide
      noDowngrade := by decide
    }
    let S_up : LutarSystem th := {
      inputLabel  := DoctrineLabel.L1
      outputLabel := DoctrineLabel.L2
      inputOk     := by decide
      outputOk    := by decide
      noDowngrade := by decide
    }
    let h : Compatible S_id S_up := by decide
    DoctrinePredicate (compose S_id S_up h).inputLabel th ∧
    DoctrinePredicate (compose S_id S_up h).outputLabel th ∧
    (compose S_id S_up h).inputLabel ≤ (compose S_id S_up h).outputLabel := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

end Lutar.Composition.Tests
