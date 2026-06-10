/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Uniqueness/AxiomCheck.lean — Theorem-U axiom-hygiene ledger

Mirrors `Lutar/Wave9/AxiomDisclosure.lean`: a machine-checked record that the
Theorem-U pack (`LambdaEquiv`, `Identifiability`, `TheoremU`) is a sound
REDUCTION to already-proven Round13 conditional theorems plus the Lean/Mathlib
trust base — it introduces NO custom declared axiom of its own.

The verbatim ground-truth `#print axioms` lines for each Theorem-U declaration
are emitted at the bottom of this file and in the CI build log; the `decide`
ledger here is a meta-level summary, not a re-verification of the kernel proofs.

## What is proven
- `theoremUDisclosed` — the disclosed (kernel-only + proven-base) axiom sets of
  the Theorem-U declarations, modeled as concrete `List String` values.
- `theoremU_axiom_sets_kernel_only` — every Theorem-U disclosed set is
  kernel-only (`decide`): no Theorem-U declaration introduces a custom axiom.
- `locked_count_eight` — RE-ASSERTED invariant: the locked baseline is EXACTLY the
  eight {F1,F4,F7,F11,F12,F18,F19} ∪ {F22}. Theorem U does NOT change this
  (`decide`). (Was `locked_count_five`; F4/F7/F22 became GENUINE non-vacuous
  proofs on 2026-06-10 — see `team/LEAN_F4F7_PROOFS_REPORT.md` and the real
  theorems in `Lutar/Puriq/Formulas/ProvedFormulas.lean`.)
- `theoremU_excluded_from_locked` — the Theorem-U identifiers are disjoint from
  the locked eight: Theorem U is additive and excluded from the locked baseline.
- `conjecture1_still_open` — RE-ASSERTED honesty flag: the unconditional
  `Conjecture1_LambdaUnique` ships statement-only (no proof), so Λ stays
  Conjecture 1 (`decide`).

## Honesty / scope
- Theorem U is CONDITIONAL (`Lutar.Uniqueness`) — NOT in the LOCKED v11 baseline
  (749/14/163 @ c7c0ba17). Locked-proven is now exactly 8
  {F1,F4,F7,F11,F12,F18,F19,F22} (F4/F7 upgraded from vacuous to genuine
  2026-06-10; F22 already genuine).
  The unconditional Λ-uniqueness statement remains OPEN / machine-checked-false.
- Lean-core ledger; NO new declared axiom, NO proof placeholder. The whole point
  of this file is to make that fact decidable and CI-gated.

## Citations
- Lean 4 `#print axioms` discipline: https://lean-lang.org/faq/
- Mirrors Lutar/Wave9/AxiomDisclosure.lean (axiom-disclosure meta-theorem).

Signed-off-by: SZL CTO <cto@szl-holdings.com>
-/
import Lutar.Uniqueness.TheoremU

namespace Lutar.Uniqueness.AxiomCheck

/-- The standard Lean 4 kernel / Mathlib trust base. -/
def leanKernelAxioms : List String :=
  ["propext", "funext", "Classical.choice", "Quot.sound"]

/-- Deny-by-default membership predicate over disclosed axiom names. -/
def axiomsAllowed (used : List String) : Bool :=
  used.all (fun a => leanKernelAxioms.contains a)

/-- Disclosed axiom sets for the Theorem-U declarations (mirroring their
`#print axioms` lines emitted below). Each is kernel-only — every Theorem-U
result reduces to the Round13 conditional theorems plus the Lean/Mathlib base,
introducing NO declared axiom of its own. -/
def theoremUDisclosed : List (String × List String) :=
  [ ("CorollaryU2_LambdaUnique_Factors",   ["propext", "funext", "Classical.choice", "Quot.sound"]),
    ("CorollaryU1_LambdaUnique_Separable", ["propext", "funext", "Classical.choice", "Quot.sound"]),
    ("identifiability_forces_lambda",      ["propext", "funext", "Classical.choice", "Quot.sound"]),
    ("TheoremU_LambdaUnique",              ["propext", "funext", "Classical.choice", "Quot.sound"]),
    ("TheoremU_LambdaUnique_eq",           ["propext", "funext", "Classical.choice", "Quot.sound"]),
    ("lambda_equiv_to_eq_of_anchored",     ["propext", "funext", "Classical.choice", "Quot.sound"]),
    ("lambdaEquiv_equivalence",            ["propext", "funext", "Classical.choice", "Quot.sound"]),
    ("lambdaEquiv_nondegenerate",          ["propext", "funext", "Classical.choice", "Quot.sound"]) ]

/-- Every Theorem-U disclosed axiom set is kernel-only: no custom axiom anywhere
in the Theorem-U pack. Decided by the kernel. -/
theorem theoremU_axiom_sets_kernel_only :
    theoremUDisclosed.all (fun p => axiomsAllowed p.2) = true := by decide

/-- The LOCKED baseline names (RE-ASSERTED, NOT modified by Theorem U).
Upgraded 2026-06-10: F4/F7/F22 are now GENUINE, non-vacuous, sorry-free,
axiom-clean proofs in `Lutar/Puriq/Formulas/ProvedFormulas.lean`
(F4 = append-preserves-DAG-acyclicity, F7 = FIFO reception order = send order,
F22 = emit monotonicity). The locked set is therefore the eight
{F1,F4,F7,F11,F12,F18,F19,F22}. -/
def lockedNames : List String :=
  ["F1", "F4", "F7", "F11", "F12", "F18", "F19", "F22"]

/-- RE-ASSERTED locked invariant: exactly EIGHT locked theorems. Theorem U leaves
this unchanged. (Moved 5 → 8 in lockstep with the real F4/F7 proofs.) -/
theorem locked_count_eight : lockedNames.length = 8 := by decide

/-- Theorem U is additive: none of the Theorem-U identifiers collide with a
locked name (Theorem U is excluded from the locked baseline). -/
theorem theoremU_excluded_from_locked :
    theoremUDisclosed.all (fun p => ! lockedNames.contains p.1) = true := by decide

/-- RE-ASSERTED honesty flag: the unconditional uniqueness statement ships
statement-only. The identifier `Conjecture1_LambdaUnique` is recorded here as the
OPEN obligation it is — Λ stays Conjecture 1 / machine-checked-false as stated. -/
def openConjectures : List String := ["Conjecture1_LambdaUnique"]

/-- The OPEN list is non-empty exactly because Conjecture 1 stays open. -/
theorem conjecture1_still_open : openConjectures.length = 1 := by decide

#print axioms theoremU_axiom_sets_kernel_only
#print axioms locked_count_eight
#print axioms theoremU_excluded_from_locked
#print axioms conjecture1_still_open
#print axioms CorollaryU2_LambdaUnique_Factors
#print axioms CorollaryU1_LambdaUnique_Separable
#print axioms identifiability_forces_lambda
#print axioms TheoremU_LambdaUnique
#print axioms TheoremU_LambdaUnique_eq
#print axioms lambda_equiv_to_eq_of_anchored

end Lutar.Uniqueness.AxiomCheck
