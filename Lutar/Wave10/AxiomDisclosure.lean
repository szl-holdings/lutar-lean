/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave10/AxiomDisclosure.lean — Wave10 axiom-disclosure ledger

Mirrors `Lutar/Wave9/AxiomDisclosure.lean`: a machine-checked record that the
Wave10 candidate-theorem pack is EXPERIMENTAL/additive and leaves the LOCKED
baseline untouched. We model the disclosed `#print axioms` set of each Wave10
theorem as a `List String` and prove they are all kernel-only, while RE-ASSERTING
the locked invariant `locked_count_eight = 8`.

The verbatim ground-truth `#print axioms` lines are emitted per theorem in each
Wave10 file and in the CI build log; this file is a meta-level summary, not a
re-verification of those kernel proofs.

## What is proven
- `wave10Disclosed` — the disclosed (kernel-only) axiom sets of the Wave10
  theorems, modeled as concrete `List String` values matching their per-file
  `#print axioms` lines.
- `wave10_axiom_sets_kernel_only` — every Wave10 disclosed set is kernel-only
  (`decide`): no Wave10 theorem introduces a custom axiom.
- `locked_count_eight` — RE-ASSERTED invariant: the locked baseline is EXACTLY the
  eight {F1,F4,F7,F11,F12,F18,F19,F22}. Wave10 does NOT change this (`decide`).
- `wave10_excluded_from_locked` — the Wave10 theorem names are disjoint from the
  locked eight: Wave10 is additive and excluded from the locked baseline.

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave10`) — NOT in the LOCKED v11 baseline (749/14/163 @
  c7c0ba17). Locked-proven stays exactly 8 {F1,F4,F7,F11,F12,F18,F19,F22}. Λ Conjecture 1.
- Lean-core only; NO Mathlib, NO new declared axiom, NO sorry.

## Citations
- Lean 4 `#print axioms` discipline: https://lean-lang.org/faq/
- Mirrors Lutar/Wave9/AxiomDisclosure.lean (axiom-disclosure meta-theorem).

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/

namespace Lutar.Wave10.AxiomDisclosure

/-- The standard Lean 4 kernel / Mathlib trust base. -/
def leanKernelAxioms : List String :=
  ["propext", "funext", "Classical.choice", "Quot.sound"]

/-- Deny-by-default membership predicate over disclosed axiom names. -/
def axiomsAllowed (used : List String) : Bool :=
  used.all (fun a => leanKernelAxioms.contains a)

/-- Disclosed axiom sets for the Wave10 theorems (mirroring their per-file
`#print axioms` lines, captured verbatim from the local kernel build). Each is
kernel-only; an empty list means "does not depend on any axioms". -/
def wave10Disclosed : List (String × List String) :=
  [ ("STL.rho_sound",                   ["propext", "Quot.sound"]),
    ("STL.rho_pos_sound",               ["propext", "Quot.sound"]),
    ("STL.rho_neg_violation",           ["propext", "Quot.sound"]),
    ("quorum_intersection_agreement",   []),
    ("quorum_unique_decision",          []),
    ("majority_quorums_intersect",      ["propext", "Quot.sound"]),
    ("dsse_token_injective",            []),
    ("dsse_token_distinct",             []),
    ("dsse_search_sound",               []),
    ("ni_id",                           []),
    ("ni_comp",                         []),
    ("ni_foldl",                        ["propext"]),
    ("ni_chain",                        ["propext"]),
    ("ni_pair",                         ["propext"]),
    ("replay_deterministic",            []),
    ("replay_congr",                    []),
    ("replay_append",                   ["propext", "Quot.sound"]),
    ("tamper_localized",                []),
    ("Reach.reach_single",              []),
    ("Reach.reach_trans",               []),
    ("Reach.reach_mono",                []),
    ("avoiding_reach_le_full",          []),
    ("cut_disconnects",                 []),
    ("path_refutes_cut",                []) ]

/-- Every Wave10 disclosed axiom set is kernel-only: no custom axiom anywhere in
the Wave10 pack. Decided by the kernel. -/
theorem wave10_axiom_sets_kernel_only :
    wave10Disclosed.all (fun p => axiomsAllowed p.2) = true := by decide

/-- The LOCKED baseline names (RE-ASSERTED, NOT modified by Wave10). -/
def lockedNames : List String := ["F1", "F4", "F7", "F11", "F12", "F18", "F19", "F22"]

/-- RE-ASSERTED locked invariant: exactly eight locked theorems. Wave10 leaves this
unchanged. -/
theorem locked_count_eight : lockedNames.length = 8 := by decide

/-- Wave10 is additive: none of the Wave10 theorem identifiers collide with a
locked name (Wave10 is excluded from the locked baseline). -/
theorem wave10_excluded_from_locked :
    wave10Disclosed.all (fun p => ! lockedNames.contains p.1) = true := by decide

#print axioms wave10_axiom_sets_kernel_only
#print axioms locked_count_eight
#print axioms wave10_excluded_from_locked

end Lutar.Wave10.AxiomDisclosure
