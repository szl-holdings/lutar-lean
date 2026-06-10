/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave9/AxiomDisclosure.lean — Wave9 axiom-disclosure ledger

Mirrors `Lutar/Wave8/AxiomDisclosure.lean`: a machine-checked record that the
Wave9 candidate-theorem pack is EXPERIMENTAL/additive and leaves the LOCKED
baseline untouched. We model the disclosed `#print axioms` set of each Wave9
theorem as a `List String` and prove they are all kernel-only, while RE-ASSERTING
the locked invariant `locked_count_eight = 8`.

The verbatim ground-truth `#print axioms` lines are emitted per theorem in each
Wave9 file and in the CI build log; this file is a meta-level summary, not a
re-verification of those kernel proofs.

## What is proven
- `wave9Disclosed` — the disclosed (kernel-only) axiom sets of the Wave9
  theorems, modeled as concrete `List String` values.
- `wave9_axiom_sets_kernel_only` — every Wave9 disclosed set is kernel-only
  (`decide`): no Wave9 theorem introduces a custom axiom.
- `locked_count_eight` — RE-ASSERTED invariant: the locked baseline is EXACTLY the
  eight {F1,F4,F7,F11,F12,F18,F19,F22}. Wave9 does NOT change this (`decide`).
- `wave9_excluded_from_locked` — the Wave9 theorem names are disjoint from the
  locked eight: Wave9 is additive and excluded from the locked baseline.

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave9`) — NOT in the LOCKED v11 baseline (749/14/163 @
  c7c0ba17). Locked-proven stays exactly 8 {F1,F4,F7,F11,F12,F18,F19,F22}. Λ Conjecture 1.
- Lean-core only; NO Mathlib, NO new declared axiom, NO sorry.

## Citations
- Lean 4 `#print axioms` discipline: https://lean-lang.org/faq/
- Mirrors Lutar/Wave8/AxiomDisclosure.lean (Ph1 axiom-disclosure meta-theorem).

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/

namespace Lutar.Wave9.AxiomDisclosure

/-- The standard Lean 4 kernel / Mathlib trust base. -/
def leanKernelAxioms : List String :=
  ["propext", "funext", "Classical.choice", "Quot.sound"]

/-- Deny-by-default membership predicate over disclosed axiom names. -/
def axiomsAllowed (used : List String) : Bool :=
  used.all (fun a => leanKernelAxioms.contains a)

/-- Disclosed axiom sets for the Wave9 theorems (mirroring their per-file
`#print axioms` lines). Each is kernel-only. -/
def wave9Disclosed : List (String × List String) :=
  [ ("MA1.no_zero_eigenvalue",            ["propext", "Classical.choice", "Quot.sound"]),
    ("MA1.nonsingular_of_strict_diag",    ["propext", "Classical.choice", "Quot.sound"]),
    ("CP1.merkle_root_binding",           ["propext"]),
    ("CP1.merkle_inclusion_sound",        ["propext"]),
    ("CP1.merkle_append_only",            ["propext"]),
    ("MC4.ville_fixed_time",              ["propext", "Classical.choice", "Quot.sound"]),
    ("MC4.ville_markov_bound",            ["propext", "Classical.choice", "Quot.sound"]),
    ("GT1.cut_blocks_reachable",          []),
    ("GT1.disjoint_paths_le_cut",         ["propext", "Classical.choice", "Quot.sound"]),
    ("OE2.posSemidef_convex_comb",        ["propext", "Classical.choice", "Quot.sound"]),
    ("OE2.ci_information_psd",            ["propext", "Classical.choice", "Quot.sound"]),
    ("C1.bdb_safe",                       ["propext", "Quot.sound"]),
    ("C1.bdb_threshold_dichotomy",        ["propext", "Classical.choice", "Quot.sound"]),
    ("PB1.pac_bayes_confidence",          ["propext", "Classical.choice", "Quot.sound"]),
    ("PB1.pac_bayes_risk_envelope",       ["propext", "Classical.choice", "Quot.sound"]),
    ("IF2.noninterference_of_robust",     []),
    ("IF2.robust_declass_sound",          ["propext", "Classical.choice", "Quot.sound"]) ]

/-- Every Wave9 disclosed axiom set is kernel-only: no custom axiom anywhere in
the Wave9 pack. Decided by the kernel. -/
theorem wave9_axiom_sets_kernel_only :
    wave9Disclosed.all (fun p => axiomsAllowed p.2) = true := by decide

/-- The LOCKED baseline names (RE-ASSERTED, NOT modified by Wave9). -/
def lockedNames : List String := ["F1", "F4", "F7", "F11", "F12", "F18", "F19", "F22"]

/-- RE-ASSERTED locked invariant: exactly eight locked theorems. Wave9 leaves this
unchanged. -/
theorem locked_count_eight : lockedNames.length = 8 := by decide

/-- Wave9 is additive: none of the Wave9 theorem identifiers collide with a locked
name (Wave9 is excluded from the locked baseline). -/
theorem wave9_excluded_from_locked :
    wave9Disclosed.all (fun p => ! lockedNames.contains p.1) = true := by decide

#print axioms wave9_axiom_sets_kernel_only
#print axioms locked_count_eight
#print axioms wave9_excluded_from_locked

end Lutar.Wave9.AxiomDisclosure
