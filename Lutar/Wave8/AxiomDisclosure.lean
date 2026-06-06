/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave8/AxiomDisclosure.lean — Ph1: Axiom-Disclosure Meta-Theorem

`#print axioms` discipline rendered as a machine-checked theorem about our own
proof system. We model the *disclosed axiom set* of a declaration as a
`List String`, define `leanKernelAxioms` (the standard Lean 4 kernel/Mathlib
trust base `{propext, funext, Classical.choice, Quot.sound}`), and prove:

  * `axiomsAllowed` is the deny-by-default membership predicate;
  * `disclosure_sound`  — if a decl's disclosed axiom set is `axiomsAllowed`,
    then every disclosed axiom is a member of `leanKernelAxioms`;
  * `locked_axiom_sets_kernel_only` — the disclosed axiom sets we publish for the
    five LOCKED theorems {F1,F11,F12,F18,F19} are each kernel-only (`decide`).

This is the honest-by-construction narrative made into a theorem: the axiom set
underlying every governance proof is enumerable, bounded, and publicly auditable.

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave8` scope) — NOT folded into the LOCKED v11 baseline
  (749/14/163 @ c7c0ba17). Locked-proven stays exactly 5 {F1,F11,F12,F18,F19}.
- Λ (F23) is untouched — it remains Conjecture 1.
- This file is a META-LEVEL property of disclosed axiom *names*; it does not, and
  cannot, by itself re-verify the underlying kernel proofs. The ground truth for
  each theorem's axioms is the `#print axioms` line emitted in the CI build log.
- NO open obligation / open obligation. NO new declared axiom.

## Citations
- Lean 4 `#print axioms` discipline: https://lean-lang.org/faq/
- Tridirectional discriminating-power meta-theorem (Lean 4 axiom-record pattern):
  arXiv:2606.01794v2  https://arxiv.org/html/2606.01794v2
- Mario Carneiro, Lean type theory / consistency relative to ZFC:
  https://supaiku.com/what-does-a-lean-proof-prove

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/

namespace Lutar.Wave8.AxiomDisclosure

/-- The standard Lean 4 kernel / Mathlib trust base. Any proof whose disclosed
`#print axioms` set is a subset of this list introduces NO custom axiom. -/
def leanKernelAxioms : List String :=
  ["propext", "funext", "Classical.choice", "Quot.sound"]

/-- Deny-by-default membership predicate over disclosed axiom names. -/
def axiomsAllowed (used : List String) : Bool :=
  used.all (fun a => leanKernelAxioms.contains a)

/-- Soundness of the disclosure check: if a declaration's disclosed axiom set
passes `axiomsAllowed`, then every disclosed axiom is in the kernel base. -/
theorem disclosure_sound (used : List String) (h : axiomsAllowed used = true) :
    ∀ a ∈ used, leanKernelAxioms.contains a = true := by
  intro a ha
  exact List.all_eq_true.mp h a ha

/-- Equivalent "no custom axiom" phrasing: the disclosed set carries no name
outside the kernel base. -/
theorem no_custom_axiom (used : List String) (h : axiomsAllowed used = true) :
    used.all (fun a => leanKernelAxioms.contains a) = true := h

/-- The empty disclosed set (a fully axiom-free decl) trivially passes. -/
theorem empty_allowed : axiomsAllowed [] = true := by decide

/-- The disclosed axiom sets we publish for the five LOCKED theorems
{F1,F11,F12,F18,F19}. These mirror the `#print axioms` lines reported in CI for
the locked kernel; we model each as a concrete `List String`. -/
def lockedDisclosed : List (String × List String) :=
  [ ("F1",  ["propext", "Classical.choice", "Quot.sound"]),
    ("F11", ["propext", "Classical.choice", "Quot.sound"]),
    ("F12", ["propext", "Classical.choice", "Quot.sound"]),
    ("F18", ["propext", "funext", "Classical.choice", "Quot.sound"]),
    ("F19", ["propext", "Classical.choice", "Quot.sound"]) ]

/-- META-THEOREM (Ph1): every LOCKED theorem's disclosed axiom set is
kernel-only. Decided by the kernel — depends on NO axioms itself. -/
theorem locked_axiom_sets_kernel_only :
    lockedDisclosed.all (fun p => axiomsAllowed p.2) = true := by decide

/-- Corollary: there are exactly five locked entries, matching the locked count. -/
theorem locked_count_five : lockedDisclosed.length = 5 := by decide

#print axioms disclosure_sound
#print axioms no_custom_axiom
#print axioms empty_allowed
#print axioms locked_axiom_sets_kernel_only
#print axioms locked_count_five

end Lutar.Wave8.AxiomDisclosure
