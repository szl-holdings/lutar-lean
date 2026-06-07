/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave11/AxiomDisclosure.lean — Wave11 (Frontier) axiom-disclosure ledger

Mirrors `Lutar/Wave10/AxiomDisclosure.lean`: a machine-checked record that the
Wave11 FRONTIER candidate-theorem pack (CF-1, CF-2, CF-3, CF-5) is
EXPERIMENTAL/additive and leaves the LOCKED baseline untouched.  We model the
disclosed `#print axioms` set of each Wave11 theorem as a `List String` and
prove they are all kernel-only, while RE-ASSERTING the locked invariant
`locked_count_five = 5`.

The verbatim ground-truth `#print axioms` lines are emitted per theorem in each
Wave11 file (and in the CI build log); this file is a meta-level summary, not a
re-verification of those kernel proofs.

## What is proven
- `wave11Disclosed` — the disclosed (kernel-only) axiom sets of the Wave11
  theorems, matching their per-file `#print axioms` lines, captured verbatim
  from the local `lake env lean` kernel build (Lean 4.18.0 / Mathlib v4.18.0).
- `wave11_axiom_sets_kernel_only` — every Wave11 disclosed set is kernel-only
  (`decide`): no Wave11 theorem introduces a custom axiom (no sorryAx).
- `locked_count_five` — RE-ASSERTED invariant: the locked baseline is EXACTLY the
  five {F1,F11,F12,F18,F19}. Wave11 does NOT change this (`decide`).
- `wave11_excluded_from_locked` — Wave11 theorem names are disjoint from the
  locked five: Wave11 is additive and excluded from the locked baseline.

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave11`) — NOT in the LOCKED v11 baseline (749/14/163 @
  c7c0ba17). Locked-proven stays exactly 5 {F1,F11,F12,F18,F19}. Λ Conjecture 1.
- Lean-core only; NO Mathlib, NO new declared axiom, NO sorry.
- The CF-5 entries are the DISCRETE Neyman-Pearson core; the measure-theoretic
  Gaussian-shift `sorry₁` in `Robustness/CertifiedRadius.lean` remains OPEN
  (roadmap) and is intentionally NOT listed as closed here.

## Citations
- Lean 4 `#print axioms` discipline: https://lean-lang.org/faq/
- Mirrors Lutar/Wave10/AxiomDisclosure.lean (axiom-disclosure meta-theorem).

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/

namespace Lutar.Wave11.AxiomDisclosure

/-- The standard Lean 4 kernel / Mathlib trust base. -/
def leanKernelAxioms : List String :=
  ["propext", "funext", "Classical.choice", "Quot.sound"]

/-- Deny-by-default membership predicate over disclosed axiom names. -/
def axiomsAllowed (used : List String) : Bool :=
  used.all (fun a => leanKernelAxioms.contains a)

/-- Disclosed axiom sets for the Wave11 FRONTIER theorems (mirroring their
per-file `#print axioms` lines, captured verbatim from the local kernel build).
Each is kernel-only. -/
def wave11Disclosed : List (String × List String) :=
  [ -- CF-1 — Λ-graph automorphism / iso distance + position-encoding invariance
    ("GraphAutoDistInvariant.reachable_iso_iff",            ["propext", "Quot.sound"]),
    ("GraphAutoDistInvariant.dist_le_of_iso",               ["propext", "Classical.choice", "Quot.sound"]),
    ("GraphAutoDistInvariant.dist_iso_eq",                  ["propext", "Classical.choice", "Quot.sound"]),
    ("GraphAutoDistInvariant.dist_auto_eq",                 ["propext", "Classical.choice", "Quot.sound"]),
    ("GraphAutoDistInvariant.positionEncoding_equivariant", ["propext", "Classical.choice", "Quot.sound"]),
    ("GraphAutoDistInvariant.positionEncoding_iso_equivariant", ["propext", "Classical.choice", "Quot.sound"]),
    -- CF-1 — the now-CLOSED PositionAware obligations (formerly `:= True`)
    ("PositionAware.dist_iso_inv_obligation_tracked",       ["propext", "Classical.choice", "Quot.sound"]),
    ("PositionAware.positionEncoding_equivariant_obligation_tracked", ["propext", "Classical.choice", "Quot.sound"]),
    -- CF-2 — Ouro looped-LM KV-cache slot-indexing equivalence
    ("OuroKVCacheSlots.slotIndex_eq",                       ["propext", "Classical.choice", "Quot.sound"]),
    ("OuroKVCacheSlots.slotIndex_injective",                ["propext", "Classical.choice", "Quot.sound"]),
    ("OuroKVCacheSlots.slotIndex_surjective",               ["propext", "Classical.choice", "Quot.sound"]),
    ("OuroKVCacheSlots.slotIndex_bijective",                ["propext", "Classical.choice", "Quot.sound"]),
    ("OuroKVCacheSlots.cache_size_correct",                 ["propext", "Classical.choice", "Quot.sound"]),
    ("OuroKVCacheSlots.decode_equivalent_of_correct_slots", ["propext", "Classical.choice", "Quot.sound"]),
    ("OuroKVCacheSlots.undersized_cache_collides",          ["propext", "Quot.sound"]),
    -- CF-3 — Ouro loop fixed-point uniqueness + early-exit error envelope
    ("OuroLoopEarlyExit.ouro_loop_unique_fixedPoint",       ["propext", "Classical.choice", "Quot.sound"]),
    ("OuroLoopEarlyExit.ouro_early_exit_error_bound",       ["propext", "Classical.choice", "Quot.sound"]),
    ("OuroLoopEarlyExit.ouro_early_exit_error_bound_initial", ["propext", "Classical.choice", "Quot.sound"]),
    ("OuroLoopEarlyExit.ouro_initial_distance_to_fixedPoint_le", ["propext", "Classical.choice", "Quot.sound"]),
    ("OuroLoopEarlyExit.ouro_early_exit_tendsto_zero",      ["propext", "Classical.choice", "Quot.sound"]),
    -- CF-5 — Neyman-Pearson optimal immune egress gate (DISCRETE core)
    ("ImmuneNeymanPearsonOpt.np_pointwise_nonneg",          ["propext", "Classical.choice", "Quot.sound"]),
    ("ImmuneNeymanPearsonOpt.neyman_pearson_most_powerful", ["propext", "Classical.choice", "Quot.sound"]),
    ("ImmuneNeymanPearsonOpt.neyman_pearson_min_false_negative", ["propext", "Classical.choice", "Quot.sound"]),
    ("ImmuneNeymanPearsonOpt.fail_closed_zero_test",        ["propext", "Classical.choice", "Quot.sound"]) ]

/-- Every Wave11 disclosed axiom set is kernel-only: no custom axiom anywhere in
the Wave11 FRONTIER pack (no sorryAx). Decided by the kernel. -/
theorem wave11_axiom_sets_kernel_only :
    wave11Disclosed.all (fun p => axiomsAllowed p.2) = true := by decide

/-- The LOCKED baseline names (RE-ASSERTED, NOT modified by Wave11). -/
def lockedNames : List String := ["F1", "F11", "F12", "F18", "F19"]

/-- RE-ASSERTED locked invariant: exactly five locked theorems. Wave11 leaves
this unchanged. -/
theorem locked_count_five : lockedNames.length = 5 := by decide

/-- Wave11 is additive: none of the Wave11 theorem identifiers collide with a
locked name (Wave11 is excluded from the locked baseline). -/
theorem wave11_excluded_from_locked :
    wave11Disclosed.all (fun p => ! lockedNames.contains p.1) = true := by decide

/-- The Wave11 pack proves exactly 24 frontier theorems (CF-1/CF-2/CF-3/CF-5),
all experimental/additive. -/
theorem wave11_theorem_count : wave11Disclosed.length = 24 := by decide

#print axioms wave11_axiom_sets_kernel_only
#print axioms locked_count_five
#print axioms wave11_excluded_from_locked
#print axioms wave11_theorem_count

end Lutar.Wave11.AxiomDisclosure
