/-
  tools/lean/LockedGuard.lean — kernel-emitted axiom guard over the LOCKED proven set.

  The eight locked formulas {F1,F4,F7,F11,F12,F18,F19,F22} are carried by the 24
  theorems below in Lutar/Puriq/Formulas/ProvedFormulas.lean. For each one this file asks the
  kernel (`collectAxioms`) which axioms the proof term depends on and FAILS THE BUILD unless
  that set lies inside the human-owned trust base {propext, Classical.choice, Quot.sound}.
  `sorryAx`, `Lean.ofReduceBool` (native_decide) and any user axiom are therefore refused.

  It is self-contained (core Lean only, no Mathlib), lives outside Lutar/ so the canonical
  declaration numbers are untouched, and is run by lake-build.yml as
      lake env lean tools/lean/LockedGuard.lean
  after `lake build`. The guard list is exhaustive on purpose: the workflow asserts exactly
  24 `allowed:true` lines, so adding or removing a locked-set theorem without updating this
  file fails loudly. Changing the trust base or the list is a code-review event.

  Cross-checked outside CI on 2026-09-30 (Lean v4.18.0, bare core, no Mathlib) against
  ProvedFormulas.lean @ main c4af7e22ab30: 24/24 allowed
  (11 depend on no axiom, 10 on propext only, 3 on propext + Quot.sound; 0 Classical.choice).
-/
import Lean
import Lutar.Puriq.Formulas.ProvedFormulas
open Lean Elab Command

namespace GEH

/-- Human-owned trust base. Policy lives here and nowhere else. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def axiomsAllowed (ax : List Name) : Bool :=
  ax.all fun a => allowedAxioms.contains a

/-- Stable emission order (dedup + sort) so receipts are deterministic. -/
def normalize (ax : Array Name) : List Name :=
  (ax.toList.eraseDups.toArray.qsort fun a b => a.toString < b.toString).toList

def guardJson (thm : Name) (axs : List Name) (allowed : Bool) : Json :=
  Json.mkObj
    [ ("tool", "lean.query_axioms")
    , ("theorem", toString thm)
    , ("axioms", toJson (axs.map toString))
    , ("allowed", allowed)
    , ("trust_base", toJson (allowedAxioms.map toString)) ]

end GEH

syntax (name := gehGuard) "#geh_guard " ident : command

/-- `#geh_guard thm` — emit the audit line for the receipt, or FAIL THE BUILD
    when `thm` depends on any axiom outside the trust base. -/
@[command_elab gehGuard] def elabGehGuard : CommandElab := fun stx => do
  match stx with
  | `(#geh_guard $n:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverload n
    let axs ← collectAxioms name
    let norm := GEH.normalize axs
    let ok := GEH.axiomsAllowed norm
    let line := "GEH_GUARD " ++ (GEH.guardJson name norm ok).compress
    if ok then
      logInfo line
    else
      throwError "{line}\nGEH GUARD FAILED: {name} depends on axioms outside the trust base {norm} (allowed: {GEH.allowedAxioms})"
  | _ => throwUnsupportedSyntax

-- ---- locked set -------------------------------------------------------------
#geh_guard Puriq.Formula.Proved.f1_replay_hash_determinism
#geh_guard Puriq.Formula.Proved.f1_replay_trace_stable
#geh_guard Puriq.Formula.Proved.f11_ayni_reciprocity_conservation
#geh_guard Puriq.Formula.Proved.f12_kuramoto_additive
#geh_guard Puriq.Formula.Proved.f18_reed_solomon_parity_count
#geh_guard Puriq.Formula.Proved.f18_erasure_tolerance
#geh_guard Puriq.Formula.Proved.f19_bekenstein_additive
#geh_guard Puriq.Formula.Proved.f19_budget_monotone
#geh_guard Puriq.Formula.Proved.f4_khipu_no_self_loop
#geh_guard Puriq.Formula.Proved.f4_khipu_acyclic_irrefl
#geh_guard Puriq.Formula.Proved.f4_khipu_reach_strictly_smaller
#geh_guard Puriq.Formula.Proved.f4_khipu_reach_decreases
#geh_guard Puriq.Formula.Proved.f4_khipu_no_cycle
#geh_guard Puriq.Formula.Proved.f4_khipu_append_preserves_invariant
#geh_guard Puriq.Formula.Proved.f4_khipu_dag_acyclic_preserved
#geh_guard Puriq.Formula.Proved.f7_chaski_enqueueAll_nil
#geh_guard Puriq.Formula.Proved.f7_chaski_drain_eq
#geh_guard Puriq.Formula.Proved.f7_chaski_enqueue_preserves_prefix
#geh_guard Puriq.Formula.Proved.f7_chaski_head_is_oldest
#geh_guard Puriq.Formula.Proved.f7_chaski_fifo_order
#geh_guard Puriq.Formula.Proved.f7_chaski_fifo_positional
#geh_guard Puriq.Formula.Proved.f22_emit_appends_length
#geh_guard Puriq.Formula.Proved.f22_emit_strictly_greater
#geh_guard Puriq.Formula.Proved.f22_khipu_emit_monotone
