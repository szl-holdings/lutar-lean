/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave8/Simplex.lean — S2: Simplex / RTA Switching Safety Invariant

The Simplex (Runtime Assurance) architecture pairs an unverified Advanced
Controller (AC) with a verified Reversionary Controller (RC) and a switching
monitor. We prove the safety invariant: if the monitor is *sound* (it only lets
the AC act when the result stays in the safe set `S`) and the RC *preserves* `S`,
then starting in `S` the switched trajectory stays in `S` for ALL time steps.

Backs the a11oy C2-override gate and killinchu autonomous-mode fallback: when the
AI controller proposes an unsafe action, the monitor reverts to the safe
controller, and the system provably stays in bounds.

## Model (discrete time)
- `State` : abstract state type; `Safe : State → Prop` is the safe set `S`.
- `AC RC : State → State` : advanced and reversionary one-step maps.
- `mon : State → Bool` : the switching monitor.
- `step s := if mon s then AC s else RC s`.
- `traj s₀ t` : the state after `t` switched steps from `s₀`.

## Assumptions
- (RC_safe)        : `∀ s, Safe s → Safe (RC s)`            — RC keeps the system in S.
- (monitor_sound)  : `∀ s, mon s = true → Safe s → Safe (AC s)` — monitor lets AC act
                     only when the AC step stays in S.

## What is proven
- `step_preserves_safe` — one switched step keeps `Safe`.
- `simplex_safety_invariant` — `Safe s₀ → ∀ t, Safe (traj s₀ t)` (induction on t).

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave8`) — NOT in the LOCKED v11 baseline. Locked-proven
  stays exactly 5 {F1,F11,F12,F18,F19}. Λ untouched (Conjecture 1).
- The guarantee is CONDITIONAL on monitor soundness — the monitor is itself
  software/hardware that must be separately assured. We state this assumption
  explicitly; the theorem does not claim the monitor is correct, only that IF it
  is sound THEN safety is maintained. (Same caveat NASA flags for RTA.)
- Lean-core only, no Mathlib, no open obligation, no new declared axiom.

## Citations
- Sha, "Using Simplicity to Control Complexity", IEEE Software 2001 (original Simplex).
- NASA Langley RTA/Simplex formalization (DASC 2024):
  https://shemesh.larc.nasa.gov/fm/papers/DASC2024-SWDMC-draft.pdf
- Black-Box Simplex (NSF): https://par.nsf.gov/servlets/purl/10327769

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/

namespace Lutar.Wave8.Simplex

variable {State : Type}

/-- One switched Simplex step: run AC when the monitor permits, else revert to RC. -/
def step (AC RC : State → State) (mon : State → Bool) (s : State) : State :=
  if mon s then AC s else RC s

/-- The switched trajectory: the state after `t` Simplex steps from `s₀`. -/
def traj (AC RC : State → State) (mon : State → Bool) (s₀ : State) : Nat → State
  | 0     => s₀
  | t + 1 => step AC RC mon (traj AC RC mon s₀ t)

/-- One switched step preserves the safe set, given RC-safety and monitor-soundness. -/
theorem step_preserves_safe (AC RC : State → State) (mon : State → Bool)
    (Safe : State → Prop)
    (hRC : ∀ s, Safe s → Safe (RC s))
    (hMon : ∀ s, mon s = true → Safe s → Safe (AC s))
    (s : State) (hs : Safe s) :
    Safe (step AC RC mon s) := by
  unfold step
  cases hb : mon s with
  | true  => simpa [hb] using hMon s hb hs
  | false => simpa [hb] using hRC s hs

/-- **S2 — Simplex safety invariant.** If RC preserves the safe set and the
monitor is sound, then starting in the safe set the switched trajectory stays in
the safe set for every time step. -/
theorem simplex_safety_invariant (AC RC : State → State) (mon : State → Bool)
    (Safe : State → Prop)
    (hRC : ∀ s, Safe s → Safe (RC s))
    (hMon : ∀ s, mon s = true → Safe s → Safe (AC s))
    (s₀ : State) (hinit : Safe s₀) :
    ∀ t, Safe (traj AC RC mon s₀ t) := by
  intro t
  induction t with
  | zero => simpa [traj] using hinit
  | succ t ih =>
      show Safe (step AC RC mon (traj AC RC mon s₀ t))
      exact step_preserves_safe AC RC mon Safe hRC hMon _ ih

#print axioms step_preserves_safe
#print axioms simplex_safety_invariant

end Lutar.Wave8.Simplex
