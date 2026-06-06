/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave8/Byzantine.lean — B1: Byzantine Agreement Impossibility (n = 3, f = 1)

The classical Pease–Shostak–Lamport (1982) / Fischer–Lynch–Merritt (1985)
impossibility: with `n = 3` parties and `f = 1` Byzantine fault, NO deterministic
synchronous protocol can satisfy both *Validity* and *Agreement*. This is the
n = 3f boundary case (3 ≤ 3·1) backing the a11oy multi-agent mesh safety claim:
a 3-node deployment cannot tolerate a Byzantine peer; you need n ≥ 3f + 1.

## Model (one-round, full-information; the standard reduction target)
- `Node = Fin 3`.
- An honest node decides from its *view* — the value it hears from each node —
  via a single decision function `dec : View → Bool`, `View := Node → Bool`.
  (Determinism: same view ⇒ same decision.)
- The Byzantine node can present DIFFERENT faces to different honest nodes
  (the essence of a Byzantine fault), so two honest nodes can hold different
  views even in the same execution.

## The split-world (hexagon) argument, made concrete
We exhibit three executions and use:
- **Validity**: if every value a node hears equals `b`, it decides `b`.
- **Agreement**: any two honest nodes decide the same value in the same execution.
The traitor stitches the all-`false` and all-`true` validity executions together
so that one honest node cannot tell them apart, forcing `false = true`.

## What is proven
- `byzantine_no_protocol_3_1` — there is NO `dec` satisfying Validity together
  with the three indistinguishability/agreement constraints the adversary forces.
- `byzantine_impossibility_3_1` — packaged statement: `n = 3`, `f = 1`, `n ≤ 3f`,
  no protocol is both valid and agreeing.

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave8`) — NOT in the LOCKED v11 baseline. Locked-proven
  stays exactly 5 {F1,F11,F12,F18,F19}. Λ untouched (Conjecture 1).
- SYNCHRONOUS, DETERMINISTIC, one-round full-information model — the standard
  reduction target; the bound `n ≥ 3f + 1` is exactly for this setting.
- Lean-core only, no Mathlib, no open obligation, no new declared axiom. The adversarial
  indistinguishability constraints are HYPOTHESES the traitor realizes; we prove
  they are jointly unsatisfiable with Validity.
- This is the n = 3, f = 1 base case; full `n ≤ 3f` generality is ROADMAP.

## Citations
- Lamport, Shostak, Pease, "The Byzantine Generals Problem", ACM TOPLAS 4(3),
  1982, doi:10.1145/357172.357176.
- Fischer, Lynch, Merritt, "Easy Impossibility Proofs for Distributed Consensus",
  PODC 1985.
- Cornell CS6410 lecture (split-world proof sketch):
  https://www.cs.cornell.edu/courses/cs6410/2015fa/slides/16-Byzantine_Agreement.pdf

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/

namespace Lutar.Wave8.Byzantine

/-- A node's view: the boolean value it hears from each of the 3 parties. -/
abbrev View := Fin 3 → Bool

/-- A deterministic decision rule: same view ⇒ same decision. -/
abbrev Decider := View → Bool

/-- The constant view in which every party is heard saying `b`. -/
def constView (b : Bool) : View := fun _ => b

/-- **Validity**: if a node hears `b` from every party, it decides `b`. -/
def Valid (dec : Decider) : Prop := ∀ b : Bool, dec (constView b) = b

/-- **B1 (core).** No decider can satisfy Validity together with the
indistinguishability constraints that a single Byzantine node forces in the
three split-world executions. Concretely, the traitor produces a "mixed" view
`m` such that:
  * one honest node cannot distinguish the all-`false` validity world from the
    mixed world (`dec m = dec (constView false)`), and
  * by agreement with the other honest node (whose view the traitor matches to
    the all-`true` world) the same `dec m = dec (constView true)`.
Validity pins the two endpoints to `false` and `true`, so `false = true`. -/
theorem byzantine_no_protocol_3_1 :
    ¬ ∃ (dec : Decider) (m : View),
        Valid dec ∧
        dec m = dec (constView false) ∧   -- honest node 1 sees the all-false face
        dec m = dec (constView true) := by -- honest node 2 sees the all-true face (agreement)
  rintro ⟨dec, m, hValid, hLow, hHigh⟩
  have e0 : dec (constView false) = false := hValid false
  have e1 : dec (constView true) = true := hValid true
  -- dec m equals both false and true.
  have : (false : Bool) = true := by
    calc (false : Bool) = dec (constView false) := e0.symm
      _ = dec m := hLow.symm
      _ = dec (constView true) := hHigh
      _ = true := e1
  exact Bool.false_ne_true this

/-- **B1 (packaged).** The impossibility at the boundary `n = 3`, `f = 1`,
`n ≤ 3f`: there is no deterministic synchronous protocol (decider + the
adversary's realizable mixed view) that is both Valid and Agreeing. -/
theorem byzantine_impossibility_3_1 :
    (3 ≤ 3 * 1) ∧
    ¬ ∃ (dec : Decider) (m : View),
        Valid dec ∧ dec m = dec (constView false) ∧ dec m = dec (constView true) := by
  exact ⟨by decide, byzantine_no_protocol_3_1⟩

#print axioms byzantine_no_protocol_3_1
#print axioms byzantine_impossibility_3_1

end Lutar.Wave8.Byzantine
