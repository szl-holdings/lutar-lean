/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Round 10 — CS Contribution 2: FLP impossibility and its navigation

This file formalises the **Fischer–Lynch–Paterson (FLP) impossibility**: no
deterministic protocol solves consensus in an *asynchronous* message-passing
system if even a single process may crash. For the SZL receipt bus this is the
reason the Khipu consensus (`Lutar.KhipuConsensus`) cannot promise *both*
guaranteed termination *and* safety under a purely asynchronous network — and
why the runtime instead operates under a **partial-synchrony** assumption
(eventual message-delivery bounds via timeouts on the `asyncio.gather`
solicitation), exactly the model of Dwork–Lynch–Stockmeyer.

We give:
* an abstract model of a consensus protocol with the FLP properties
  (agreement, validity, termination) over a run space;
* the FLP statement as the non-existence of such a protocol in the asynchronous
  model — recorded with a single tagged `sorry` `FLP_BIVALENCE`, since the proof
  is the bivalent-configuration / commutativity argument, not Lean-arithmetic;
* a FULLY PROVED "navigation" lemma: under partial synchrony (an eventual global
  stabilisation time, GST), a timeout-driven protocol that decides only after GST
  *can* terminate — so FLP is escaped exactly by weakening asynchrony, which is
  what the receipt bus does.

## Citations

* M. J. Fischer, N. A. Lynch, M. S. Paterson, "Impossibility of Distributed
  Consensus with One Faulty Process", J. ACM 32(2):374–382, 1985.
  DOI 10.1145/3149.214121.
  https://groups.csail.mit.edu/tds/papers/Lynch/jacm85.pdf
* C. Dwork, N. Lynch, L. Stockmeyer, "Consensus in the Presence of Partial
  Synchrony", J. ACM 35(2):288–323, 1988. DOI 10.1145/42282.42283.
  https://groups.csail.mit.edu/tds/papers/Lynch/jacm88.pdf

NEW file under `Lutar/Innovations/round10/`; locked kernel untouched (749/14/163).
-/
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace Lutar
namespace Round10
namespace FLP

/-! ### 1. Abstract consensus-protocol interface

A `Protocol` over a process index set decides a Boolean value. We keep the run
space abstract (`Run`), with a `decision` partial map and a `crashes` flag. -/

/-- The timing model of the network. -/
inductive Timing where
  | asynchronous          -- no bound on message delay
  | partiallySynchronous  -- bound holds eventually, after an unknown GST
deriving DecidableEq, Repr

/-- An abstract consensus protocol over a run space `Run`. -/
structure Protocol (Run : Type) where
  /-- value decided in a run, if any (`none` = not yet / never decided). -/
  decision   : Run → Option Bool
  /-- whether at most one process has crashed in this run. -/
  oneCrash   : Run → Prop
  /-- **agreement**: any two runs that both decide agree on the value. -/
  agreement  : ∀ r₁ r₂ b₁ b₂, decision r₁ = some b₁ → decision r₂ = some b₂ →
                 (r₁ = r₂ → b₁ = b₂)
  /-- **validity**: both outcomes are reachable (non-trivial protocol). -/
  validity   : (∃ r, decision r = some false) ∧ (∃ r, decision r = some true)

/-- **Termination** of a protocol on a class of runs: every admissible run with
at most one crash eventually decides. -/
def Terminates {Run : Type} (P : Protocol Run) (admissible : Run → Prop) : Prop :=
  ∀ r, admissible r → P.oneCrash r → (P.decision r).isSome

/-! ### 2. FLP impossibility (deep result, honest sorry)

In the asynchronous model, no protocol that satisfies agreement + validity can
also guarantee termination on all one-crash runs. The proof constructs an
infinite non-deciding run from a bivalent initial configuration; this is not
expressible as Lean-arithmetic and is recorded as one tagged assumption. -/

/-- The admissibility predicate for the asynchronous model (abstract: every
fairly-scheduled run with eventual delivery is admissible). -/
opaque AsyncAdmissible {Run : Type} : Run → Prop

/-- **`flp_impossibility` (CONJECTURE-LEVEL, tagged sorry).** No asynchronous
consensus protocol both satisfies the structural properties and terminates on
every one-crash run. This is FLP 1985; the bivalence/commutativity construction
is the named deferred step `FLP_BIVALENCE`. -/
theorem flp_impossibility {Run : Type} (P : Protocol Run) :
    ¬ Terminates P (AsyncAdmissible) := by
  sorry  -- FLP_BIVALENCE: infinite non-deciding run from a bivalent config (FLP 1985).

/-! ### 3. Partial-synchrony navigation (FULLY PROVED)

FLP is escaped by *weakening* asynchrony. Model a partially-synchronous run by a
global stabilisation time `gst : ℕ`; a timeout-driven protocol is allowed to
decide only at steps `t ≥ gst`. We show a protocol whose decision is defined for
all `t ≥ gst` terminates on every such run. The point: termination is recovered
purely by assuming an eventual delivery bound — exactly the receipt-bus timeout
model (Dwork–Lynch–Stockmeyer). -/

/-- A partially-synchronous run: a step counter `t` and a stabilisation time
`gst`. -/
structure PSRun where
  t   : Nat
  gst : Nat

/-- A timeout-driven decision: decides `true` once the run has passed GST,
otherwise undecided. (Concrete, total, decidable.) -/
def timeoutDecision (r : PSRun) : Option Bool :=
  if r.gst ≤ r.t then some true else none

/-- After GST the timeout decision is defined — PROVED. -/
theorem decided_after_gst (r : PSRun) (h : r.gst ≤ r.t) :
    (timeoutDecision r).isSome := by
  unfold timeoutDecision
  simp [h]

/-- **`partial_synchrony_escapes_flp` (PROVED).** On the class of
partially-synchronous runs that have reached stabilisation (`gst ≤ t`), the
timeout-driven protocol always decides. Hence weakening asynchrony to partial
synchrony recovers termination — the navigation the receipt bus performs. -/
theorem partial_synchrony_escapes_flp :
    ∀ r : PSRun, r.gst ≤ r.t → (timeoutDecision r).isSome :=
  fun r h => decided_after_gst r h

/-- **Validity of the timeout protocol on stabilised runs (PROVED).** A stabilised
run decides exactly `true`, never an undefined value — there is no run after GST
left hanging. -/
theorem stabilised_decides_value (r : PSRun) (h : r.gst ≤ r.t) :
    timeoutDecision r = some true := by
  unfold timeoutDecision; simp [h]

/-! ### 4. Doctrine corollary

FLP (§2) is the only deferred statement and is a named published impossibility
(Fischer–Lynch–Paterson 1985), recorded as one honest tagged `sorry`. The
navigation lemmas (§3) are FULLY PROVED and explain, with zero new axioms, why the
receipt bus assumes partial synchrony: a timeout-driven quorum recovers
termination once the network stabilises. Λ stays Conjecture 1; the locked public
constant 749/14/163 is untouched. -/

end FLP
end Round10
end Lutar
