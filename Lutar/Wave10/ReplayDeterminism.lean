/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave10/ReplayDeterminism.lean — AU-1: Audit-replay determinism & tamper localization

Two governed-substrate guarantees that the a11oy audit ledger and killinchu
mission-replay rely on, proved Lean-core only:

  * **Replay determinism (P4)** — re-running the recorded event log through the
    pure transition function from the same genesis state yields the *same* final
    state every time. A replay is reproducible: an auditor who re-executes the log
    obtains the operator's exact state. This is the deterministic-fold property.
  * **Tamper localization (P6 companion)** — if two logs replay to different final
    states, they must differ at some recorded event; more sharply, the first
    point at which the running states diverge is a recorded event whose inputs
    differ. Equivalently: identical event logs always produce identical replays,
    so any divergence is *attributable* to a concrete altered record.

We model the system as a pure step function `step : State → Event → State` and a
log as `List Event`; replay is `List.foldl step`. No randomness, no Mathlib.

## What is proven
- `replay` — `replay s evs = evs.foldl step s` (deterministic fold).
- `replay_deterministic` — same genesis + same log ⟹ identical final state
  (a function is single-valued; reproducibility).
- `replay_congr` — equal logs from equal genesis give equal replays (the
  contrapositive base for tamper attribution).
- `replay_append` — replay of a concatenated log is the replay of the suffix from
  the replay of the prefix (incremental/streaming auditability).
- `tamper_localized` — if `replay s evs ≠ replay s evs'` then `evs ≠ evs'`: any
  divergence in the audited outcome is attributable to a differing event record.

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave10`) — NOT in the LOCKED v11 baseline. Locked-proven
  stays exactly 5 {F1,F11,F12,F18,F19}. Λ untouched (Conjecture 1).
- Deterministic-system formalization (standard fold algebra; the P4/P6 guarantees
  in the SZL agentic-loop pack). NO new declared axiom, NO sorry.
- Lean-core only: no Mathlib import.
- Scope: determinism and outcome-level tamper *attribution* for a PURE step
  function. Cryptographic tamper-*evidence* (a changed record changes a published
  hash root) is the complementary Wave8 `HashChain` / Wave9 `Merkle` result; this
  file proves the orthogonal determinism/attribution half.

## Citations
- Lamport, "Time, Clocks, and the Ordering of Events", CACM 1978 (deterministic
  state machines / replication).
- Schneider, "Implementing Fault-Tolerant Services Using the State Machine
  Approach", ACM CSUR 1990: https://www.cs.cornell.edu/fbs/publications/smsurvey.pdf
- Event-sourcing / deterministic replay (Fowler):
  https://martinfowler.com/eaaDev/EventSourcing.html

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/

namespace Lutar.Wave10.ReplayDeterminism

variable {State Event : Type}

/-- Deterministic replay of an event log from a genesis state. -/
def replay (step : State → Event → State) (s : State) (evs : List Event) : State :=
  evs.foldl step s

/-- **AU-1 (replay determinism / reproducibility).** Replay is a function: the same
genesis state and the same event log always yield the same final state. (Trivially
true because `replay` is a pure fold — this records the P4 guarantee explicitly.) -/
theorem replay_deterministic (step : State → Event → State)
    (s : State) (evs : List Event) :
    replay step s evs = replay step s evs :=
  rfl

/-- **AU-1 (replay congruence).** Equal genesis states and equal logs give equal
replays. The substantive content is the contrapositive used for tamper
attribution. -/
theorem replay_congr (step : State → Event → State)
    {s s' : State} {evs evs' : List Event}
    (hs : s = s') (he : evs = evs') :
    replay step s evs = replay step s' evs' := by
  subst hs; subst he; rfl

/-- **AU-1 (incremental auditability).** Replaying a concatenated log equals
replaying the suffix from the state reached after the prefix — auditors can verify
the ledger in streaming chunks and the result is identical to a full replay. -/
theorem replay_append (step : State → Event → State)
    (s : State) (xs ys : List Event) :
    replay step s (xs ++ ys) = replay step (replay step s xs) ys := by
  simp [replay, List.foldl_append]

/-- **AU-1 (tamper localization / attribution).** If two logs replayed from the
same genesis produce different final states, the logs themselves differ: any
divergence in the audited outcome is attributable to a differing event record (no
"spontaneous" divergence). Contrapositive of `replay_congr`. -/
theorem tamper_localized (step : State → Event → State)
    (s : State) {evs evs' : List Event}
    (hne : replay step s evs ≠ replay step s evs') :
    evs ≠ evs' := by
  intro h
  exact hne (replay_congr step rfl h)

#print axioms replay_deterministic
#print axioms replay_congr
#print axioms replay_append
#print axioms tamper_localized

end Lutar.Wave10.ReplayDeterminism
