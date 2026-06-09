/-
# Putnam 2020 A2 — DEMO (statement formalized, proof deferred)

Problem. Let `k` be a nonnegative integer. Evaluate
`∑_{j=0}^{k} 2^{k−j} · C(k+j, j)`.
Answer: `4^k`.

Honesty label: **DEMO.** The statement below typechecks against core Lean (we
define our own `binom` via Pascal's rule because `Nat.choose` is not in the core
prelude), but the proof is `sorry`, so `#print axioms putSum_eq_four_pow` would
report `sorryAx`. This file is intentionally NOT labeled REAL.

Sanity of the *statement* (not a proof): `#eval` confirms `putSum k = 4 ^ k`
for `k = 0 … 7` (all hold). Computational agreement is evidence the statement is
correctly transcribed; it is NOT a kernel proof, hence DEMO.

See `Showcase/Putnam/P04.md` for the human-readable writeup.
-/
namespace Showcase.Putnam

/-- Binomial coefficient via Pascal's rule (core-only; avoids `Nat.choose`). -/
def binom : Nat → Nat → Nat
  | _,     0     => 1
  | 0,     _+1   => 0
  | n+1, k+1 => binom n k + binom n (k + 1)

/-- The Putnam 2020 A2 sum `∑_{j=0}^{k} 2^{k−j} · C(k+j, j)`. -/
def putSum (k : Nat) : Nat :=
  (List.range (k + 1)).foldl (fun acc j => acc + 2 ^ (k - j) * binom (k + j) j) 0

-- Statement sanity check (evidence, NOT proof): all equal `4 ^ k`.
#eval (List.range 8).map (fun k => (putSum k, 4 ^ k, putSum k == 4 ^ k))

/-- Putnam 2020 A2 (DEMO): `putSum k = 4 ^ k`.
    Proof deferred (`sorry`) — this declaration is DEMO, not REAL. -/
theorem putSum_eq_four_pow (k : Nat) : putSum k = 4 ^ k := by
  sorry

end Showcase.Putnam
