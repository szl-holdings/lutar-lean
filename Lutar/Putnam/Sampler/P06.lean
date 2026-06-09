import Mathlib

namespace Lutar.Putnam.Sampler

/-!
# Sampler Problem 6 (Combinatorics / coin-flip parity invariant)

**Problem (PDF):** *The PDF statement is incomplete* (the coin/move counts are cut off). We
restate the well-posed core that the problem is built on: a parity invariant for a
coin-flipping process.

**Restated precisely.** Coins are heads/tails; a *move* flips exactly `k` coins. If a move
flips `k` coins of which `j` were heads (`0 ≤ j ≤ k`), the head-count changes from `H` to
`H + k - 2j`. We model a run as a list `js` of the per-move head-counts-among-flipped, and
`runMoves k H js` is the resulting head-count.

**Invariant (proved):** `runMoves k H js ≡ H + k · (number of moves) (mod 2)`. In particular,
each move flips the head-count parity iff `k` is odd; the `-2j` term never affects parity.

**Necessary condition (proved):** to reach all-heads `H = 2n` from `H = n` we must have
`0 ≡ n + k·m (mod 2)` where `m` is the number of moves — the standard parity obstruction.

**Difficulty:** 3 (after restatement).
**Status:** KERNEL-VERIFIED (sorry-free).
-/

/-- Head-count after a list of moves, each flipping `k` coins; the list entry `jᵢ` is the
number of heads among the `k` coins flipped on move `i`. Each move sends `H ↦ H + k - 2·jᵢ`. -/
def runMoves (k H : ℤ) : List ℤ → ℤ
  | [] => H
  | j :: js => runMoves k (H + k - 2 * j) js

/-- **Parity invariant.** After `js.length` moves each flipping `k` coins, the head-count is
congruent mod 2 to `H + k · (number of moves)`, independent of the `jᵢ`. -/
theorem p06_parity_invariant (k H : ℤ) (js : List ℤ) :
    runMoves k H js % 2 = (H + k * (js.length : ℤ)) % 2 := by
  induction js generalizing H with
  | nil => simp [runMoves]
  | cons j js ih =>
      simp only [runMoves]
      rw [ih]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      omega

/-- **Necessary parity condition** to reach all-heads (`H = 2n`) from `H = n` via `js.length`
moves, each flipping `k` coins. -/
theorem p06_reach_all_heads_necessary (n k : ℤ) (js : List ℤ)
    (hreach : runMoves k n js = 2 * n) :
    (0 : ℤ) = (n + k * (js.length : ℤ)) % 2 := by
  have h := p06_parity_invariant k n js
  rw [hreach] at h
  omega

end Lutar.Putnam.Sampler
