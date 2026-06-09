import Mathlib

namespace Lutar.Putnam.P_A3

/-!
# Putnam 2025 A3

**Problem.** Alice and Bob play with a string of `n` digits, each in `{0,1,2}`,
all initially `0`. A legal move adds or subtracts `1` from a single digit,
producing a string never seen before in the game. A player with no legal move
loses; Alice moves first. For each `n ≥ 1`, determine which player has a winning
strategy.

**Corrected answer.** The SECOND player (Bob) wins for every `n ≥ 1`.

*Drift note.* An earlier docstring of this file claimed "Alice (first player)
wins". That is INCONSISTENT with the `n = 1` case: the position graph is the
path `0 — 1 — 2`, whose matching `{1, 2}` misses the start `0`, so the second
player always has the matched reply (Bob wins). We formalize the corrected
answer.

**Honest status: OPEN** — faithful statement of the corrected answer via a
second-player pairing strategy, proof DEFERRED (`sorry`). The two combinatorial
helpers `card_positions` and `three_pow_odd'` are REAL (kernel-checked).
-/

/-- A position: a length-`n` string of digits in `{0,1,2}`. -/
abbrev Pos (n : ℕ) := Fin n → Fin 3

/-- The total number of positions is `3 ^ n` (REAL). -/
theorem card_positions (n : ℕ) : Fintype.card (Pos n) = 3 ^ n := by
  rw [Fintype.card_pi]
  simp

/-- `3 ^ n` is odd (REAL). -/
theorem three_pow_odd' (n : ℕ) : Odd ((3 : ℕ) ^ n) := (by decide : Odd (3 : ℕ)).pow

/-- Two positions are adjacent iff they differ by ±1 (no wraparound) in exactly
one coordinate. -/
def Adj {n : ℕ} (p q : Pos n) : Prop :=
  ∃ i : Fin n, (∀ j, j ≠ i → p j = q j) ∧
    ((p i).val + 1 = (q i).val ∨ (q i).val + 1 = (p i).val)

/-- The start position: all zeros. -/
def startPos (n : ℕ) : Pos n := fun _ => 0

/-- A second-player winning pairing strategy: an adjacency-respecting,
fixed-point-free involution on the non-start positions. Its existence is the
combinatorial certificate that the second player (Bob) wins the no-repetition
move game. -/
def SecondPlayerWins (n : ℕ) : Prop :=
  ∃ σ : Pos n → Pos n,
    (∀ p, p ≠ startPos n → Adj p (σ p)) ∧
    (∀ p, p ≠ startPos n → σ p ≠ startPos n) ∧
    (∀ p, p ≠ startPos n → σ (σ p) = p) ∧
    (∀ p, p ≠ startPos n → σ p ≠ p)

/-- Faithful statement of the corrected Putnam 2025 A3 answer (OPEN: proof
deferred). -/
theorem putnam_A3_correct (n : ℕ) (hn : 1 ≤ n) : SecondPlayerWins n := by
  sorry

end Lutar.Putnam.P_A3
