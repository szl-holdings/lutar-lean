import Mathlib

namespace Lutar.Putnam.P_A3

/-!
## Putnam 2025 A3 — Bob wins for all n ≥ 1 (official MAA/Kedlaya solution)

The earlier code in this file encoded "Alice wins", which is FALSE.
The correct answer is that BOB has a winning strategy for all n ≥ 1; see the
MAA Putnam 2025 archive and Kedlaya's solution PDF at
https://kskedlaya.org/putnam-archive/2025solutions.pdf.

Proof: pending. The previous statement encoded the wrong winner and cannot be
salvaged.
-/

/-!
# Putnam 2025 A3

**Problem:** Alice and Bob play a game with a string of n digits, each 0, 1, or 2.
Initially all digits are 0. A legal move: add or subtract 1 from one digit, creating
a new string not seen before. A player with no legal move loses. Alice goes first.
For each n ≥ 1, determine which player has a guaranteed winning strategy.

**Answer:** Bob wins for all n ≥ 1.

**Official source:** The MAA / Kedlaya 2025 official solutions state:
"A3. Bob has a winning strategy for all n ≥ 1." The strategy uses a perfect matching
of the graph G on vertices {0,1,2}^n \ {(0,…,0)} with edges between strings differing
by ±1 in a single position: whenever Alice moves into a matched vertex, Bob replies with
its partner, so Bob always has a move and Alice eventually runs out.
(Solutions to the 86th William Lowell Putnam Mathematical Competition,
https://kskedlaya.org/putnam-archive/2025s.pdf; MAA archive
https://maa.org/putnam-competition/.)

Note: the previous version of this file encoded "Alice wins". That is false. The file's
own n = 1 case analysis (from 0 Alice can only go to 1; Bob goes to 2; Alice is stuck)
had already derived "Bob wins for n = 1" but was overridden by an incorrect
"official answer says Alice wins" note. The official answer is Bob.

@[source] https://kskedlaya.org/putnam-archive/2025s.pdf
@[source] https://maa.org/putnam-competition/
@[difficulty] 3
-/

-- Model: digits ∈ {0,1,2}, string of length n. A position is a function Fin n → Fin 3.

/-- The number of positions in {0,1,2}^n is 3^n. -/
lemma card_positions (n : ℕ) : Fintype.card (Fin n → Fin 3) = 3 ^ n := by
  simp [Fintype.card_fun, Fintype.card_fin]

/-- 3^n is always odd. (So {0,1,2}^n \ {(0,…,0)} has an even number of vertices,
    which is what permits the perfect matching underlying Bob's strategy.) -/
lemma three_pow_odd (n : ℕ) : Odd (3 ^ n) :=
  Odd.pow (by norm_num : Odd 3)

/-- Main theorem: Bob (the second player) wins for all n ≥ 1.

    The statement below is a `True` shell — the game-theoretic content (existence of a
    winning strategy for Bob via a perfect matching of {0,1,2}^n \ {0^n}) is NOT encoded.
    A faithful encoding plus the matching argument is pending. The answer asserted in the
    docstring ("Bob wins for all n ≥ 1") matches the official MAA/Kedlaya solution; the
    earlier "Alice wins" answer was false and has been corrected. -/
theorem putnam_A3_correct (n : ℕ) (hn : 1 ≤ n) :
    -- TODO: replace `True` with the faithful statement
    --   "Bob (second player) has a winning strategy for the {0,1,2}^n move-game".
    -- This requires a combinatorial-game / Sprague–Grundy formalisation not present here.
    True := by
  -- Proof pending. Body left as a placeholder; the previous attempt asserted the wrong
  -- winner and cannot be salvaged.
  sorry

example : (3 : ℕ) ^ 1 = 3 := by norm_num

/-!
## Summary
- `putnam_A3_correct`: TRACKED — `True` shell (problem NOT encoded), root sorry on body.
- `card_positions`: REAL proof (simp).
- `three_pow_odd`: REAL proof (Odd.pow).
- Sorry count: 1 (root sorry on `putnam_A3_correct`).
- Correction note: this file previously stated "Alice wins", which is false per the
  official MAA/Kedlaya 2025 solution (Bob wins for all n ≥ 1). The stated answer is now
  correct; the theorem is still a `True` shell and the strategy is not proved.
-/

end Lutar.Putnam.P_A3
