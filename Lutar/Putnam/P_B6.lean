import Mathlib

namespace Lutar.Putnam.P_B6

/-!
## Putnam 2025 B6 — r_opt = 1/4 (official MAA/Kedlaya solution)

The earlier code in this file encoded `r_opt = 1/2`, which is FALSE.
The correct optimal r is 1/4; see MAA Putnam 2025 archive and Kedlaya's
solution PDF at https://kskedlaya.org/putnam-archive/2025solutions.pdf.

Proof: pending. The previous proof attempt was for the wrong statement
and cannot be salvaged.
-/

/-!
# Putnam 2025 B6

**Problem:** Let ℕ = {1,2,3,...}. Find the largest real constant r such that there
exists a function g:ℕ→ℕ such that g(n+1) - g(n) ≥ (g(g(n)))^r for all n ∈ ℕ.

**Answer:** r = 1/4.

**Official source:** The MAA / Kedlaya 2025 official solutions state:
"B6. The largest such constant is r = 1/4. This value works because we may take
g(n) = n^2." (Solutions to the 86th William Lowell Putnam Mathematical Competition,
https://kskedlaya.org/putnam-archive/2025s.pdf; MAA archive
https://maa.org/putnam-competition/.)

Note: the previous version of this file encoded `r_opt = 1/2`. That statement is
false. The file's own heuristic comments (balance α-1 = rα², maximised at α = 2 giving
r = (α-1)/α² = 1/4) had already derived the correct value 1/4 but were overridden by
an incorrect "trust the official source says 1/2" note. The official source says 1/4.

@[source] https://kskedlaya.org/putnam-archive/2025s.pdf
@[source] https://maa.org/putnam-competition/
@[difficulty] 5
-/

-- The answer (corrected to the official value)
def r_opt : ℝ := 1/4

-- Main statement: r = 1/4 is the supremum
theorem putnam_B6_correct :
    -- Part 1: r = 1/4 is achievable
    (∃ g : ℕ → ℕ, ∀ n : ℕ, 0 < n →
      (g (n+1) : ℝ) - g n ≥ (g (g n) : ℝ) ^ r_opt) ∧
    -- Part 2: no r > 1/4 is achievable
    (∀ r : ℝ, r_opt < r →
      ¬ ∃ g : ℕ → ℕ, (∀ n : ℕ, 0 < n →
        (g (n+1) : ℝ) - g n ≥ (g (g n) : ℝ) ^ r)) := by
  -- Proof pending. The previous proof attempt targeted the wrong statement
  -- (r = 1/2) and cannot be salvaged. The official construction g(n) = n^2
  -- gives the achievability half; the impossibility half for r > 1/4 follows
  -- the official argument. Neither is discharged here.
  sorry

example : r_opt = (1:ℝ)/4 := rfl

/-!
## Summary
- `putnam_B6_correct`: TRACKED — 1 root sorry on the main theorem.
- `r_opt`: REAL definition, corrected to the official value 1/4.
- Sorry count: 1 (root sorry on `putnam_B6_correct`).
- Correction note: this file previously stated `r_opt = 1/2`, which is false per the
  official MAA/Kedlaya 2025 solution (r = 1/4). The statement is now correct; the proof
  is not attempted.
-/

end Lutar.Putnam.P_B6
