/-
================================================================================
  LedgerIdentities.lean
  SZL Holdings — machine-checked CHECKED-class identities from the
  szl-formula-ledger corpus (formulas/corpus.json).

  Doctrine posture: EXPERIMENTAL / additive. This file is NOT folded into the
  locked Doctrine-v11 baseline (749/14/163 @ c7c0ba17) and does NOT change the
  locked-proven set {F1,F4,F7,F11,F12,F18,F19,F22} (still exactly 8, enforced by
  Lutar.Uniqueness.AxiomCheck.locked_count_eight). It touches NEITHER Λ
  (Conjecture-1) NOR Khipu BFT safety (Conjecture-2): the one BFT result below
  is the *arithmetic quorum-overlap* only, explicitly NOT the safety property.

  What this adds: the ledger currently labels these SYMBOLIC identities
  "machine-checkable with sympy". This module upgrades them to Lean-KERNEL
  proofs (strictly stronger than a sympy numeric/symbolic check), each sorry-free
  and Mathlib-lemma-backed.
================================================================================
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

namespace SZL.Ledger.Identities

/-! ### L1 — Cauchy–Schwarz (n=2) via the Lagrange identity.
Ledger id `cauchy-schwarz-2d`. -/

/-- Lagrange identity (2D): the exact algebraic decomposition. -/
theorem cauchy_schwarz_2d_lagrange (a₁ a₂ b₁ b₂ : ℝ) :
    (a₁ * b₁ + a₂ * b₂) ^ 2
      = (a₁ ^ 2 + a₂ ^ 2) * (b₁ ^ 2 + b₂ ^ 2) - (a₁ * b₂ - a₂ * b₁) ^ 2 := by
  ring

/-- Cauchy–Schwarz inequality (2D), a corollary of the Lagrange identity. -/
theorem cauchy_schwarz_2d_ineq (a₁ a₂ b₁ b₂ : ℝ) :
    (a₁ * b₁ + a₂ * b₂) ^ 2 ≤ (a₁ ^ 2 + a₂ ^ 2) * (b₁ ^ 2 + b₂ ^ 2) := by
  nlinarith [sq_nonneg (a₁ * b₂ - a₂ * b₁)]

/-! ### L2 — AM–GM (2 variables). Ledger id `A4-bounded-amgm`. -/

/-- Polynomial AM–GM: `4ab ≤ (a+b)²`. -/
theorem amgm_two_poly (a b : ℝ) : 4 * a * b ≤ (a + b) ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- The exact AM–GM slack term (the ledger's `(√a−√b)²/2` analogue at the
squared level): `(a+b)² − 4ab = (a−b)²`. -/
theorem amgm_two_slack (a b : ℝ) : (a + b) ^ 2 - 4 * a * b = (a - b) ^ 2 := by
  ring

/-- Real-sqrt AM–GM: for nonnegative reals, `√(ab) ≤ (a+b)/2`. -/
theorem amgm_two_sqrt (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  rw [show (a + b) / 2 = Real.sqrt (((a + b) / 2) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg (a - b)]

/-! ### L3 — Egyptian Horus-Eye unit-fraction sum. Ledger id `TH_V18_04`. -/

/-- Horus-Eye: `1/2 + 1/4 + 1/8 + 1/16 + 1/32 + 1/64 = 63/64`. -/
theorem horus_eye_sum :
    (1 : ℚ) / 2 + 1 / 4 + 1 / 8 + 1 / 16 + 1 / 32 + 1 / 64 = 63 / 64 := by
  norm_num

/-! ### L4 — Kraft equality for the complete prefix code {1,2,3,3}.
Ledger id `TH_V18_03`. -/

/-- Kraft (complete code): `2⁻¹ + 2⁻² + 2⁻³ + 2⁻³ = 1`. -/
theorem kraft_prefix_complete :
    (1 : ℚ) / 2 + 1 / 4 + 1 / 8 + 1 / 8 = 1 := by
  norm_num

/-! ### L5 — Fisher–Rao self-distance. Ledger id `fisher-rao-identity`. -/

/-- Fisher–Rao self-distance vanishes: `d(p,p) = 2·arccos(1) = 0`. -/
theorem fisher_rao_self_zero : 2 * Real.arccos 1 = 0 := by
  rw [Real.arccos_one]; ring

/-! ### L6 — Shor [[9,1,3]] code arithmetic. Ledger id `shor-913-distance`. -/

/-- Correctable errors: `t = ⌊(d−1)/2⌋ = 1` for distance `d = 3`. -/
theorem shor_913_correctable : (3 - 1) / 2 = 1 := by decide

/-- Classical Singleton consistency: `d ≤ n − k + 1` for `[[9,1,3]]`
(`3 ≤ 9 − 1 + 1`). -/
theorem shor_913_singleton_ok : 3 ≤ 9 - 1 + 1 := by decide

/-! ### L7 — Completing the square. Ledger id `quadratic-completion`. -/

/-- al-Khwārizmī completion: `x² + b·x + c = (x + b/2)² + (c − b²/4)`. -/
theorem quadratic_completion (x b c : ℝ) :
    x ^ 2 + b * x + c = (x + b / 2) ^ 2 + (c - b ^ 2 / 4) := by
  ring

/-! ### L8 — Byzantine quorum ARITHMETIC. Ledger id `byzantine-n3f1`.
HONESTY: this proves ONLY the arithmetic quorum-overlap. The BFT *safety*
property itself is **Conjecture-2** and is NOT proven here or anywhere. -/

/-- With `f` faults, `n = 3f+1` nodes, quorum `q = 2f+1`: two quorums overlap in
`2q − n = f + 1` nodes — so any two quorums share at least one non-faulty node.
Arithmetic only; BFT safety stays Conjecture-2. -/
theorem bft_quorum_overlap (f : ℕ) : 2 * (2 * f + 1) - (3 * f + 1) = f + 1 := by
  omega

/-- The overlap strictly exceeds the fault budget `f` (`f + 1 > f`), the
arithmetic precondition behind quorum intersection. Still NOT BFT safety. -/
theorem bft_overlap_exceeds_faults (f : ℕ) : f < 2 * (2 * f + 1) - (3 * f + 1) := by
  omega

end SZL.Ledger.Identities
