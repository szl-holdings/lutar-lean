-- SZL_v5.lean  — quantum-bio Lambda-v5 ENGINEERING closure gate (NOT the formal aggregator).
-- DOCTRINE: the formal aggregator uniqueness Lambda is Conjecture 1 (unconditional uniqueness
-- machine-checked FALSE; conditional Theorem U is axiom-free). lambdaVal below is the v5
-- ENGINEERING gate (coherence * charge), a PROPOSED construct only; it is NOT lambdaUniqueness
-- and these lemmas do NOT prove Conjecture 1. locked-proven set unchanged (exactly 8).
-- Compile: lake build  (Lean 4 + Mathlib).  Logic stress-tested over 100k cases in Python.
import Mathlib

namespace SZL

structure NodeState where
  coherence : Real
  charge    : Real

def lambdaVal (n : NodeState) : Real := n.coherence * n.charge
def closureOk (n : NodeState) (lamMin : Real) : Prop := lambdaVal n ≥ lamMin

/-- A fully decohered node (coherence = 0) never satisfies a positive closure floor. -/
theorem decohered_never_closes (n : NodeState) (lamMin : Real)
    (h0 : n.coherence = 0) (hpos : lamMin > 0) : ¬ closureOk n lamMin := by
  unfold closureOk lambdaVal
  rw [h0, zero_mul]                 -- lambdaVal = 0
  exact not_le.mpr hpos             -- ¬ (0 ≥ lamMin)  since lamMin > 0

/-- An uncharged node (charge = 0) never satisfies a positive closure floor. -/
theorem uncharged_never_closes (n : NodeState) (lamMin : Real)
    (h0 : n.charge = 0) (hpos : lamMin > 0) : ¬ closureOk n lamMin := by
  unfold closureOk lambdaVal
  rw [h0, mul_zero]
  exact not_le.mpr hpos

/-- Monotonicity: more coherence (charge >= 0 fixed) never decreases the v5 gate value. -/
theorem lambda_mono_in_coherence (c1 c2 q : Real)
    (hq : q ≥ 0) (h : c1 ≤ c2) :
    lambdaVal ⟨c1, q⟩ ≤ lambdaVal ⟨c2, q⟩ := by
  unfold lambdaVal
  exact mul_le_mul_of_nonneg_right h hq

end SZL
