-- SZL_v5.lean  — Lambda-invariant closure theorems
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

/-- Monotonicity: more coherence (charge ≥ 0 fixed) never decreases Lambda. -/
theorem lambda_mono_in_coherence (c1 c2 q : Real)
    (hq : q ≥ 0) (h : c1 ≤ c2) :
    lambdaVal ⟨c1, q⟩ ≤ lambdaVal ⟨c2, q⟩ := by
  unfold lambdaVal
  exact mul_le_mul_of_nonneg_right h hq

end SZL
