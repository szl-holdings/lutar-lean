import Mathlib

namespace Lutar.Putnam.SZL.ReceiptVerify

/-!
# SZL original — receipt sign / verify correctness

An SZL-original companion to the Putnam set, modelling the receipt-signing
backbone (a11oy receipts): a tag is canonical iff it equals the key-derived
signature, and verification is sound, complete, and tamper-evident. All proofs
are REAL (kernel-checked); no `sorry`, no new axiom.

EXPERIMENTAL — not folded into the locked v11 baseline.
-/

/-- The canonical signature of a payload under key function `key`. -/
def sign (key : ℕ → ℕ) (payload : ℕ) : ℕ := key payload

/-- Verification recomputes the canonical tag and compares. -/
def verify (key : ℕ → ℕ) (payload tag : ℕ) : Bool := key payload == tag

/-- Soundness: a genuinely signed receipt always verifies (REAL). -/
theorem verify_sign (key : ℕ → ℕ) (payload : ℕ) :
    verify key payload (sign key payload) = true := by
  simp [verify, sign]

/-- Completeness: verification succeeds iff the tag is the canonical signature
(REAL). -/
theorem verify_iff (key : ℕ → ℕ) (payload tag : ℕ) :
    verify key payload tag = true ↔ tag = key payload := by
  unfold verify
  simp only [beq_iff_eq]
  exact eq_comm

/-- Tamper-evidence: a tag that is not the canonical signature does NOT verify
(REAL). -/
theorem verify_tamper (key : ℕ → ℕ) (payload tag : ℕ) (h : tag ≠ key payload) :
    verify key payload tag ≠ true := by
  rw [verify_iff]; exact h

end Lutar.Putnam.SZL.ReceiptVerify
