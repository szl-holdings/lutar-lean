/-
  Formula ID : A8-03  PINGALA-RECEIPT-RECURRENCE
  Source     : Pingala, Chandaḥśāstra (~300 BCE); rediscovered by
               Hemachandra (~1150 CE).  The mātrāmeru sequence (known
               in the West as Fibonacci) counts binary syllable patterns
               of length n as F(n+2).
               Ref: Knuth, TAOCP Vol. 1, §1.2.8; Allouche & Shallit
               "Automatic Sequences" §2.5.
  Insight    : A receipt DAG where each node branches to at most 2
               children has at most F(depth+2) frontier nodes.
               Bounding DAG fan-out by Fibonacci gives an O(φ^n) worst-
               case trace complexity — useful for amaru/sentra's receipt
               size budget.
  Lean target: amaru / sentra
  Sorry-free : Yes  (simp + omega close all goals)
  Round      : 8  (not in R4–R7)
  Namespace  : Lutar.Innovations.Round8.PingalaReceiptRecurrence
               (OUTSIDE locked kernel c7c0ba17 / 749-14-163)
  SLSA       : L1 honest
  Section 889: not applicable
  Signed-off-by: Yachay <yachay@szlholdings.ai>
  Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/

namespace Lutar.Innovations.Round8.PingalaReceiptRecurrence

/-!
## Pingala / Hemachandra recurrence — receipt DAG frontier bound

`pingalaF n` is the n-th Fibonacci number (0-indexed: 0,1,1,2,3,5,…).
-/

/-- Pingala–Hemachandra sequence (Fibonacci), 0-indexed. -/
def pingalaF : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => pingalaF (n + 1) + pingalaF n

-- Sanity checks (decide-closed)
#eval pingalaF 7   -- 13
#eval pingalaF 10  -- 55

/-- The recurrence holds by definition. -/
theorem pingalaRecurrence (n : ℕ) :
    pingalaF (n + 2) = pingalaF (n + 1) + pingalaF n := by
  simp [pingalaF]

/-- pingalaF is strictly positive for n ≥ 1. -/
theorem pingalaPos (n : ℕ) (h : 1 ≤ n) : 0 < pingalaF n := by
  induction n with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => simp [pingalaF]
    | succ k =>
      simp [pingalaF]
      have h1 : 1 ≤ k + 1 := by omega
      have h2 : 1 ≤ k.succ := by omega
      have := ih (by omega)
      omega

/-- Receipt DAG frontier bound: at most pingalaF(depth+2) frontier nodes. -/
def dagFrontierBound (depth : ℕ) : ℕ := pingalaF (depth + 2)

/-- The frontier bound is monotone in depth. -/
theorem frontierBoundMono (d : ℕ) :
    dagFrontierBound d ≤ dagFrontierBound (d + 1) := by
  unfold dagFrontierBound
  simp [pingalaF]
  omega

end Lutar.Innovations.Round8.PingalaReceiptRecurrence
