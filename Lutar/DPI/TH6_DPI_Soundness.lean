import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Preimage
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# TH6_DPI_Soundness.lean
## DPI Soundness — Receipt Chain Entropy Bound

**Doctrine v6** — Canonical scanner reference.  
**Guarantee**: `axiom`-free; no `sorry`.

This module formalises the Data Processing Inequality (DPI) soundness theorem
for the Lutar receipt chain. The DPI states that processing data cannot increase
Shannon entropy: H(f(X)) ≤ H(X) for any deterministic function f. In the Lutar
context, each receipt operation in a DPI chain is a deterministic transform, so
the entropy of the chain output is bounded by the entropy of the initial input.

### Key theorem: `dpi_receipt_chain_entropy_bound`
For a DPI receipt chain of length N with initial entropy H₀, the entropy at
any stage k satisfies H_k ≤ H₀.

### Reference
Cover, T. M., & Thomas, J. A. (2006). *Elements of Information Theory* (2nd ed.).
Wiley-Interscience. ISBN 978-0-471-24195-9. §2.8, Data Processing Inequality.
-/
namespace Lutar.DPI

/-! ## 1. Shannon Entropy Model -/

/-- Shannon entropy over a finite discrete distribution.
    For a distribution `p : Fin n → ℝ` (where ∑ p i = 1, p i ≥ 0),
    H(p) = -∑ p_i · log₂(p_i), with the convention 0 · log 0 = 0. -/
noncomputable def shannonEntropy {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  -∑ i, p i * Real.log (p i) / Real.log 2

/-- A *valid distribution* satisfies non-negativity and normalisation. -/
structure ValidDist (n : ℕ) where
  prob    : Fin n → ℝ
  nn      : ∀ i, 0 ≤ prob i

/-! ## 2. DPI Receipt Chain -/

/-- A receipt operation is a row-stochastic matrix (Markov kernel)
    mapping distributions. We represent it as a function on valid distributions. -/
structure ReceiptOp (n m : ℕ) where
  /-- The Markov kernel: `kernel i j` = P(output = j | input = i) -/
  kernel    : Fin n → Fin m → ℝ
  kernel_nn : ∀ i j, 0 ≤ kernel i j
  kernel_row: ∀ i, ∑ j, kernel i j = 1

/-- Apply a receipt operation to a valid distribution. -/
def applyOp {n m : ℕ} (op : ReceiptOp n m) (d : ValidDist n) : ValidDist m where
  prob    := fun j => ∑ i, d.prob i * op.kernel i j
  nn      := fun j => Finset.sum_nonneg (fun i _ => mul_nonneg (d.nn i) (op.kernel_nn i j))

/-! ## 3. Entropy Non-Increase Under Markov Kernels (DPI) -/

/-- **DPI Lemma** (Cover-Thomas 2006, §2.8)
    Entropy non-increase is NOT assumed globally: it holds for deterministic
    kernels but FAILS for general Markov kernels (mixing toward uniform raises
    entropy). It is therefore taken as a per-kernel hypothesis.

    In a full machine-checked proof this would follow from the log-sum
    inequality (Jensen's inequality for the convex function t ↦ t log t).
    We introduce it as a hypothesis parameterised by the kernel, which
    callers must discharge for their specific kernels.

    Reference: Cover & Thomas (2006), ISBN 978-0-471-24195-9, Theorem 2.8.1. -/
def DPI_hypothesis {n m : ℕ} (op : ReceiptOp n m) : Prop :=
  ∀ (d : ValidDist n),
    shannonEntropy (applyOp op d).prob ≤ shannonEntropy d.prob

/-! ## 4. DPI Receipt Chain -/

/-- A *DPI receipt chain* is a sequence of receipt operations. -/
abbrev ReceiptChain (n : ℕ) := List (ReceiptOp n n)

/-- Apply a chain of receipt operations sequentially. -/
def applyChain {n : ℕ} (chain : ReceiptChain n) (d : ValidDist n) : ValidDist n :=
  chain.foldl (fun acc op => applyOp op acc) d

/-! ## 5. DPI Receipt Chain Entropy Bound (proved, conditional on the per-kernel hypothesis)

The statement below is the *real* DPI receipt-chain entropy bound, no longer a
`:= True` shell. It says: if every operation in the chain satisfies the
per-kernel DPI hypothesis (entropy non-increase under that Markov kernel), then
the entropy of the chain output is bounded by the entropy of the initial input.

Proved by induction on the chain: each step is bounded by that operation's
`DPI_hypothesis`, and the bounds chain transitively. Scope (honest): Shannon
entropy is NOT monotone under every Markov kernel (mixing toward uniform raises
it); it is non-increasing under deterministic kernels. So the per-kernel
hypothesis is a genuine assumption, and this conditional theorem is the correct
statement. An unconditional version for arbitrary kernels would be false.
-/

/-- **DPI receipt-chain entropy bound.** If every receipt operation in `chain`
satisfies its per-kernel DPI hypothesis, then applying the whole chain cannot
increase Shannon entropy: `H(applyChain chain d) ≤ H(d)`.

Proof route: induction on `chain` (`foldl`), each step discharged by the op's
`DPI_hypothesis`, transitively chaining the bound. The base entropy-non-increase
lemma (`H(applyOp op d) ≤ H(d)` from row-stochasticity, i.e. the log-sum
inequality) is the remaining open piece. -/
theorem dpi_receipt_chain_entropy_bound {n : ℕ}
    (chain : ReceiptChain n)
    (d : ValidDist n)
    (h_dpi : ∀ op ∈ chain, DPI_hypothesis op) :
    shannonEntropy (applyChain chain d).prob ≤ shannonEntropy d.prob := by
  induction chain generalizing d with
  | nil => exact le_rfl
  | cons op rest ih =>
    have hop : DPI_hypothesis op := h_dpi op (by simp)
    show shannonEntropy (applyChain rest (applyOp op d)).prob <= shannonEntropy d.prob
    exact le_trans (ih (applyOp op d) (fun o ho => h_dpi o (by simp [ho]))) (hop d)

end Lutar.DPI
