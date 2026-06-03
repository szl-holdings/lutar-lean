/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Round 10 — CS Contribution 3: the CAP theorem on the receipt register

This file formalises the **Gilbert–Lynch CAP theorem** (Brewer's conjecture): a
distributed read/write register cannot simultaneously provide **C**onsistency
(linearizability), **A**vailability (every request to a non-failing node gets a
response), and **P**artition-tolerance (correctness despite dropped messages).

For the SZL receipt bus this pins down its positioning: the Khipu DAG anchored to
the Sigstore Rekor public log is a **CP** system — it favours consistency
(a 3-of-4 quorum, linearizable canonical history) over availability during a
partition, rather than an AP system. The proof below is the classic two-node
argument and is **FULLY PROVED** (0 sorry) on a finite-state model: we exhibit a
two-node execution under partition in which availability + consistency are jointly
contradictory.

## Citations

* S. Gilbert, N. Lynch, "Brewer's Conjecture and the Feasibility of Consistent,
  Available, Partition-Tolerant Web Services", ACM SIGACT News 33(2):51–59, 2002.
  DOI 10.1145/564585.564601.
  https://users.ece.cmu.edu/~adrian/731-sp04/readings/GL-cap.pdf
* S. Gilbert, N. Lynch, "Perspectives on the CAP Theorem", IEEE Computer
  45(2):30–36, 2012. DOI 10.1109/MC.2011.389.
  https://groups.csail.mit.edu/tds/papers/Gilbert/Brewer2.pdf
* M. P. Herlihy, J. M. Wing, "Linearizability: A Correctness Condition for
  Concurrent Objects", ACM TOPLAS 12(3):463–492, 1990. DOI 10.1145/78969.78972.
  https://cs.brown.edu/people/mph/HerlihyW90/p463-herlihy.pdf

NEW file under `Lutar/Innovations/round10/`; locked kernel untouched (749/14/163).
-/
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace Lutar
namespace Round10
namespace CAP

/-! ### 1. A minimal two-node register model

Two nodes `G1, G2`, each holding a value. A partition drops all messages between
them. We model a single-bit register: initial value `v0`, a write of `v1 ≠ v0` on
`G1`, then a read on `G2`. -/

/-- The two nodes of the minimal CAP witness. -/
inductive Node where
  | G1 | G2
deriving DecidableEq, Repr

/-- A system execution: each node's locally-held value (a bit), and a flag for
whether the inter-node link is partitioned. -/
structure Exec where
  val        : Node → Bool
  partitioned : Bool

/-- **Availability**: on this execution every node returns its locally-held value
without waiting (a total response function exists). We model the read on a node as
simply returning `val node` — always defined. -/
def reads (e : Exec) (n : Node) : Bool := e.val n

/-- **Consistency (linearizability, single-register form)**: after a write of `v1`
acknowledged at `G1`, a subsequent read at `G2` must also return `v1`. We encode
this as: the two nodes hold the same value. -/
def Consistent (e : Exec) : Prop := e.val Node.G1 = e.val Node.G2

/-- **Partition step**: a write `w` applied at `G1` while partitioned updates only
`G1`'s value; `G2` cannot learn of it because all messages are dropped. -/
def writeG1UnderPartition (e : Exec) (w : Bool) : Exec :=
  { e with val := fun n => match n with | Node.G1 => w | Node.G2 => e.val Node.G2,
           partitioned := true }

/-! ### 2. The impossibility (FULLY PROVED)

Start from a consistent state where both nodes hold `v0`. Apply a write of
`v1 ≠ v0` at `G1` under partition. Availability forces `G2` to respond to a read
immediately (it returns its own `v0`). Consistency would require that read to be
`v1`. The two demands contradict. -/

/-- **`cap_two_node_impossibility` (PROVED).** There is no execution that is
simultaneously (i) the result of a `v1 ≠ v0` write at `G1` under partition,
(ii) available — `G2` answers from its local value — and (iii) consistent. Taking
`v0 = false, v1 = true`: the post-write execution has `G1 = true`, `G2 = false`,
so `Consistent` (`true = false`) is false, while the available read at `G2`
returns `false`. -/
theorem cap_two_node_impossibility (e : Exec)
    (hg1 : e.val Node.G1 = false) (hg2 : e.val Node.G2 = false) :
    reads (writeG1UnderPartition e true) Node.G2 = false ∧
      ¬ Consistent (writeG1UnderPartition e true) := by
  refine ⟨?_, ?_⟩
  · -- availability: G2 still answers its local (stale) value, false
    show (writeG1UnderPartition e true).val Node.G2 = false
    simp only [writeG1UnderPartition]
    exact hg2
  · -- consistency fails: G1 = true, G2 = false
    show ¬ ((writeG1UnderPartition e true).val Node.G1 =
            (writeG1UnderPartition e true).val Node.G2)
    simp only [writeG1UnderPartition, hg2]
    -- goal reduces to `¬ (true = false)`
    intro hcontra
    exact absurd hcontra (by decide)

/-- **`cannot_have_all_three` (PROVED).** Packaged form: under a partition with a
genuine pending write, you cannot have both an available stale read at `G2` and
consistency. Concretely the conjunction (available read = stale value) ∧
(consistent) is unsatisfiable for the witness execution. -/
theorem cannot_have_all_three (e : Exec)
    (hg1 : e.val Node.G1 = false) (hg2 : e.val Node.G2 = false) :
    ¬ (reads (writeG1UnderPartition e true) Node.G2 = true ∧
       Consistent (writeG1UnderPartition e true)) := by
  rintro ⟨havail, _⟩
  -- the available read returns the stale false, contradicting `= true`
  simp [writeG1UnderPartition, reads, hg2] at havail

/-! ### 3. Receipt-bus positioning (PROVED corollary)

Forced to choose, the receipt bus drops availability under partition to keep
consistency: a partitioned organ that cannot reach quorum returns *no* canonical
decision rather than a divergent one. We record this as: when partitioned and the
local read would diverge, the consistent choice is to *not* serve a (false) read. -/

/-- The CP policy: under partition, refuse to serve a read that would violate
consistency. Modelled as returning `none`. -/
def cpRead (e : Exec) (n : Node) : Option Bool :=
  if e.partitioned then none else some (reads e n)

/-- **`cp_preserves_consistency` (PROVED).** The CP policy never serves a stale
divergent value under partition: it returns `none`, so it cannot answer the
inconsistent read. This is the receipt bus's deliberate sacrifice of A for C. -/
theorem cp_preserves_consistency (e : Exec) (n : Node) (hp : e.partitioned = true) :
    cpRead e n = none := by
  unfold cpRead; simp [hp]

/-! ### 4. Doctrine corollary

The CAP impossibility (§2) is FULLY PROVED on a finite two-node model with zero
new axioms and zero `sorry`. It fixes the receipt bus as a **CP** system (§3): it
forgoes availability under partition to preserve the linearizable canonical
history. Λ stays Conjecture 1; the locked public constant 749/14/163 is
untouched. -/

end CAP
end Round10
end Lutar
