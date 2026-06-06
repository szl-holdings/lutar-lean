/-
# WAVE 7 — Mathlib-DEPENDENT substrate guarantees (kernel-checked by lutar-lean CI)

These are pure term/tactic instantiations of named Mathlib theorems at the pinned rev
`d7317655e2826dc1f1de9a0c138db2775c4bb841` (Mathlib v4.13.0). They are wired into the
`lake build` kernel-check root, so CI re-verifies them and emits `#print axioms`. Expected
dependency is the standard Mathlib trio `[propext, Classical.choice, Quot.sound]` — NO
`sorryAx`, NO declared Lutar axioms.

HONESTY: nothing here proves Λ uniqueness (still Conjecture 1). These are honest finite
lemmas grounded in published results, NOT analytic limit theorems.

## Citations (proof-technique provenance + Mathlib lemma used)
- W7-1 graph degree-sum / functional isomorphism-invariance — the graph2nn program
  (You, Leskovec, He, Xie, ICML 2020, arXiv:2007.06559): clustering coefficient & average
  path length are isomorphism-invariant graph functionals. The discrete BACKBONE is that
  any vertex-summed functional is invariant under a vertex relabeling (graph automorphism).
  Mathlib: `Equiv.sum_comp` (additive of `Equiv.prod_comp`). This is the F-G6 core, and
  the additive companion of the in-tree `GraphLambda` F-G4 product invariance.
- W7-5 PAC-Bayes / Jensen-direction averaging envelope — McAllester, *PAC-Bayesian model
  averaging* (COLT 1999, doi:10.1145/307400.307435): an averaged/aggregated risk is
  controlled by its component extremes. The discrete backbone: `∑ f ≤ card • max` and
  `card • min ≤ ∑ f`, i.e. `min ≤ average ≤ max`. Mathlib: `Finset.sum_le_card_nsmul`,
  `Finset.card_nsmul_le_sum`. Powers cost-aware model routing (a11oy Model Router;
  GraphRouter, arXiv:2410.03834).
-/
-- Mathlib v4.18.0: `Mathlib/Algebra/BigOperators/Group/Finset.lean` was split into a
-- `Finset/` directory; the `Finset.sum`/`Finset.prod` API (incl. `Equiv.sum_comp`,
-- `Finset.sum_le_card_nsmul`, `Finset.card_nsmul_le_sum`) now lives under `.Finset.Basic`.
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Equiv.Basic

namespace Wave7.MathlibCore

open Finset

/-! ## W7-1 — Vertex-summed graph functional is isomorphism-invariant (F-G6 core). -/

/-- Degree of a vertex `v` under a `Bool` adjacency `A` on a finite vertex type `V`:
    the number of neighbours (size of the `true`-neighbour finset). -/
noncomputable def degree {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → V → Bool) (v : V) : ℕ :=
  (Finset.univ.filter (fun w => A v w = true)).card

/-- The total degree sum (handshake quantity, `= 2·|E|` for a symmetric adjacency). -/
noncomputable def degreeSum {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → V → Bool) : ℕ :=
  ∑ v, degree A v

/-- **W7-1a — `Equiv.sum_comp` re-export: a vertex-summed functional is invariant under
    relabeling.** For any vertex bijection `σ : V ≃ V` (a relabeling / graph automorphism
    on the labels) and any `ℕ`-valued vertex functional `f`, `∑ v, f (σ v) = ∑ v, f v`.
    The combinatorial backbone of isomorphism-invariance of every degree-based graph
    statistic (graph2nn). -/
theorem w7_1a_vertexSum_relabel_invariant {V : Type*} [Fintype V]
    (σ : V ≃ V) (f : V → ℕ) :
    (∑ v, f (σ v)) = ∑ v, f v :=
  Equiv.sum_comp σ f

/-- **W7-1 — the degree-sum graph functional is invariant under a degree-preserving
    relabeling.** If a relabeling `σ` carries the degree function along
    (`degree A (σ v) = degree A' v`, the hypothesis recorded by an isomorphism that
    preserves adjacency), then the two graphs have the same handshake quantity. -/
theorem w7_1_degreeSum_iso_invariant {V : Type*} [Fintype V] [DecidableEq V]
    (A A' : V → V → Bool) (σ : V ≃ V)
    (hdeg : ∀ v, degree A (σ v) = degree A' v) :
    degreeSum A = degreeSum A' := by
  unfold degreeSum
  calc (∑ v, degree A v) = ∑ v, degree A (σ v) := (Equiv.sum_comp σ (degree A)).symm
    _ = ∑ v, degree A' v := Finset.sum_congr rfl (fun v _ => hdeg v)

/-! ## W7-5 — Average envelope (PAC-Bayes / Jensen direction): min ≤ average ≤ max. -/

/-- **W7-5a — aggregate ≤ |support|·max (the "average ≤ worst-case" half).** If every
    component score `f i ≤ M` on a finite support `s`, then `∑ f ≤ |s|·M`. The discrete
    backbone of a PAC-Bayes / cost-aware-routing upper envelope: the averaged risk never
    exceeds the worst component. -/
theorem w7_5a_sum_le_card_max {ι : Type*} (s : Finset ι) (f : ι → ℕ) (M : ℕ)
    (h : ∀ i ∈ s, f i ≤ M) :
    (∑ i ∈ s, f i) ≤ s.card • M :=
  Finset.sum_le_card_nsmul s f M h

/-- **W7-5b — |support|·min ≤ aggregate (the "best-case ≤ average" half).** If every
    component `m ≤ f i`, then `|s|·m ≤ ∑ f`. Together with W7-5a this brackets the average
    in `[min, max]` — the two-sided routing envelope. -/
theorem w7_5b_card_min_le_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ) (m : ℕ)
    (h : ∀ i ∈ s, m ≤ f i) :
    s.card • m ≤ ∑ i ∈ s, f i :=
  Finset.card_nsmul_le_sum s f m h

/-- **W7-5 — two-sided average envelope.** On a nonempty finite support with `m ≤ f i ≤ M`
    for every component, the aggregate is bracketed: `|s|·m ≤ ∑ f ≤ |s|·M`. Dividing by
    `|s|` is the `min ≤ average ≤ max` statement behind cost-aware model routing. -/
theorem w7_5_average_envelope {ι : Type*} (s : Finset ι) (f : ι → ℕ) (m M : ℕ)
    (hlo : ∀ i ∈ s, m ≤ f i) (hhi : ∀ i ∈ s, f i ≤ M) :
    s.card • m ≤ (∑ i ∈ s, f i) ∧ (∑ i ∈ s, f i) ≤ s.card • M :=
  ⟨w7_5b_card_min_le_sum s f m hlo, w7_5a_sum_le_card_max s f M hhi⟩

end Wave7.MathlibCore

-- ## Wave-7 Mathlib-dependent axiom disclosure (CI prints these in the build log).
#print axioms Wave7.MathlibCore.w7_1a_vertexSum_relabel_invariant
#print axioms Wave7.MathlibCore.w7_1_degreeSum_iso_invariant
#print axioms Wave7.MathlibCore.w7_5a_sum_le_card_max
#print axioms Wave7.MathlibCore.w7_5b_card_min_le_sum
#print axioms Wave7.MathlibCore.w7_5_average_envelope
