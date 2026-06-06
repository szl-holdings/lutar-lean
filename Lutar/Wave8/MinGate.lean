/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave8/MinGate.lean — L2: Min-Gate Uniqueness (deny-by-default aggregator)

The a11oy / a11oy-Code policy router aggregates per-policy confidence scores with
a *deny-by-default* gate. We prove an HONEST uniqueness result (in deliberate
contrast to the machine-checked-FALSE Λ uniqueness, Conjecture 1): under a small
set of design axioms, the ONLY deny-by-default aggregator is the pointwise
minimum (the conjunctive / AND gate).

Scores are modeled as `Nat` (fixed-point confidence units, e.g. permille in
[0,1000]); this keeps the result Lean-core / Mathlib-free and fully checkable.

## Axioms on a deny-by-default aggregator `D : (Fin (n+1) → Nat) → Nat`
- (Mono)  monotone: `(∀ i, u i ≤ w i) → D u ≤ D w`   (more evidence never hurts)
- (Diag)  idempotent on constants: `D (fun _ => x) = x`
- (Cons)  conservative: `D v ≤ vmin v`               (never exceeds the weakest input)

## What is proven
- `vmin_le`              — the vector minimum lower-bounds every component.
- `min_gate_lower_bound` — (Mono)+(Diag) force `vmin v ≤ D v`.
- `deny_by_default_unique` — (Mono)+(Diag)+(Cons) ⟹ `D = vmin` (the squeeze).
- `vmin_is_deny_by_default` — `vmin` itself satisfies all three axioms (existence).

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave8`) — NOT in the LOCKED v11 baseline. Locked-proven
  stays exactly 5 {F1,F11,F12,F18,F19}. Λ untouched (Conjecture 1).
- This is a POSITIVE, provable uniqueness theorem — it does NOT rely on, and is
  not, the false Λ = geometric-mean uniqueness (`unconditional_lambda_is_false`).
- Lean-core only: no Mathlib import, no open obligation, no new declared axiom.
- Scope: discrete `Nat` confidence units; the continuous-[0,1] statement (with
  `Continuous`) is the same squeeze and is left as a Mathlib follow-up.

## Citations
- Grabisch, Marichal, Mesiar, Pap, "Aggregation Functions", Cambridge 2009
  (min as the unique conjunctive idempotent conservative aggregator).
- Threshold-rule axiomatics for graded preferences:
  http://www.accessecon.com/pubs/SCW2008/GeneralPDFSCW2008/SCW2008-08-00108S.pdf

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/

namespace Lutar.Wave8.MinGate

/-- Minimum of a nonempty score vector `Fin (n+1) → Nat`. -/
def vmin : (n : Nat) → (Fin (n+1) → Nat) → Nat
  | 0,     v => v 0
  | n + 1, v => Nat.min (v 0) (vmin n (fun i => v i.succ))

/-- The vector minimum lower-bounds every component. -/
theorem vmin_le {n : Nat} (v : Fin (n+1) → Nat) : ∀ i, vmin n v ≤ v i := by
  induction n with
  | zero =>
      intro i
      refine Fin.cases ?_ (fun j => Fin.elim0 j) i
      simp [vmin]
  | succ n ih =>
      intro i
      refine Fin.cases ?_ ?_ i
      · exact Nat.min_le_left _ _
      · intro j
        exact Nat.le_trans (Nat.min_le_right _ _) (ih (fun k => v k.succ) j)

/-- Predicate: `D` is non-decreasing in each argument (componentwise monotone). -/
def Monotone' {n : Nat} (D : (Fin (n+1) → Nat) → Nat) : Prop :=
  ∀ u w : Fin (n+1) → Nat, (∀ i, u i ≤ w i) → D u ≤ D w

/-- Predicate: `D` is idempotent on constant vectors (the diagonal condition). -/
def Diagonal {n : Nat} (D : (Fin (n+1) → Nat) → Nat) : Prop :=
  ∀ x : Nat, D (fun _ => x) = x

/-- Predicate: `D` is conservative — never exceeds the weakest input. -/
def Conservative {n : Nat} (D : (Fin (n+1) → Nat) → Nat) : Prop :=
  ∀ v : Fin (n+1) → Nat, D v ≤ vmin n v

/-- (Mono)+(Diag) force the minimum as a LOWER bound on any aggregator:
since each `v i ≥ vmin v`, monotonicity from the constant vector `vmin v` gives
`vmin v = D (const (vmin v)) ≤ D v`. -/
theorem min_gate_lower_bound {n : Nat} (D : (Fin (n+1) → Nat) → Nat)
    (hMono : Monotone' D) (hDiag : Diagonal D) :
    ∀ v : Fin (n+1) → Nat, vmin n v ≤ D v := by
  intro v
  have hconst : D (fun _ => vmin n v) = vmin n v := hDiag (vmin n v)
  have hstep : D (fun _ => vmin n v) ≤ D v :=
    hMono (fun _ => vmin n v) v (fun i => vmin_le v i)
  -- rewrite the constant evaluation
  have : vmin n v ≤ D v := by rw [← hconst]; exact hstep
  exact this

/-- L2 — Deny-by-default uniqueness. Any aggregator that is monotone, idempotent
on the diagonal, and conservative MUST equal the pointwise minimum. Honest
uniqueness, in contrast to the false Λ uniqueness (Conjecture 1). -/
theorem deny_by_default_unique {n : Nat} (D : (Fin (n+1) → Nat) → Nat)
    (hMono : Monotone' D) (hDiag : Diagonal D) (hCons : Conservative D) :
    ∀ v : Fin (n+1) → Nat, D v = vmin n v := by
  intro v
  exact Nat.le_antisymm (hCons v) (min_gate_lower_bound D hMono hDiag v)

/-- Existence: the minimum gate itself satisfies all three axioms, so the
characterization is non-vacuous. -/
theorem vmin_is_deny_by_default {n : Nat} :
    Monotone' (vmin n) ∧ Diagonal (vmin n) ∧ Conservative (vmin n) := by
  refine ⟨?_, ?_, ?_⟩
  · -- monotone
    intro u w h
    -- prove vmin n u ≤ w i for all i, then vmin n u ≤ vmin n w by a min lower-bound
    have key : ∀ m (a b : Fin (m+1) → Nat), (∀ i, a i ≤ b i) → vmin m a ≤ vmin m b := by
      intro m
      induction m with
      | zero => intro a b hab; simpa [vmin] using hab 0
      | succ m ih =>
          intro a b hab
          have h0 : a 0 ≤ b 0 := hab 0
          have htail : vmin m (fun i => a i.succ) ≤ vmin m (fun i => b i.succ) :=
            ih _ _ (fun i => hab i.succ)
          simp only [vmin]
          -- Nat.min a b ≤ Nat.min a' b' when a ≤ a' and b ≤ b'
          apply Nat.le_min.mpr
          exact ⟨Nat.le_trans (Nat.min_le_left _ _) h0,
                 Nat.le_trans (Nat.min_le_right _ _) htail⟩
    exact key n u w h
  · intro x
    induction n with
    | zero => simp [vmin]
    | succ n ih => simp [vmin, ih]
  · intro v; exact Nat.le_refl _

#print axioms vmin_le
#print axioms min_gate_lower_bound
#print axioms deny_by_default_unique
#print axioms vmin_is_deny_by_default

end Lutar.Wave8.MinGate
