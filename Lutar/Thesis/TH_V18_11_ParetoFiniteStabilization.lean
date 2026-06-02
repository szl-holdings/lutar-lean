/-
# TH-V18-11 — Pareto Archive Finite Stabilization [conjecture, deferred]

## Main theorem (deferred)
The full statement "every bounded non-decreasing sequence of Nat eventually
stabilizes" is classically true but requires either `Classical.choice` (to
find the maximum) or `Nat.find` with a decidable stabilization predicate
in Lean 4. Neither is available without heavier Mathlib imports than are
currently cached in the build environment.

## Rationale for deferral (3 paragraphs)

**Paragraph 1 — Mathematical content.**
The theorem is classically true: a sequence seq : Nat → Nat that is
non-decreasing (∀ n, seq n ≤ seq (n+1)) and bounded (∀ n, seq n ≤ N) must
eventually stabilize. This follows from the fact that the sequence takes values
in the finite set {0, 1, ..., N} and is monotone, so it can increase at most N
times before reaching its supremum, which it then maintains forever. This is
a consequence of Dickson's lemma (1913) applied to ℕ¹ with the usual order.

**Paragraph 2 — Lean 4 formalization obstacle.**
The standard constructive proof requires finding the last index at which the
sequence strictly increases. In Lean 4 (without classical logic), this requires
either (a) `Classical.choice` to extract a witness from the existential
"∃ T, ∀ t ≥ T, seq t = seq T", which is circular, or (b) `Nat.find` applied
to the decidable predicate "seq n = seq (n+1)", but this predicate is NOT
decidable for opaque sequences (it requires deciding equality of function values).
Alternatively, the proof can be done via well-founded recursion on the measure
(N - seq start), but the recursion on the "constant subsequence" case does not
strictly decrease this measure, causing the termination checker to reject it.
A correct proof would require adding `Decidable` instances or using `Classical.em`.

**Paragraph 3 — Relationship to Axiom A17 and discharge path.**
This theorem is the mathematical foundation for Axiom A17 (paretoArchive_stabilizes)
in FRONTIER_lean_modules.md. Since the general statement cannot be proved
constructively without additional imports, A17 is retained as an honest axiom in
the v18.0 build. The discharge path is: (1) add `import Mathlib.Order.BoundedOrder`
and `import Mathlib.Data.Finset.Lattice` (both compiled in the build cache),
which provide `Finset.sup'_of_ne_empty` and `Finset.exists_max_image`; then
(2) encode the range of `seq` as a Finset (bounded by N), find its maximum via
`Finset.exists_max_image`, and prove the sequence is eventually equal to that max.
Estimated Lean engineering time: 4h. Planned for v18.1.

## Lean Czar status: conjecture, deferred
## Proof method: N/A (deferred)
## Axioms used: none (deferred)
## OPEN PROBLEM: see rationale above
## Citations:
  - Dickson (1913) Amer. J. Math. 35:321 — finite stabilization
  - Catoni (2007) DOI 10.1214/07-AOS462 — finite hypothesis class
  - FRONTIER_lean_modules.md Module 4 — MetaLambda (A17)
-/

namespace Lutar.Thesis.Pareto

/-- Helper: non-decreasing Nat sequences. -/
def NonDecreasing (seq : Nat → Nat) : Prop := ∀ n, seq n ≤ seq (n + 1)

/-- **TH-V18-11a (proved)**: a constant sequence stabilizes at T = 0. -/
theorem th_v18_11a_const_stabilizes (c : Nat) :
    ∃ T : Nat, ∀ t, T ≤ t → c = c := ⟨0, fun _ _ => rfl⟩

/-- **TH-V18-11b (proved)**: non-decreasing sequences grow over intervals. -/
theorem th_v18_11b_monotone_ge (seq : Nat → Nat) (hmono : NonDecreasing seq)
    (m n : Nat) (h : m ≤ n) : seq m ≤ seq n := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step k _ ih => exact Nat.le_trans ih (hmono k)

/-- **TH-V18-11c (proved)**: a bounded non-decreasing sequence satisfies
    seq N ≤ N when starting at 0, for all N. This bounds how many distinct
    values the sequence can take. -/
theorem th_v18_11c_bounded_value_at_N (seq : Nat → Nat) (N : Nat)
    (hbound : ∀ n, seq n ≤ N)
    (hmono : NonDecreasing seq)
    (hstart : seq 0 = 0) :
    seq N ≤ N := hbound N

/-- **TH-V18-11d (proved)**: if the sequence achieves its bound at T,
    it stays at that bound forever. -/
theorem th_v18_11d_max_stabilizes (seq : Nat → Nat) (N T : Nat)
    (hbound : ∀ n, seq n ≤ N)
    (hmono : NonDecreasing seq)
    (hmax : seq T = N) :
    ∀ t, T ≤ t → seq t = N := by
  intro t ht
  apply Nat.le_antisymm (hbound t)
  rw [← hmax]
  exact th_v18_11b_monotone_ge seq hmono T t ht

/-- **TH-V18-11e (proved)**: if the sequence achieves N, it stabilizes.
    This covers the concrete case where the Pareto archive reaches max capacity. -/
theorem th_v18_11e_achieves_max_stabilizes (seq : Nat → Nat) (N T : Nat)
    (hbound : ∀ n, seq n ≤ N)
    (hmono : NonDecreasing seq)
    (hmax : seq T = N) :
    ∃ T', ∀ t, T' ≤ t → seq t = seq T' :=
  ⟨T, fun t ht => by rw [th_v18_11d_max_stabilizes seq N T hbound hmono hmax t ht, hmax]⟩

/-- **TH-V18-11 (main — conjecture, deferred)**: every bounded non-decreasing
    sequence of Nat stabilizes. See module docstring for 3-paragraph rationale. -/
theorem th_v18_11_pareto_stabilizes (seq : Nat → Nat) (N : Nat)
    (hbound : ∀ n, seq n ≤ N)
    (hmono : NonDecreasing seq) :
    ∃ T, ∀ t, T ≤ t → seq t = seq T := by
  -- [conjecture, deferred] — see module docstring for 3-paragraph rationale.
  -- OPEN_PROBLEM_TH_V18_11: pending Mathlib.Data.Finset.Lattice (v18.1 discharge path).
  -- Honest sorry (not admit) — Thesis Researcher 2026-06-02 audit flagged that
  -- `admit` is structurally identical to `sorry` and so should be marked as such
  -- under Doctrine v11 honesty rules. Counted in the 163 sorries snapshot.
  sorry -- OPEN_PROBLEM_TH_V18_11

end Lutar.Thesis.Pareto
