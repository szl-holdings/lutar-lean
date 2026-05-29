import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic

/-!
# CompositionOverhead.lean
## Overhead Bound Theorem for Composed Doctrine-Locked Systems

**Doctrine v6** — Canonical scanner reference.  
**Guarantee**: `axiom`-free; no `sorry`.

This module proves that the overhead incurred by composing N doctrine-locked
systems is bounded by O(N · maxOverhead), where `maxOverhead` is the maximum
per-system overhead constant. The model uses a cost semiring to track
computation overhead through composition pipelines.

### Key theorem: `composition_overhead_bound`
For a composition of N systems each with overhead ≤ C, the total overhead
of the composed pipeline is ≤ N * C.
-/

namespace Lutar.Composition.Overhead

/-! ## 1. Overhead Model -/

/-- The overhead of a single system step, measured in abstract cost units. -/
def OverheadCost := ℕ

/-- A system with an associated overhead cost. -/
structure CostSystem where
  /-- Abstract overhead cost of executing this system step. -/
  cost     : OverheadCost
  /-- Every system must declare a positive overhead (even a no-op has cost 1). -/
  pos      : 0 < cost

/-- Total overhead of sequentially composed systems. -/
def totalOverhead (systems : List CostSystem) : OverheadCost :=
  systems.foldl (fun acc s => acc + s.cost) 0

/-! ## 2. Bound Lemmas -/

/-- The total overhead of a single system equals its cost. -/
@[simp]
theorem totalOverhead_singleton (s : CostSystem) :
    totalOverhead [s] = s.cost := by
  simp [totalOverhead]

/-- Overhead is additive over list concatenation. -/
theorem totalOverhead_append (l₁ l₂ : List CostSystem) :
    totalOverhead (l₁ ++ l₂) = totalOverhead l₁ + totalOverhead l₂ := by
  simp [totalOverhead, List.foldl_append]
  induction l₁ with
  | nil => simp
  | cons h t ih =>
    simp [List.foldl, ih]
    omega

/-- Each term in the sum is bounded by the per-element maximum. -/
theorem totalOverhead_le_len_mul_max
    (systems : List CostSystem) (C : ℕ)
    (hbound : ∀ s ∈ systems, s.cost ≤ C) :
    totalOverhead systems ≤ systems.length * C := by
  induction systems with
  | nil => simp [totalOverhead]
  | cons h t ih =>
    simp [totalOverhead, List.foldl]
    have hh : h.cost ≤ C := hbound h (List.mem_cons_self h t)
    have ht : ∀ s ∈ t, s.cost ≤ C := fun s hs => hbound s (List.mem_cons_of_mem h hs)
    have ih' := ih ht
    -- totalOverhead (h :: t) = h.cost + totalOverhead t
    have expand : totalOverhead (h :: t) = h.cost + totalOverhead t := by
      simp [totalOverhead, List.foldl]
      induction t with
      | nil => simp
      | cons a rest iht =>
        simp [List.foldl]
        omega
    rw [expand]
    calc h.cost + totalOverhead t
        ≤ C + t.length * C := by linarith
      _ = (t.length + 1) * C := by ring
      _ = (h :: t).length * C := by simp

/-! ## 3. Main Overhead Bound Theorem -/

/-- **Composition Overhead Bound (Doctrine v6)**

    For any list of N doctrine-locked systems each with overhead cost ≤ C,
    the composed pipeline's total overhead is bounded by N * C.

    This is the formal statement of the O(N) composition overhead claim
    in the Lutar Doctrine v6 specification. -/
theorem composition_overhead_bound
    (systems : List CostSystem)
    (C : ℕ)
    (hC : 0 < C)
    (hbound : ∀ s ∈ systems, s.cost ≤ C) :
    totalOverhead systems ≤ systems.length * C :=
  totalOverhead_le_len_mul_max systems C hbound

/-! ## 4. Strict Bound for Non-Empty Pipelines -/

/-- For a non-empty pipeline, the bound is strict when at least one system
    has cost strictly less than C. -/
theorem composition_overhead_strict_bound
    (systems : List CostSystem)
    (hne : systems ≠ [])
    (C : ℕ)
    (hC : 0 < C)
    (hbound : ∀ s ∈ systems, s.cost ≤ C)
    (hstrict : ∃ s ∈ systems, s.cost < C) :
    totalOverhead systems < systems.length * C := by
  obtain ⟨s₀, hs₀mem, hs₀lt⟩ := hstrict
  have hle := totalOverhead_le_len_mul_max systems C hbound
  -- Split the list at s₀ to get the strict inequality
  obtain ⟨prefix, suffix, rfl⟩ := List.mem_iff_append.mp hs₀mem
  rw [totalOverhead_append]
  simp [totalOverhead]
  have hprefix : totalOverhead prefix ≤ prefix.length * C :=
    totalOverhead_le_len_mul_max prefix C (fun s hs => hbound s (List.mem_append_left _ hs))
  have hsuffix : totalOverhead suffix ≤ suffix.length * C :=
    totalOverhead_le_len_mul_max suffix C (fun s hs => hbound s (by simp; right; exact hs))
  calc totalOverhead prefix + (s₀.cost + totalOverhead suffix)
      < prefix.length * C + (C + suffix.length * C) := by linarith
    _ = (prefix.length + 1 + suffix.length) * C := by ring
    _ = (prefix ++ s₀ :: suffix).length * C := by simp [List.length_append]; ring

/-! ## 5. Overhead-Aware Composition -/

/-- A *bounded pipeline* is a list of cost systems with a certified overhead cap. -/
structure BoundedPipeline where
  systems : List CostSystem
  cap     : ℕ
  hcap    : 0 < cap
  hbound  : ∀ s ∈ systems, s.cost ≤ cap
  /-- Certified total overhead ≤ length * cap -/
  cert    : totalOverhead systems ≤ systems.length * cap :=
    totalOverhead_le_len_mul_max systems cap hbound

/-- Concatenating two bounded pipelines with the same cap gives a bounded pipeline. -/
def BoundedPipeline.append (P₁ P₂ : BoundedPipeline)
    (hcap : P₁.cap = P₂.cap) : BoundedPipeline where
  systems := P₁.systems ++ P₂.systems
  cap     := P₁.cap
  hcap    := P₁.hcap
  hbound  := fun s hs => by
    simp [List.mem_append] at hs
    cases hs with
    | inl h => exact P₁.hbound s h
    | inr h => rw [hcap]; exact P₂.hbound s h
  cert    := by
    rw [totalOverhead_append, List.length_append, Nat.add_mul]
    have h1 := P₁.cert
    have h2 := P₂.cert
    rw [hcap] at h2
    linarith

end Lutar.Composition.Overhead
