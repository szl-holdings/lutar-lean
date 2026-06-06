import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Preimage
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Basic

open BigOperators

namespace Lutar

/-- **lambda_perm_invariant** (Λ A5 — permutation invariance).

    A Λ-style product aggregate over a finite type is invariant under
    any permutation of the index set.  Derived from `Fintype.prod_equiv`.

    *Doctrine note:* Λ itself remains **Conjecture 1**.  This theorem is a
    peripheral combinatorial property of the machinery, not a proof of Λ. -/
theorem lambda_perm_invariant
    {α : Type*} [Fintype α] {β : Type*} [CommMonoid β]
    (f : α → β) (σ : α ≃ α) :
    ∏ x, f x = ∏ x, f (σ x) :=
  (Fintype.prod_equiv σ (f ∘ σ) f (fun _ => rfl)).symm

end Lutar
