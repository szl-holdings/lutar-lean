import Mathlib

namespace Lutar.Putnam.Sampler

/-!
# Sampler Problem 10 (Combinatorics / pigeonhole on residues)

**Problem (PDF):** Among any `n+1` integers there exist two whose difference is divisible by `n`.

**Faithful note:** `n+1` integers are modeled as `f : Fin (n+1) → ℤ`. Two with index `i ≠ j`
and `n ∣ f i - f j` exist by pigeonhole: the `n+1` residues `f i mod n` live in the `n`-element
set `ZMod n`, so two coincide.

**Difficulty:** 2.
**Status:** KERNEL-VERIFIED (sorry-free).
-/

theorem p10 (n : ℕ) (hn : 0 < n) (f : Fin (n + 1) → ℤ) :
    ∃ i j : Fin (n + 1), i ≠ j ∧ (n : ℤ) ∣ (f i - f j) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hcard : Fintype.card (ZMod n) < Fintype.card (Fin (n + 1)) := by
    rw [ZMod.card n, Fintype.card_fin]; omega
  obtain ⟨i, j, hij, hgij⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (n + 1) => (f i : ZMod n)) hcard
  refine ⟨i, j, hij, ?_⟩
  have hg : (f i : ZMod n) = (f j : ZMod n) := hgij
  have hzero : ((f i - f j : ℤ) : ZMod n) = 0 := by
    push_cast
    rw [sub_eq_zero]
    exact hg
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (f i - f j) n).mp hzero

end Lutar.Putnam.Sampler
