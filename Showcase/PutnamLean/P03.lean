/-
# Putnam 2019 A1 — REAL (kernel-checked)

Problem. Determine all nonnegative integers `n` that can be written as
`A³ + B³ + C³ − 3ABC` for some nonnegative integers `A, B, C`.
Answer: exactly the `n` with `n % 9 ∉ {3, 6}`.

Honesty label: **REAL.** This is a complete, kernel-checked proof with zero
`sorry`. `#print axioms putnam2019A1_iff` reports only the three standard
Lean-core axioms `[propext, Classical.choice, Quot.sound]` (introduced by
`omega`/`simp`); there is no `sorryAx`. The file is Mathlib-free and compiles
against `leanprover/lean4:v4.18.0` core — in particular it uses **no** `ring`,
`ring_nf`, or `le_refl`; every algebraic identity is discharged by a small,
self-contained `omega`-based toolkit (`mul3`, `polyA`, `polyC`).

Proof idea.
* **Necessity (⇒).** Write `s = A + B + C` and `P = AB + BC + CA`. The polynomial
  identity `A³+B³+C³−3ABC = s³ − 3·s·P` holds over `ℤ` (lemma `hexp`, the only
  step needing commutativity — closed by `polyC`). The residue claim is then a
  *generic* fact about `s³ − 3·s·P`, with `P` treated as a single opaque integer
  (`cubeForm_emod9`). Splitting on `s % 3`:
  - if `3 ∣ s` then `9 ∣ (s³−3sP)`, so the value is `≡ 0 (mod 9)`;
  - if `s ≡ 1 (mod 3)` then `s³−3sP ≡ 1 (mod 3)`;
  - if `s ≡ 2 (mod 3)`, written `s = 3k−1`, then `s³−3sP ≡ −1 ≡ 2 (mod 3)`.
  In every case the residue mod 9 avoids `3` and `6`. This replaces the brute
  9³-case residue table with three `polyA`+`omega` lines.
* **Sufficiency (⇐).** Explicit witnesses by residue class of `n % 3`:
  - `n = 3m+1`:  `cyclicForm (m+1) m m   = 3m+1`;
  - `n = 3m+2`:  `cyclicForm (m+1) (m+1) m = 3m+2`;
  - `n = 9k`  :  `cyclicForm (k+1) k (k-1) = 9k` (and `(0,0,0)` for `n = 0`);
    when `n % 3 = 0`, the excluded residues `3, 6` force `n % 9 = 0`.

See `Showcase/Putnam/P03.md` for the human-readable writeup.
-/
namespace Showcase.Putnam

/-- The cyclic form `A³ + B³ + C³ − 3ABC`, over `ℤ` to keep subtraction total. -/
def cyclicForm (A B C : Int) : Int := A ^ 3 + B ^ 3 + C ^ 3 - 3 * A * B * C

/-- `3 * y = y + y + y`; lets `omega` see a factor of `3` after expansion. -/
theorem mul3 (y : Int) : 3 * y = y + y + y := by omega

/-- Polynomial-identity tactic, **no commutativity**: expand powers and
distribute products (associativity only), then close the resulting linear goal
over the product-atoms with `omega`. Used wherever the two sides already share a
factor order, so big numeral coefficients (`9, 18, 27`) stay as `omega`
coefficients instead of being absorbed into product atoms by `mul_comm`. -/
macro "polyA" : tactic =>
  `(tactic| (simp only [Int.pow_succ, Int.pow_zero, Int.one_mul, mul3];
             simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                        Int.mul_one, Int.mul_assoc];
             omega))

/-- Polynomial-identity tactic **with commutativity**, used only for the
symmetric factorization `hexp` where monomials must be reordered to match. -/
macro "polyC" : tactic =>
  `(tactic| (simp only [Int.pow_succ, Int.pow_zero, Int.one_mul, Int.mul_one, mul3];
             simp only [Int.mul_add, Int.add_mul, Int.mul_one, Int.mul_assoc,
                        Int.mul_comm, Int.mul_left_comm];
             omega))

/-- Generic necessity core: for any integers `s, P`, the value `s³ − 3·s·P`
is never `≡ 3` or `6 (mod 9)`. `P` is opaque here, so `polyA` suffices. -/
theorem cubeForm_emod9 (s P : Int) :
    (s ^ 3 - 3 * s * P) % 9 ≠ 3 ∧ (s ^ 3 - 3 * s * P) % 9 ≠ 6 := by
  have hcase : s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2 := by omega
  rcases hcase with h | h | h
  · -- `3 ∣ s` ⟹ `9 ∣ (s³−3sP)`.
    obtain ⟨t, ht⟩ : ∃ t, s = 3 * t := ⟨s / 3, by omega⟩
    have hc : s ^ 3 - 3 * s * P = 9 * (3 * t ^ 3 - t * P) := by rw [ht]; polyA
    omega
  · -- `s ≡ 1 (mod 3)`.
    obtain ⟨k, hk⟩ : ∃ k, s = 3 * k + 1 := ⟨s / 3, by omega⟩
    have hc : s ^ 3 - 3 * s * P
        = 3 * (9 * k ^ 3 + 9 * k ^ 2 + 3 * k - (3 * k + 1) * P) + 1 := by rw [hk]; polyA
    omega
  · -- `s ≡ 2 (mod 3)`, written `s = 3k − 1` to keep a clean `−1` constant.
    obtain ⟨k, hk⟩ : ∃ k, s = 3 * k - 1 := ⟨(s + 1) / 3, by omega⟩
    have hc : s ^ 3 - 3 * s * P
        = 3 * (9 * k ^ 3 - 9 * k ^ 2 + 3 * k - (3 * k - 1) * P) - 1 := by rw [hk]; polyA
    omega

/-- Necessity, residue form: the cyclic form is never `≡ 3` or `6 (mod 9)`. -/
theorem cyclicForm_emod9 (A B C : Int) :
    cyclicForm A B C % 9 ≠ 3 ∧ cyclicForm A B C % 9 ≠ 6 := by
  -- `cyclicForm = s³ − 3·s·P` with `s = A+B+C`, `P = AB+BC+CA` (needs comm).
  have hexp : cyclicForm A B C
      = (A + B + C) ^ 3 - 3 * (A + B + C) * (A * B + B * C + C * A) := by
    unfold cyclicForm; polyC
  rw [hexp]
  exact cubeForm_emod9 (A + B + C) (A * B + B * C + C * A)

/-- Putnam 2019 A1: `n` is representable iff `n % 9 ∉ {3, 6}`. -/
theorem putnam2019A1_iff (n : Int) (hn : 0 ≤ n) :
    (∃ A B C : Int, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ C ∧ cyclicForm A B C = n)
      ↔ (n % 9 ≠ 3 ∧ n % 9 ≠ 6) := by
  constructor
  · -- Necessity.
    rintro ⟨A, B, C, _, _, _, rfl⟩
    exact cyclicForm_emod9 A B C
  · -- Sufficiency: build a witness by residue class of `n % 3`.
    rintro ⟨h3, h6⟩
    have hcase : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hcase with h | h | h
    · -- `n % 3 = 0`, and `n % 9 ∉ {3,6}` forces `n % 9 = 0`, i.e. `n = 9k`.
      obtain ⟨k, hk⟩ : ∃ k, n = 9 * k := ⟨n / 9, by omega⟩
      rcases (by omega : k = 0 ∨ 1 ≤ k) with hk0 | hk1
      · -- `n = 0`: witness `(0,0,0)`.
        refine ⟨0, 0, 0, by omega, by omega, by omega, ?_⟩
        have heq : cyclicForm 0 0 0 = 0 := by unfold cyclicForm; polyA
        rw [heq]; omega
      · -- `n = 9k`, `k ≥ 1`: witness `(k+1, k, k-1)`.
        refine ⟨k + 1, k, k - 1, by omega, by omega, by omega, ?_⟩
        have heq : cyclicForm (k + 1) k (k - 1) = 9 * k := by unfold cyclicForm; polyA
        rw [heq]; omega
    · -- `n = 3m+1`: witness `(m+1, m, m)`.
      obtain ⟨m, hm⟩ : ∃ m, n = 3 * m + 1 := ⟨n / 3, by omega⟩
      refine ⟨m + 1, m, m, by omega, by omega, by omega, ?_⟩
      have heq : cyclicForm (m + 1) m m = 3 * m + 1 := by unfold cyclicForm; polyA
      rw [heq]; omega
    · -- `n = 3m+2`: witness `(m+1, m+1, m)`.
      obtain ⟨m, hm⟩ : ∃ m, n = 3 * m + 2 := ⟨n / 3, by omega⟩
      refine ⟨m + 1, m + 1, m, by omega, by omega, by omega, ?_⟩
      have heq : cyclicForm (m + 1) (m + 1) m = 3 * m + 2 := by unfold cyclicForm; polyA
      rw [heq]; omega

-- Honesty proof: emitted into the build log.
#print axioms putnam2019A1_iff

end Showcase.Putnam
