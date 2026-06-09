/-
# Putnam 2020 A2 — REAL (kernel-checked)

Problem. Let `k` be a nonnegative integer. Evaluate
`∑_{j=0}^{k} 2^{k−j} · C(k+j, j)`.
Answer: `4^k`.

Honesty label: **REAL.** This is a complete, kernel-checked proof with zero
`sorry`. `#print axioms putSum_eq_four_pow` reports only the two standard
Lean-core axioms `[propext, Quot.sound]` (introduced by `omega`/`simp`); there
is no `sorryAx` and no `Classical.choice`. The file is Mathlib-free and compiles
against `leanprover/lean4:v4.18.0` core — in particular it uses **no** `ring`,
`ring_nf`, or `le_refl`; every algebraic identity is discharged by `omega`,
`simp only` (associativity/commutativity of `*`), and the Pascal recurrence.

Because `Nat.choose` is not in the core prelude, we define our own `binom` via
Pascal's rule and develop the few combinatorial facts we need from scratch.

Proof idea.
* Introduce an auxiliary `S n k = ∑_{j=0}^{k} 2^{k−j} · binom (n+j) j`, defined by
  the recurrence `S n 0 = 1`, `S n (k+1) = 2·S n k + binom (n+k+1) (k+1)` (`R1`,
  definitional). Then `putSum k = S k k`.
* **Pascal toolkit.** `binom_pascal` (definitional), over-diagonal vanishing
  `binom_lt`, the diagonal `binom_self = 1`, the subtraction-free complementary
  symmetry `binom (a+b) a = binom (a+b) b` (`binom_symm`, a nested induction),
  and the corollary `binom (2k+2) (k+1) = 2·binom (2k+1) k` (`binom_D`).
* **Additive recurrence** `R3 : S (n+1) k + binom (n+k+1) k = 2·S n k`
  (induction on `k`; the step is Pascal plus linear arithmetic over the
  `binom`/`S` atoms, closed by `omega`).
* **Diagonal** `S k k = 4^k` (induction on `k`): `R1`, `R3 k k`, and `binom_D`
  combine so that the two `binom` terms cancel, leaving `S (k+1) (k+1) = 4·S k k`.
* **Bridge** `putSum k = S k k`: the partial `foldl` up to index `m` equals
  `2^(k−m) · S k m` (induction on `m`, `m ≤ k`); at `m = k` the prefactor is `1`.

See `Showcase/Putnam/P04.md` for the human-readable writeup.
-/
namespace Showcase.Putnam

/-- Binomial coefficient via Pascal's rule (core-only; avoids `Nat.choose`). -/
def binom : Nat → Nat → Nat
  | _,     0     => 1
  | 0,     _+1   => 0
  | n+1, k+1 => binom n k + binom n (k + 1)

/-- `binom n 0 = 1` (the equation compiler splits on the first argument, so this
is not `rfl` for a variable `n`). -/
theorem binom_zero (n : Nat) : binom n 0 = 1 := by cases n <;> rfl

/-- Pascal's rule, definitional. -/
theorem binom_pascal (n k : Nat) :
    binom (n + 1) (k + 1) = binom n k + binom n (k + 1) := rfl

/-- Over-diagonal vanishing: `binom n k = 0` whenever `n < k`. -/
theorem binom_lt (n : Nat) : ∀ k, n < k → binom n k = 0 := by
  induction n with
  | zero => intro k hk; cases k with | zero => omega | succ k => rfl
  | succ m ih =>
    intro k hk; cases k with
    | zero => omega
    | succ j => rw [binom_pascal, ih j (by omega), ih (j + 1) (by omega)]

/-- Diagonal value: `binom n n = 1`. -/
theorem binom_self (n : Nat) : binom n n = 1 := by
  induction n with
  | zero => rfl
  | succ m ih => rw [binom_pascal, ih, binom_lt m (m + 1) (by omega)]

/-- Complementary symmetry, stated subtraction-free: `binom (a+b) a = binom (a+b) b`.
Nested induction (`a` generalizing `b`, then `b`); both branches realign indices
with `omega` and apply Pascal to each side. -/
theorem binom_symm : ∀ a b, binom (a + b) a = binom (a + b) b := by
  intro a
  induction a with
  | zero => intro b; simp only [Nat.zero_add]; rw [binom_zero, binom_self]
  | succ a ih =>
    intro b
    induction b with
    | zero => simp only [Nat.add_zero]; rw [binom_zero, binom_self]
    | succ b ih_b =>
      have e1 : a + 1 + (b + 1) = (a + b + 1) + 1 := by omega
      have hL : binom ((a + b + 1) + 1) (a + 1)
          = binom (a + b + 1) a + binom (a + b + 1) (a + 1) := binom_pascal (a + b + 1) a
      have hR : binom ((a + b + 1) + 1) (b + 1)
          = binom (a + b + 1) b + binom (a + b + 1) (b + 1) := binom_pascal (a + b + 1) b
      have hA : binom (a + b + 1) a = binom (a + b + 1) (b + 1) := by
        have h := ih (b + 1); have e2 : a + (b + 1) = a + b + 1 := by omega
        rwa [e2] at h
      have hB : binom (a + b + 1) (a + 1) = binom (a + b + 1) b := by
        have e3 : a + 1 + b = a + b + 1 := by omega
        rwa [e3] at ih_b
      rw [e1, hL, hR, hA, hB]; omega

/-- Central corollary: `binom (2k+2) (k+1) = 2 · binom (2k+1) k`
(Pascal at `2k+1` plus the symmetry `binom (2k+1) (k+1) = binom (2k+1) k`). -/
theorem binom_D (k : Nat) : binom (2 * k + 2) (k + 1) = 2 * binom (2 * k + 1) k := by
  have e1 : 2 * k + 2 = (2 * k + 1) + 1 := by omega
  rw [e1, binom_pascal]
  have hsym : binom (2 * k + 1) (k + 1) = binom (2 * k + 1) k := by
    have h := binom_symm (k + 1) k; have e2 : (k + 1) + k = 2 * k + 1 := by omega
    rw [e2] at h; exact h
  rw [hsym]; omega

/-- Auxiliary closed-form accumulator `S n k = ∑_{j=0}^{k} 2^{k−j} · binom (n+j) j`,
given by its `R1` recurrence (matched on the second argument for termination). -/
def S : Nat → Nat → Nat
  | _, 0     => 1
  | n, k + 1 => 2 * S n k + binom (n + k + 1) (k + 1)

/-- `R1` base, definitional. -/
theorem S_zero (n : Nat) : S n 0 = 1 := rfl

/-- `R1` step, definitional. -/
theorem S_succ (n k : Nat) : S n (k + 1) = 2 * S n k + binom (n + k + 1) (k + 1) := rfl

/-- Additive recurrence `R3 : S (n+1) k + binom (n+k+1) k = 2 · S n k`.
Induction on `k`; the step rewrites both `S`-recurrences and one Pascal step,
then closes a linear goal over the `binom`/`S` atoms with `omega`. -/
theorem R3 (n : Nat) : ∀ k, S (n + 1) k + binom (n + k + 1) k = 2 * S n k := by
  intro k
  induction k with
  | zero =>
    show S (n + 1) 0 + binom (n + 0 + 1) 0 = 2 * S n 0
    rw [S_zero, S_zero, binom_zero]
  | succ k ih =>
    have ei : (n + 1) + k + 1 = n + k + 2 := by omega
    have hS1 : S (n + 1) (k + 1) = 2 * S (n + 1) k + binom (n + k + 2) (k + 1) := by
      rw [S_succ, ei]
    have hS2 : S n (k + 1) = 2 * S n k + binom (n + k + 1) (k + 1) := rfl
    have hpa : binom (n + k + 2) (k + 1)
        = binom (n + k + 1) k + binom (n + k + 1) (k + 1) := binom_pascal (n + k + 1) k
    have hgi : binom (n + (k + 1) + 1) (k + 1) = binom (n + k + 2) (k + 1) := rfl
    rw [hgi, hS1, hS2, hpa]; omega

/-- Diagonal evaluation `S k k = 4^k` (induction on `k`): `R1`, `R3 k k`, and
`binom_D` make the two `binom` terms cancel, giving `S (k+1) (k+1) = 4 · S k k`. -/
theorem diag (k : Nat) : S k k = 4 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hSd : S (k + 1) (k + 1) = 2 * S (k + 1) k + binom (2 * k + 2) (k + 1) := by
      have e : (k + 1) + k + 1 = 2 * k + 2 := by omega
      rw [S_succ, e]
    have hR3k : S (k + 1) k + binom (2 * k + 1) k = 2 * S k k := by
      have h := R3 k k; have e : k + k + 1 = 2 * k + 1 := by omega
      rw [e] at h; exact h
    have hD : binom (2 * k + 2) (k + 1) = 2 * binom (2 * k + 1) k := binom_D k
    have hpow : (4 : Nat) ^ (k + 1) = 4 * 4 ^ k := by rw [Nat.pow_succ]; omega
    rw [hpow]; omega

/-- The Putnam 2020 A2 sum `∑_{j=0}^{k} 2^{k−j} · C(k+j, j)`. -/
def putSum (k : Nat) : Nat :=
  (List.range (k + 1)).foldl (fun acc j => acc + 2 ^ (k - j) * binom (k + j) j) 0

-- Statement sanity check (evidence, NOT proof): all equal `4 ^ k`.
#eval (List.range 8).map (fun k => (putSum k, 4 ^ k, putSum k == 4 ^ k))

/-- Bridge: the partial `foldl` of `putSum`'s summand over `j ∈ [0, m]` equals
`2^(k−m) · S k m` for every `m ≤ k`. Induction on `m`; the step uses
`List.range_succ`/`List.foldl_append` to peel the last term, `S_succ`, and the
identity `2^(k−m) = 2 · 2^(k−(m+1))` (valid since `m < k`). -/
theorem bridge (k : Nat) : ∀ m, m ≤ k →
    (List.range (m + 1)).foldl (fun acc j => acc + 2 ^ (k - j) * binom (k + j) j) 0
      = 2 ^ (k - m) * S k m := by
  intro m
  induction m with
  | zero =>
    intro _
    simp only [List.range_succ, List.range_zero, List.nil_append, List.foldl_cons,
               List.foldl_nil, Nat.sub_zero, Nat.add_zero, Nat.zero_add, binom_zero,
               S_zero, Nat.mul_one]
  | succ m ih =>
    intro hm
    have hmk : m ≤ k := by omega
    have hmlt : m < k := by omega
    have hP := ih hmk
    rw [List.range_succ, List.foldl_append, hP]
    show 2 ^ (k - m) * S k m + 2 ^ (k - (m + 1)) * binom (k + (m + 1)) (m + 1)
        = 2 ^ (k - (m + 1)) * S k (m + 1)
    have hb : binom (k + (m + 1)) (m + 1) = binom (k + m + 1) (m + 1) := rfl
    have hpow2 : (2 : Nat) ^ (k - m) = 2 * 2 ^ (k - (m + 1)) := by
      have e : k - m = (k - (m + 1)) + 1 := by omega
      rw [e, Nat.pow_succ]; omega
    rw [hb, S_succ, hpow2]
    simp only [Nat.mul_add, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]

/-- Putnam 2020 A2 (REAL): `putSum k = 4 ^ k`. Combine the `bridge` (at `m = k`)
with the `diag`onal evaluation. -/
theorem putSum_eq_four_pow (k : Nat) : putSum k = 4 ^ k := by
  have hb := bridge k k (Nat.le_refl k)
  have hd := diag k
  unfold putSum
  rw [hb]
  simp only [Nat.sub_self, Nat.pow_zero, Nat.one_mul, hd]

-- Honesty proof: emitted into the build log.
#print axioms putSum_eq_four_pow

end Showcase.Putnam
