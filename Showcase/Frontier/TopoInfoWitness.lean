/-
  Showcase.Frontier.TopoInfoWitness
  =================================
  EXPERIMENTAL.  Mathlib-free; every theorem closes by `decide` / `rfl` /
  `Nat`/`Int` arithmetic over closed terms, so a bare Lean kernel checks it
  (sorry-free). Compiles against `leanprover/lean4:v4.18.0` core. NO Mathlib
  import, NO declared axiom, NO `sorry`, NO `native_decide`.

  AUTHOR NOTE (honesty doctrine v11):
    We claim NO general topology or coding theorem. We formalize, as closed
    integer / Bool identities the kernel checks, the DISCRETE ARITHMETIC
    SKELETONS of two structural facts. Honest discrete witnesses of shape, not
    the general theorems. Locked-proven set stays EXACTLY 8; says NOTHING about
    Λ (Conjecture 1).

  MOTIVATION (real, citeable):
    (1) Euler's polyhedron formula V − E + F = 2 for convex polyhedra; Euler
        (1758), "Elementa doctrinae solidorum." We witness it on the five
        Platonic solids as a closed integer identity.
    (2) Kraft–McMillan inequality: a binary prefix-free (instantaneous) code on
        codeword lengths ℓ₁,…,ℓₙ exists iff Σ 2^{−ℓᵢ} ≤ 1.  Kraft (1949);
        McMillan (1956). We witness the integer (cleared-denominator) form on a
        canonical prefix code and exhibit a violating multiset.
-/
namespace Showcase.Frontier.TopoInfoWitness

/-! ## Part 1 — Euler characteristic V − E + F = 2 (Platonic-solid witness)

    For every convex polyhedron, `V − E + F = 2`. We check it as a closed
    integer identity on the five Platonic solids — the discrete witness of the
    Euler characteristic of the 2-sphere. -/

/-- `(vertices, edges, faces)` for the five Platonic solids. -/
def platonic : List (Nat × Nat × Nat) :=
  [ (4, 6, 4),      -- tetrahedron
    (8, 12, 6),     -- cube (hexahedron)
    (6, 12, 8),     -- octahedron
    (20, 30, 12),   -- dodecahedron
    (12, 30, 20) ]  -- icosahedron

/-- Euler characteristic `V − E + F` as an integer. -/
def eulerChar (s : Nat × Nat × Nat) : Int :=
  (s.1 : Int) - (s.2.1 : Int) + (s.2.2 : Int)

/-- **Euler's formula (discrete witness).** Every Platonic solid satisfies
    `V − E + F = 2` — the Euler characteristic of a sphere.  Exhaustive over the
    five solids; a bare kernel checks it. -/
theorem euler_platonic :
    (platonic.all (fun s => eulerChar s == 2)) = true := by decide

/-- A non-spherical witness for contrast: a torus-like cell complex with
    `V − E + F = 0` (Euler characteristic of the torus).  This is NOT a polyhedron
    bound — it documents that `=2` is special to the sphere. -/
theorem torus_euler_zero : (1 : Int) - 2 + 1 = 0 := by decide

/-! ## Part 2 — Kraft inequality (integer-cleared witness)

    A binary prefix-free code on lengths `ℓ₁,…,ℓₙ` exists iff `Σ 2^{−ℓᵢ} ≤ 1`.
    Clearing denominators by `2^L` with `L = max ℓᵢ`, the test becomes the
    INTEGER inequality `Σ 2^{L−ℓᵢ} ≤ 2^L`.  We witness both a satisfying code and
    a violating multiset. -/

/-- Integer-cleared Kraft sum `Σ 2^{L−ℓᵢ}` for lengths `ls` at scale `L`. -/
def kraftClearedSum (L : Nat) (ls : List Nat) : Nat :=
  (ls.map (fun li => 2 ^ (L - li))).foldl (· + ·) 0

/-- **Kraft inequality — satisfying witness.** The prefix code with lengths
    `[1, 2, 3, 3]` (e.g. `0, 10, 110, 111`) satisfies Kraft: with `L = 3`,
    `Σ 2^{3−ℓᵢ} = 4 + 2 + 1 + 1 = 8 ≤ 8 = 2³`.  A prefix-free code exists. -/
theorem kraft_satisfied :
    kraftClearedSum 3 [1, 2, 3, 3] ≤ 2 ^ 3 := by decide

/-- The satisfying code is *tight* (a complete code: equality holds). -/
theorem kraft_tight :
    kraftClearedSum 3 [1, 2, 3, 3] = 2 ^ 3 := by decide

/-- **Kraft inequality — violating witness.** The lengths `[1, 1, 2]` violate
    Kraft: with `L = 2`, `Σ 2^{2−ℓᵢ} = 2 + 2 + 1 = 5 > 4 = 2²`.  No binary
    prefix-free code with these lengths can exist — the integer shadow of
    `Σ 2^{−ℓᵢ} = 1/2 + 1/2 + 1/4 = 5/4 > 1`. -/
theorem kraft_violated :
    2 ^ 2 < kraftClearedSum 2 [1, 1, 2] := by decide

end Showcase.Frontier.TopoInfoWitness
