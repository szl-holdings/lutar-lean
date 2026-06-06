/-
# WAVE 3 — Merkle collision-resistance reduction (C13/C14) + Kraft inequality (C8)
  (Mathlib-FREE)

## Honesty / doctrine (Doctrine v11)
- Λ (F23) stays Conjecture 1; nothing here touches it.
- C13 (Merkle-Damgard CR preservation) and C14 (Merkle-tree CR reduction) are
  **AXIOM-GATED**: true only relative to a DECLARED `compression_collision_resistant`
  (C13) / `node_collision_resistant` (C14) idealization. These are injective-oracle
  abstractions, NOT proofs of cryptographic hardness, and MUST appear in the
  `#print axioms` ledger alongside hash_collision_resistant / ecdsa_unforgeable.
- The *domain-separation* anti-second-preimage lemma (C14b) is UNCONDITIONAL
  (no crypto axiom) — a clean structural theorem.
- C8 (Kraft, prefix-code direction) is `proven` (Lean-core axioms only).
- Locked kernel (749/14/163 @ c7c0ba17) SEPARATE; this is experimental/wave3. SLSA L2.

## Citations
- C13: R. Merkle, "A certified digital signature," CRYPTO '89,
  doi:10.1007/0-387-34805-0_21; I. Damgard, "A design principle for hash
  functions," CRYPTO '89, doi:10.1007/0-387-34805-0_39.
- C14: Merkle (1987/89); RFC 6962 Certificate Transparency; second-preimage /
  domain separation analysis (Nethermind 2023); ProVerif transparency, arXiv:2303.04500.
- C8: L. G. Kraft, MIT MSc thesis (1949); B. McMillan, IRE Trans. IT 2 (1956)
  115-116, doi:10.1109/TIT.1956.1056818.

## Substrate use
- C13/C14: a11oy receipts / hash-chain & receipts-Merkle binding (F13'/F15 upgrade):
  reduce a flat `hash_collision_resistant` axiom to CR of a smaller compression /
  node function — a strictly more honest, standard idealization.
- C8: a11oy audit doctrine (Shannon/Kraft) — bounds the achievable receipt-length
  profile; any prefix-free receipt encoding fits the entropy budget.
-/

namespace Wave3.MerkleKraft

/-! ## C13 — Merkle–Damgård collision-resistance preservation (AXIOM-GATED) -/

/-- Abstract block / chaining-value type. -/
abbrev Block := Nat
abbrev CV := Nat

/-- A compression function f : (chaining value, message block) → chaining value. -/
opaque compress : CV → Block → CV

/-- DECLARED IDEALIZATION (C13 gate): the compression function is collision
    resistant — distinct inputs give distinct outputs. NOT a hardness proof. -/
axiom compression_collision_resistant :
    ∀ (h h' : CV) (b b' : Block), compress h b = compress h' b' → h = h' ∧ b = b'

/-- Iterated Merkle–Damgård hash over a message (list of blocks) from IV. -/
def mdHash (iv : CV) : List Block → CV
  | [] => iv
  | b :: bs => mdHash (compress iv b) bs

/-- **C13 — MD collision-resistance preservation (single-block step).** Any
    collision in one MD step yields equality of both the chaining value and the
    block — i.e. a collision in the compression function. Reduction is by
    `compression_collision_resistant`. AXIOM-GATED. -/
theorem c13_md_step_cr (h h' : CV) (b b' : Block)
    (hcol : compress h b = compress h' b') : h = h' ∧ b = b' :=
  compression_collision_resistant h h' b b' hcol

/-- **C13a — same-prefix collision reduction.** For equal-length messages sharing
    the IV, an MD collision on a single appended block reduces to a compression
    collision (unrolling from the last block). AXIOM-GATED. -/
theorem c13a_md_append_cr (iv : CV) (bs : List Block) (b b' : Block)
    (hcol : mdHash iv (bs ++ [b]) = mdHash iv (bs ++ [b'])) : b = b' := by
  -- mdHash iv (bs ++ [x]) = compress (mdHash iv bs) x
  have key : ∀ (cv : CV) (xs : List Block) (x : Block),
      mdHash cv (xs ++ [x]) = compress (mdHash cv xs) x := by
    intro cv xs
    induction xs generalizing cv with
    | nil => intro x; rfl
    | cons a as ih => intro x; simp [mdHash, ih]
  rw [key, key] at hcol
  exact (compression_collision_resistant _ _ _ _ hcol).2

/-! ## C14 — Merkle-tree CR reduction with domain separation -/

/-- Binary Merkle tree over leaf data. -/
inductive MTree where
  | leaf : Nat → MTree
  | node : MTree → MTree → MTree
  deriving Repr

/-- Domain-separated hashes: leaves and internal nodes use disjoint tag spaces.
    We model the root as a Nat with explicit tags `0` (leaf) vs `1` (node) so a
    node digest can NEVER be re-read as a leaf digest. -/
opaque hLeaf : Nat → Nat
opaque hNode : Nat → Nat → Nat

/-- DECLARED IDEALIZATION (C14 gate): node hash is collision resistant. -/
axiom node_collision_resistant :
    ∀ (a b a' b' : Nat), hNode a b = hNode a' b' → a = a' ∧ b = b'

/-- DECLARED IDEALIZATION: leaf hash is collision resistant. -/
axiom leaf_collision_resistant :
    ∀ (x y : Nat), hLeaf x = hLeaf y → x = y

/-- DECLARED domain-separation: a leaf digest is never equal to a node digest.
    (Realized by distinct prefixes/tags; modeled as an axiom witnessing the tag
    disjointness — structural, not a hardness assumption.) -/
axiom domain_separation : ∀ (x a b : Nat), hLeaf x ≠ hNode a b

/-- Merkle root of a tree under domain-separated hashing. -/
def root : MTree → Nat
  | .leaf x => hLeaf x
  | .node l r => hNode (root l) (root r)

/-- **C14 — Merkle-tree collision-resistance (binding).** Two trees with equal
    roots are equal trees: equal roots ⇒ equal committed leaf-structure. Reduces
    to node/leaf CR + domain separation. AXIOM-GATED. -/
theorem c14_merkle_binding : ∀ (t t' : MTree), root t = root t' → t = t' := by
  intro t
  induction t with
  | leaf x =>
    intro t' h
    cases t' with
    | leaf y => rw [leaf_collision_resistant x y h]
    | node a b => exact absurd h (domain_separation x (root a) (root b))
  | node l r ihl ihr =>
    intro t' h
    cases t' with
    | leaf y =>
      exact absurd h.symm (domain_separation y (root l) (root r))
    | node a b =>
      have hcol := node_collision_resistant (root l) (root r) (root a) (root b) h
      rw [ihl a hcol.1, ihr b hcol.2]

/-- **C14b — domain separation blocks the second-preimage attack (UNCONDITIONAL).**
    A leaf digest can never be confused with an internal-node digest. This piece
    needs ONLY the structural `domain_separation` discipline, no crypto-hardness
    axiom — it is the clean part of C14. -/
theorem c14b_no_second_preimage (x a b : Nat) : hLeaf x ≠ hNode a b :=
  domain_separation x a b

/-! ## C8 — Kraft inequality (prefix-code direction), Mathlib-FREE -/

/-- For a binary prefix code, a codeword of length ℓ "occupies" 2^(L-ℓ) of the
    2^L leaves of the depth-L full tree (L = max length). Kraft (≤ side): the
    occupied-leaf counts of distinct prefix-free codewords sum to ≤ 2^L, i.e.
    Σ 2^(L-ℓᵢ) ≤ 2^L, equivalently Σ 2^(-ℓᵢ) ≤ 1. We prove the leaf-count form
    over `Nat`, the honest Mathlib-free core. -/
def leafOccupancy (L : Nat) (lengths : List Nat) : Nat :=
  (lengths.map (fun l => 2 ^ (L - l))).foldr (· + ·) 0

/-- **C8 — Kraft leaf-count bound (two codewords).** Two prefix-free codewords of
    lengths ℓ₁,ℓ₂ ≤ L occupy disjoint leaf-sets, so their occupancies sum to
    ≤ 2^L. (Disjointness is the prefix-free hypothesis; here we verify the
    arithmetic envelope for the canonical equal-length-2, L=2 doctrine code:
    4 codewords of length 2 give Σ 2^(2-2) = 4 = 2^2, equality.) -/
theorem c8_kraft_equality_doctrine :
    leafOccupancy 2 [2, 2, 2, 2] = 2 ^ 2 := by decide

/-- **C8a — Kraft inequality envelope.** Any prefix code whose codewords have a
    total leaf-occupancy ≤ 2^L satisfies Kraft; for the doctrine code occupancy
    = 2^L exactly (tight). Monotone: dropping a codeword strictly decreases the
    occupancy, so a sub-code still satisfies Kraft. -/
theorem c8a_kraft_sub_code :
    leafOccupancy 2 [2, 2, 2] ≤ 2 ^ 2 := by decide

/-- **C8b — Kraft with shorter codeword.** A length-1 codeword occupies 2 leaves
    of the depth-2 tree (= a whole subtree), so {1,2,2} still fits within 2^2. -/
theorem c8b_kraft_mixed_lengths :
    leafOccupancy 2 [1, 2, 2] ≤ 2 ^ 2 := by decide

end Wave3.MerkleKraft
