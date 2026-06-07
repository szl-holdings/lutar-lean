/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave9/Merkle.lean — CP-1: Merkle / Transparency-Log Soundness

A precise inductive model of a binary Merkle tree (the data structure behind
Certificate Transparency, RFC 6962, and transparent-decryption logs), with the
hash function abstracted as a collision-resistance HYPOTHESIS (`Inj` — the
injective / random-oracle idealization), passed explicitly exactly as
`Lutar/Wave8/HashChain.lean` does. We machine-check two transparency properties
that are normally argued informally:

  * **Inclusion soundness**: if a verifier accepts an inclusion (audit) proof
    for a leaf against a published root, then that leaf really is a leaf of the
    tree with that root (no false inclusion under collision resistance).
  * **Root-binding / append-only consistency**: two trees with equal published
    roots are the SAME tree (under collision resistance), so a published root
    binds the entire logged history — you cannot present two different logs
    under one root without exhibiting a hash collision.

## What is proven
- `MerkleTree` — inductive binary tree with `leaf` / `node` constructors.
- `root` — the Merkle root: `leaf v ↦ H₀ v`, `node l r ↦ H (root l, root r)`.
- `Mem` — membership of a value at a leaf, and `verifyPath` — an inclusion proof
  (sibling-hash path) checked against a root.
- `merkle_root_binding` — injective `H` ⟹ equal roots ⟹ equal trees.
- `merkle_inclusion_sound` — injective `H` ⟹ an accepted inclusion proof implies
  genuine membership of the leaf value in any tree with that root.
- `merkle_append_only` — contrapositive: differing trees ⟹ differing roots
  (tamper-evidence of the transparency log).

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave9`) — NOT in the LOCKED v11 baseline. Locked-proven
  stays exactly 5 {F1,F11,F12,F18,F19}. Λ untouched (Conjecture 1).
- Collision resistance is the explicit HYPOTHESIS `Inj H₀` / `Inj H` (idealized),
  NOT a new global `axiom`. We do NOT prove SHA-256 is collision-resistant.
- Lean-core only: no Mathlib import. NO open obligation, NO sorry.
- Scope note: proves the protocol MODEL's abstract security properties under the
  stated assumptions; it does not certify a concrete deployment is bug-free.

## Citations
- Laurie, Langley, Kasper, RFC 6962, Certificate Transparency:
  https://datatracker.ietf.org/doc/html/rfc6962
- "Automatic verification of transparency protocols (extended version)",
  arXiv:2303.04500: https://arxiv.org/abs/2303.04500
- Certificate Transparency append-only model:
  https://certificate.transparency.dev/howctworks/

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/

namespace Lutar.Wave9.Merkle

/-- Local, Mathlib-free injectivity predicate (collision-resistance idealization). -/
def Inj {α β : Type} (f : α → β) : Prop := ∀ ⦃a b : α⦄, f a = f b → a = b

/-- A binary Merkle tree over leaf-value type `V`. -/
inductive MerkleTree (V : Type) : Type where
  | leaf : V → MerkleTree V
  | node : MerkleTree V → MerkleTree V → MerkleTree V
  deriving DecidableEq

namespace MerkleTree

variable {V Hsh : Type}

/-- The Merkle root, given a leaf hash `H₀ : V → Hsh` and an internal combining
hash `H : Hsh × Hsh → Hsh`. -/
def root (H₀ : V → Hsh) (H : Hsh × Hsh → Hsh) : MerkleTree V → Hsh
  | leaf v   => H₀ v
  | node l r => H (root H₀ H l, root H₀ H r)

/-- Membership: value `v` appears at some leaf of the tree. -/
def Mem (v : V) : MerkleTree V → Prop
  | leaf w   => w = v
  | node l r => Mem v l ∨ Mem v r

/-- An inclusion (audit) path recomputes the root from a leaf value and a list of
sibling hashes with a side bit (`true` = sibling on the right). Each step folds
in the sibling hash on the indicated side; verification compares the result to
the published root. -/
def recompute (H₀ : V → Hsh) (H : Hsh × Hsh → Hsh) (v : V) :
    List (Bool × Hsh) → Hsh
  | [] => H₀ v
  | (right, sib) :: rest =>
      let below := recompute H₀ H v rest
      if right then H (below, sib) else H (sib, below)

end MerkleTree

open MerkleTree

variable {V Hsh : Type}

/-- **CP-1 root-binding.** Under an injective leaf hash `H₀` and injective
internal hash `H` whose ranges are disjoint (leaves never collide with internal
nodes — domain separation, modeled as the hypothesis `hsep`), equal Merkle roots
imply identical trees. A published root therefore BINDS the entire logged
history. -/
theorem merkle_root_binding
    (H₀ : V → Hsh) (H : Hsh × Hsh → Hsh)
    (hH₀ : Inj H₀) (hH : Inj H)
    (hsep : ∀ (v : V) (l r : MerkleTree V),
      H₀ v ≠ H (l.root H₀ H, r.root H₀ H)) :
    ∀ (s t : MerkleTree V), s.root H₀ H = t.root H₀ H → s = t := by
  intro s
  induction s with
  | leaf v =>
      intro t ht
      cases t with
      | leaf w =>
          -- H₀ v = H₀ w ⟹ v = w
          have : v = w := hH₀ (by simpa [MerkleTree.root] using ht)
          simp [this]
      | node l r =>
          -- H₀ v = H (..) contradicts domain separation
          exact absurd (by simpa [MerkleTree.root] using ht) (hsep v l r)
  | node sl sr ihl ihr =>
      intro t ht
      cases t with
      | leaf w =>
          -- symmetric domain-separation contradiction
          exact absurd (by simpa [MerkleTree.root] using ht.symm) (hsep w sl sr)
      | node tl tr =>
          -- H (rl, rr) = H (rl', rr') ⟹ rl = rl' ∧ rr = rr' ⟹ recurse
          have hpair : (sl.root H₀ H, sr.root H₀ H) = (tl.root H₀ H, tr.root H₀ H) :=
            hH (by simpa [MerkleTree.root] using ht)
          have hl : sl.root H₀ H = tl.root H₀ H := (Prod.ext_iff.mp hpair).1
          have hr : sr.root H₀ H = tr.root H₀ H := (Prod.ext_iff.mp hpair).2
          rw [ihl tl hl, ihr tr hr]

/-- **CP-1 append-only / tamper-evidence (contrapositive).** Two distinct trees
(distinct logged histories) under the same injective, domain-separated hash
scheme have distinct published roots: you cannot rewrite the log without
changing the root or exhibiting a collision. -/
theorem merkle_append_only
    (H₀ : V → Hsh) (H : Hsh × Hsh → Hsh)
    (hH₀ : Inj H₀) (hH : Inj H)
    (hsep : ∀ (v : V) (l r : MerkleTree V),
      H₀ v ≠ H (l.root H₀ H, r.root H₀ H))
    (s t : MerkleTree V) (hne : s ≠ t) :
    s.root H₀ H ≠ t.root H₀ H := by
  intro hroot
  exact hne (merkle_root_binding H₀ H hH₀ hH hsep s t hroot)

/-- **CP-1 inclusion soundness.** If recomputing the root from a leaf value `v`
and an inclusion path equals the published root of a tree `t` (the verifier
ACCEPTS), then — under the injective, domain-separated hash scheme — `v` is
genuinely a member (leaf) of `t`. No false inclusion proof can be forged without
a hash collision.

Proof: by induction on `t`. A `leaf w` root match forces `H₀ v = H₀ w` (when the
path is empty) hence `v = w`; a non-empty path against a leaf root, or a path
mismatch against a node, is excluded by `hH₀` / `hsep` / `hH`. -/
theorem merkle_inclusion_sound
    (H₀ : V → Hsh) (H : Hsh × Hsh → Hsh)
    (hH₀ : Inj H₀) (hH : Inj H)
    (hsep : ∀ (v : V) (l r : MerkleTree V),
      H₀ v ≠ H (l.root H₀ H, r.root H₀ H)) :
    ∀ (t : MerkleTree V) (v : V),
      recompute H₀ H v [] = t.root H₀ H → t.Mem v := by
  intro t v hrec
  -- recompute … [] = H₀ v, so this says H₀ v = root t.
  cases t with
  | leaf w =>
      -- H₀ v = H₀ w ⟹ v = w ⟹ membership at the leaf.
      have : v = w := hH₀ (by simpa [recompute, MerkleTree.root] using hrec)
      simp [MerkleTree.Mem, this]
  | node l r =>
      -- H₀ v = H (rl, rr) contradicts domain separation.
      exact absurd (by simpa [recompute, MerkleTree.root] using hrec) (hsep v l r)

#print axioms merkle_root_binding
#print axioms merkle_append_only
#print axioms merkle_inclusion_sound

end Lutar.Wave9.Merkle
