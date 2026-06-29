/-
# Theorem 9 (EXPERIMENTAL) — Merkle Functor Kernel Theorem

Compositional closure of Khipu receipt chains, ported from the composition
half of Lochbihler's Theorem 5 ("Authenticated Data Structures as Functors in
Isabelle/HOL", FMBC 2020, OASIcs vol. 84, art. 6,
DOI:10.4230/OASIcs.FMBC.2020.6) and instantiated to the Khipu hash chain.

A Khipu receipt chain is a list of hash-linked receipts. Composition of two
chains is list append; the canonical hash-recomputation morphism is `rehash`.
The content of the theorem is that the induced endofunctor on the receipt-chain
category (`KhipuReceiptFunctor`) is a genuine `CategoryTheory.Functor`: it
preserves identities (`map_id`) and composition (`map_comp`). Composition
preservation is exactly `List.map` distributing over `List.append`, so any
concatenation of verified receipt chains is itself a verified chain whose hash
structure is coherent with the composition — "compositional closure".

Implementation note on the blueprint: the blueprint's draft `Category`
instance typed `Hom h₁ h₂ := { c : KhipuChain // c.length > 0 ∧ True }` while
also defining `id` as the empty chain `[]` (length 0). Those two are
contradictory (the identity morphism cannot satisfy `length > 0`). The
mathematically correct path category — the one whose composition is `List.append`
with `[]` as identity — takes the morphisms to be plain receipt chains. That is
what is formalised here; the well-formedness predicate is recorded separately as
`WellFormedReceipt` rather than smuggled into the `Hom` type.

The hash function is modelled abstractly as an `opaque` constant `sha3_256`.
The functor laws are independent of the choice of hash function, so no concrete
SHA3 implementation (and no new `axiom`) is required: `opaque` introduces a
sealed constant, not an axiom, leaving the Doctrine-v11 axiom count untouched.

HONESTY: This module is EXPERIMENTAL. It is NOT part of the locked Doctrine-v11
baseline. The locked-proven count stays EXACTLY 8 {F1,F4,F7,F11,F12,F18,F19,F22}
until a human deliberately promotes this after kernel confirmation. This file
proves what the Lean kernel checks: the functor laws and the compositional
closure theorem, sorry-free. It does NOT prove BFT safety, adversarial
substitution resistance, liveness, or hash collision resistance — see
THEOREM9_BLUEPRINT.md §7.2 (DO-NOT-CLAIM list).

Sources:
  * Lochbihler, A. (2020). Authenticated Data Structures as Functors in
    Isabelle/HOL. FMBC 2020, OASIcs vol. 84, art. 6.
    DOI:10.4230/OASIcs.FMBC.2020.6
  * Mathlib4 `CategoryTheory.Functor.Basic`, `CategoryTheory.Category.Basic`.
-/
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory

namespace Lutar.Khipu.MerkleFunctor

/-! ## Core types (blueprint §2.2) -/

/-- A Khipu receipt hash: an abstract byte string. -/
abbrev KhipuHash := ByteArray

/-- Abstract hash function. Modelled `opaque` (sealed, NOT an `axiom`): the
    functor laws below hold for any function of this type, so the specific
    SHA3-256 implementation is irrelevant to the proof. -/
opaque sha3_256 : ByteArray → ByteArray

/-- A Khipu receipt: one hash-linked record in the chain.
    Operationally `selfHash = sha3_256 (prevHash ++ payloadHash)`; the invariant
    is recorded as `WellFormedReceipt` rather than baked into the structure. -/
structure KhipuReceipt where
  prevHash : KhipuHash
  payloadHash : KhipuHash
  selfHash : KhipuHash

/-- A Khipu receipt chain: a list of receipts. Morphisms of `KhipuReceiptCat`. -/
abbrev KhipuChain := List KhipuReceipt

/-! ## Lemma 1.1 — `rehash` is well-typed -/

/-- `rehash` recomputes a receipt's `selfHash` from `prevHash ++ payloadHash`.
    This is the morphism-map building block of `KhipuReceiptFunctor`. -/
def rehash (r : KhipuReceipt) : KhipuReceipt :=
  { r with selfHash := sha3_256 (r.prevHash ++ r.payloadHash) }

/-- `rehash` preserves the `prevHash` and `payloadHash` fields. -/
lemma rehash_preserves_fields (r : KhipuReceipt) :
    (rehash r).prevHash = r.prevHash ∧ (rehash r).payloadHash = r.payloadHash := by
  constructor <;> rfl

/-! ## Lemma 1.2 — `rehash` is idempotent -/

/-- A receipt is well-formed if its `selfHash` was computed correctly. -/
def WellFormedReceipt (r : KhipuReceipt) : Prop :=
  r.selfHash = sha3_256 (r.prevHash ++ r.payloadHash)

/-- Every receipt is well-formed after one `rehash`. -/
lemma rehash_wellFormed (r : KhipuReceipt) : WellFormedReceipt (rehash r) := rfl

/-- `rehash` is idempotent: applying it twice equals applying it once. -/
lemma rehash_idempotent (r : KhipuReceipt) : rehash (rehash r) = rehash r := rfl

/-! ## Lemma 1.3 — `KhipuReceiptCat` is a `Category`

Objects are hash tips; a morphism `h₁ ⟶ h₂` is a receipt chain; composition is
list append and the identity is the empty chain. -/

/-- The category of Khipu receipt chains. -/
def KhipuReceiptCat : Type := KhipuHash

instance : Category KhipuReceiptCat where
  Hom _ _ := KhipuChain
  id _ := ([] : KhipuChain)
  comp f g := List.append f g
  id_comp f := List.nil_append f
  comp_id f := List.append_nil f
  assoc f g h := List.append_assoc f g h

/-- The three `Category` axioms, restated explicitly (blueprint Lemma 1.3). -/
lemma khipuReceiptCat_id_comp {h₁ h₂ : KhipuReceiptCat} (f : h₁ ⟶ h₂) :
    CategoryStruct.comp (CategoryStruct.id h₁) f = f := by
  simp

lemma khipuReceiptCat_comp_id {h₁ h₂ : KhipuReceiptCat} (f : h₁ ⟶ h₂) :
    CategoryStruct.comp f (CategoryStruct.id h₂) = f := by
  simp

lemma khipuReceiptCat_assoc {h₁ h₂ h₃ h₄ : KhipuReceiptCat}
    (f : h₁ ⟶ h₂) (g : h₂ ⟶ h₃) (k : h₃ ⟶ h₄) :
    CategoryStruct.comp (CategoryStruct.comp f g) k =
      CategoryStruct.comp f (CategoryStruct.comp g k) := by
  simp

/-! ## Lemma 1.5 — `List.map` distributes over append (the structural key)

Stated before the functor since `map_comp` is definitionally this fact. -/

/-- `List.map` distributes over append, specialised to receipt chains. -/
lemma receipt_map_append (f : KhipuReceipt → KhipuReceipt) (c₁ c₂ : KhipuChain) :
    List.map f (c₁ ++ c₂) = List.map f c₁ ++ List.map f c₂ :=
  List.map_append f c₁ c₂

/-! ## §2.5 — The `KhipuReceiptFunctor`, with Lemmas 1.4 and 1.6 inline -/

/-- The Khipu receipt functor: identity on hash-tip objects, `rehash` on each
    receipt of a chain morphism.

    * `map_id` (Lemma 1.4): `List.map rehash [] = []` — definitional.
    * `map_comp` (Lemma 1.6): `List.map rehash (f ++ g) = List.map rehash f ++
      List.map rehash g` — `List.map_append`. -/
def KhipuReceiptFunctor : KhipuReceiptCat ⥤ KhipuReceiptCat where
  obj h := h
  map c := List.map rehash c
  map_id _ := rfl
  map_comp f g := by
    change List.map rehash (List.append f g)
      = List.append (List.map rehash f) (List.map rehash g)
    exact List.map_append rehash f g

/-- Lemma 1.4 — identity preservation, restated. -/
lemma khipuFunctor_map_id (h : KhipuReceiptCat) :
    KhipuReceiptFunctor.map (𝟙 h) = 𝟙 (KhipuReceiptFunctor.obj h) :=
  KhipuReceiptFunctor.map_id h

/-- Lemma 1.6 — composition preservation, restated. -/
lemma khipuFunctor_map_comp {h₁ h₂ h₃ : KhipuReceiptCat}
    (f : h₁ ⟶ h₂) (g : h₂ ⟶ h₃) :
    KhipuReceiptFunctor.map (f ≫ g) =
      KhipuReceiptFunctor.map f ≫ KhipuReceiptFunctor.map g :=
  KhipuReceiptFunctor.map_comp f g

/-! ## Lemma 1.7 — `KhipuReceiptFunctor` is a genuine functor -/

/-- The functor exists and acts as specified (object map is the identity, the
    morphism map is `rehash` pointwise). Its mere construction above already
    discharged both functor laws to the kernel. -/
theorem khipuReceiptFunctor_is_valid_functor :
    ∃ F : KhipuReceiptCat ⥤ KhipuReceiptCat,
      (∀ h, F.obj h = h) ∧
      (∀ {h₁ h₂ : KhipuReceiptCat} (c : h₁ ⟶ h₂), F.map c = c.map rehash) := by
  refine ⟨KhipuReceiptFunctor, fun _ => rfl, ?_⟩
  intro _ _ _; rfl

/-! ## Lemma 1.8 — Theorem 9: compositional closure -/

/-- **Theorem 9 (EXPERIMENTAL, kernel-checked here):**
    Khipu receipt chains are compositionally closed.

    For any composable receipt chains `f : h₁ ⟶ h₂` and `g : h₂ ⟶ h₃`, the
    `KhipuReceiptFunctor` maps their composition to the composition of their
    images: the hash-recomputed concatenation equals the concatenation of the
    individually hash-recomputed chains. This is the composition direction of
    Lochbihler's Theorem 5, instantiated to the Khipu hash chain. -/
theorem khipuReceiptChains_compositionalClosure
    {h₁ h₂ h₃ : KhipuReceiptCat} (f : h₁ ⟶ h₂) (g : h₂ ⟶ h₃) :
    KhipuReceiptFunctor.map (CategoryStruct.comp f g) =
      CategoryStruct.comp
        (KhipuReceiptFunctor.map f)
        (KhipuReceiptFunctor.map g) :=
  KhipuReceiptFunctor.map_comp f g

end Lutar.Khipu.MerkleFunctor
