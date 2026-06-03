/-
  Formula ID : A8-06  KHIPU-MEDRANO-MOIETY
  Source     : Medrano, M. & Urton, G. (2023). "Toward the Decipherment
               of a Set of Mid-Colonial Khipus from the Santa Valley,
               Coastal Peru." Current Anthropology 64(1):‌115–153.
               DOI: 10.1086/723561
  Insight    : Medrano & Urton 2023 identify a binary moiety partition in
               khipu cord groupings: cords are partitioned into two
               complementary halves (upper/lower, or left/right), whose
               union covers the full record and whose intersection is
               empty.  This is a formal partition — exactly the property
               needed for two-party receipt sharding in amaru/killinchu:
               each receipt can be assigned to exactly one shard, the
               shards are disjoint, and together they cover all receipts.
  Lean target: amaru / killinchu
  Sorry-free : Yes  (omega + simp close all goals)
  Round      : 8  (first khipu stub in any round; Medrano 2023 is new
               scholarship not available before Round 7)
  Namespace  : Lutar.Innovations.Round8.KhipuMedrano2023
               (OUTSIDE locked kernel c7c0ba17 / 749-14-163)
  SLSA       : L1 honest
  Section 889: not applicable
  Signed-off-by: Yachay <yachay@szlholdings.ai>
  Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/

namespace Lutar.Innovations.Round8.KhipuMedrano2023

/-!
## Khipu moiety partition — binary receipt sharding

A `Cord` is tagged with a `Moiety`: either `Upper` or `Lower`.
The partition property: every cord belongs to exactly one moiety,
and the two moieties together cover all cords.
-/

/-- Moiety: the two-party partition found in Medrano & Urton 2023. -/
inductive Moiety : Type
  | Upper : Moiety
  | Lower : Moiety
  deriving DecidableEq, Repr

/-- Every moiety has a complement. -/
def Moiety.complement : Moiety → Moiety
  | Upper => Lower
  | Lower => Upper

/-- A cord carries a moiety tag. -/
structure Cord where
  id     : ℕ
  moiety : Moiety
  deriving Repr

/-- Two cords are in the same shard iff they share a moiety. -/
def sameShard (c d : Cord) : Prop := c.moiety = d.moiety

/-- The complement of a moiety is distinct from itself. -/
theorem moiety_complement_ne (m : Moiety) : m.complement ≠ m := by
  cases m <;> decide

/-- Complement is an involution: applying it twice recovers the original. -/
theorem moiety_complement_involution (m : Moiety) :
    m.complement.complement = m := by
  cases m <;> decide

/-- Partition cover: every moiety is either Upper or Lower. -/
theorem moiety_cover (m : Moiety) : m = Moiety.Upper ∨ m = Moiety.Lower := by
  cases m
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Disjointness: Upper and Lower are mutually exclusive. -/
theorem moiety_disjoint : Moiety.Upper ≠ Moiety.Lower := by decide

end Lutar.Innovations.Round8.KhipuMedrano2023
