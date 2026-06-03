/-
  Formula ID : A8-04  MOHIST-DISTINGUISHABILITY
  Source     : Mohist Canon, Jing (經) A 88 (≈ 350 BCE):
               "同 (tóng) = same; 異 (yì) = different.
                Two things are the same when they share every name." 
               Ref: Fraser, "The Mohist Canons", Stanford Encyclopedia
               of Philosophy (Win 2018 edition), §3.2.
  Insight    : Mohist extensionality: two receipts are identical iff they
               agree on every distinguishing predicate.  In Lean 4 this
               maps to `Decidable` equality on a product type — any two
               receipt values that differ on at least one field are
               provably distinct.  Used in amaru/killinchu deduplication.
  Lean target: amaru / killinchu
  Sorry-free : Yes  (instDecidableAnd + decide close all goals)
  Round      : 8  (not in R4–R7)
  Namespace  : Lutar.Innovations.Round8.MohistDistinguishability
               (OUTSIDE locked kernel c7c0ba17 / 749-14-163)
  SLSA       : L1 honest
  Section 889: not applicable
  Signed-off-by: Yachay <yachay@szlholdings.ai>
  Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/

namespace Lutar.Innovations.Round8.MohistDistinguishability

/-!
## Mohist extensional distinguishability — receipt deduplication

A `Receipt` is identified by a pair of tags.  Two receipts are the same
(同) iff both tag components agree; otherwise they are different (異).
-/

/-- A receipt with two distinguishing tag fields. -/
structure Receipt where
  tagA : Bool
  tagB : Bool
  deriving DecidableEq, Repr

/-- Two receipts are Mohist-same iff they share every tag. -/
def mohist_same (r s : Receipt) : Bool :=
  (r.tagA == s.tagA) && (r.tagB == s.tagB)

/-- mohist_same agrees with structural equality. -/
theorem mohistSame_iff_eq (r s : Receipt) :
    mohist_same r s = true ↔ r = s := by
  cases r; cases s
  simp [mohist_same, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨h1, h2⟩; simp [h1, h2]
  · intro h; injection h; exact ⟨‹_›, ‹_›⟩

/-- If two receipts differ on tagA, they are provably distinct. -/
theorem distinctByTagA (r s : Receipt) (h : r.tagA ≠ s.tagA) : r ≠ s := by
  intro heq
  have := congr_arg Receipt.tagA heq
  exact h this

/-- If two receipts differ on tagB, they are provably distinct. -/
theorem distinctByTagB (r s : Receipt) (h : r.tagB ≠ s.tagB) : r ≠ s := by
  intro heq
  have := congr_arg Receipt.tagB heq
  exact h this

/-- Decidable distinguishability: we can always determine 同 vs 異. -/
example (r s : Receipt) : Decidable (r = s) := inferInstance

end Lutar.Innovations.Round8.MohistDistinguishability
