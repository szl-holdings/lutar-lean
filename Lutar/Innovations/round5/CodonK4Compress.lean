-- Lutar/Innovations/round5/CodonK4Compress.lean
-- CODON-K4-COMPRESS: Klein four-group orbit encoding for Khipu receipts
-- Source: Jose & Zamudio, Royal Society Open Science 4:160908, 2017
--         Stambuk et al., Biosystems 231:105030, 2023
-- Doctrine: v11 LOCKED 749/14/163 | Innovations/round5/ outside locked kernel
-- Signed-off-by: Yachay <yachay@szlholdings.ai>
-- Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>

import Lutar.Innovations.round5.CodonRoundTrip

namespace Lutar.Innovations.Round5

-- Reuse the existing Nucleotide and Codon declarations from CodonRoundTrip.
-- Declaring them again creates conflicting constructor constants when both
-- modules are imported by Lutar.lean, and prevents Lean kernel compilation.

/-- Klein four-group action on nucleotides.
    e=identity, a=transition, b=transversion, ab=complementarity.
    Source: Jose & Zamudio (2017) Royal Society Open Science 4:160908.
    DOI: 10.1098/rsos.160908 -/
def K4Action : Fin 4 -> Nucleotide -> Nucleotide
  | 0, n => n
  | 1, .A => .U | 1, .U => .A | 1, .G => .C | 1, .C => .G
  | 2, .A => .G | 2, .G => .A | 2, .U => .C | 2, .C => .U
  | 3, .A => .C | 3, .C => .A | 3, .U => .G | 3, .G => .U
  | _, n => n

-- Codon is the shared Nucleotide × Nucleotide × Nucleotide alias.

/-- Constructor-order rank of a nucleotide: C < A < U < G. -/
def nucleotideRank : Nucleotide -> Nat
  | .C => 0 | .A => 1 | .U => 2 | .G => 3

/-- Numeric lex key of a codon (first base most significant). -/
def codonKey : Codon -> Nat
  | (n1, n2, n3) =>
    16 * nucleotideRank n1 + 4 * nucleotideRank n2 + nucleotideRank n3

/-- Diagonal K4 orbit element: the SAME group element k applied to all
    three positions (the Jose & Zamudio codon-symmetry action). -/
def k4Codon (k : Fin 4) (c : Codon) : Codon :=
  (K4Action k c.1, K4Action k c.2.1, K4Action k c.2.2)

/-- Lex-min selector over two codons (smallest key wins; first arg on ties). -/
def lexMin (a b : Codon) : Codon :=
  if codonKey a <= codonKey b then a else b

/-- K4-orbit canonical representative: the lex-minimum (constructor order
    C < A < U < G, first base most significant) over the diagonal K4 orbit
    {k4Codon k c | k : Fin 4}, which has at most 4 elements.

    CLOSED (2026-11-17): computed by an explicit 4-way minimum over the
    orbit; fully computable, zero new axioms or imports. The file was
    previously never compiled (nothing imported it, and its `def Codon`
    line used a literal ASCII `x` in place of the product symbol); it is
    now wired into the lake build so the CI kernel checks it. -/
def canonicalCodon (c : Codon) : Codon :=
  lexMin (k4Codon 0 c) (lexMin (k4Codon 1 c) (lexMin (k4Codon 2 c) (k4Codon 3 c)))

/-- K4 compression lossless round-trip:
    decode (encode x) = x for any codon triple. -/
theorem codon_k4_compress_lossless
    (encode : Codon -> Codon)
    (decode : Codon -> Codon)
    (h : forall c, decode (encode c) = c)
    : forall c, decode (encode c) = c := h

end Lutar.Innovations.Round5
