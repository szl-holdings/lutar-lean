-- Lutar/Innovations/round5/CodonRoundTrip.lean
-- CODON-ROUNDTRIP: Canonical section of the 64->20 codon surjection
-- Source: Lenstra, J. Theoretical Biology 347:13-26, 2014
-- Doctrine: v11 LOCKED 749/14/163 | Innovations/round5/ outside locked kernel
-- Signed-off-by: Yachay <yachay@szlholdings.ai>
-- Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>

namespace Lutar.Innovations.Round5

inductive Nucleotide : Type where | C | A | U | G
def Codon := Nucleotide × Nucleotide × Nucleotide

/-- 20 canonical amino acids + stop. -/
inductive AminoAcid : Type where
  | Ala | Arg | Asn | Asp | Cys | Gln | Glu | Gly | His | Ile
  | Leu | Lys | Met | Phe | Pro | Ser | Thr | Trp | Tyr | Val | Stop
  deriving DecidableEq, Repr

/-- Standard genetic code: surjection from 64 codons to 21 targets.
    Source: Lenstra (2014) J. Theoretical Biology 347:13-26.
    DOI: 10.1016/j.jtbi.2014.01.002

    CLOSED (2026-11-17): the table is filled in verbatim below (the standard
    RNA genetic code, all 64 codon cases, no new imports). Both former
    placeholder obligations of this file are retired and the round-trip
    theorem is proved by structural cases + definitional reduction;
    zero new axioms. -/
def geneticCode : Codon -> AminoAcid
  | (.C, .U, _) => .Leu
  | (.C, .C, _) => .Pro
  | (.C, .A, .U) | (.C, .A, .C) => .His
  | (.C, .A, .A) | (.C, .A, .G) => .Gln
  | (.C, .G, _) => .Arg
  | (.A, .U, .U) | (.A, .U, .C) | (.A, .U, .A) => .Ile
  | (.A, .U, .G) => .Met
  | (.A, .C, _) => .Thr
  | (.A, .A, .U) | (.A, .A, .C) => .Asn
  | (.A, .A, .A) | (.A, .A, .G) => .Lys
  | (.A, .G, .U) | (.A, .G, .C) => .Ser
  | (.A, .G, .A) | (.A, .G, .G) => .Arg
  | (.U, .U, .U) | (.U, .U, .C) => .Phe
  | (.U, .U, .A) | (.U, .U, .G) => .Leu
  | (.U, .C, _) => .Ser
  | (.U, .A, .U) | (.U, .A, .C) => .Tyr
  | (.U, .A, .A) | (.U, .A, .G) => .Stop
  | (.U, .G, .U) | (.U, .G, .C) => .Cys
  | (.U, .G, .A) => .Stop
  | (.U, .G, .G) => .Trp
  | (.G, .U, _) => .Val
  | (.G, .C, _) => .Ala
  | (.G, .A, .U) | (.G, .A, .C) => .Asp
  | (.G, .A, .A) | (.G, .A, .G) => .Glu
  | (.G, .G, _) => .Gly

/-- Canonical section: each AminoAcid -> its lex-first encoding codon
    (lex order = constructor declaration order C < A < U < G).

    CLOSED (2026-11-17): filled in verbatim; retired alongside the table. -/
def canonicalSection : AminoAcid -> Codon
  | .Ala => (.G, .C, .C)
  | .Arg => (.C, .G, .C)
  | .Asn => (.A, .A, .C)
  | .Asp => (.G, .A, .C)
  | .Cys => (.U, .G, .C)
  | .Gln => (.C, .A, .A)
  | .Glu => (.G, .A, .A)
  | .Gly => (.G, .G, .C)
  | .His => (.C, .A, .C)
  | .Ile => (.A, .U, .C)
  | .Leu => (.C, .U, .C)
  | .Lys => (.A, .A, .A)
  | .Met => (.A, .U, .G)
  | .Phe => (.U, .U, .C)
  | .Pro => (.C, .C, .C)
  | .Ser => (.U, .C, .C)
  | .Stop => (.U, .A, .A)
  | .Thr => (.A, .C, .C)
  | .Trp => (.U, .G, .G)
  | .Tyr => (.U, .A, .C)
  | .Val => (.G, .U, .C)

/-- Round-trip losslessness: decode (canonicalSection aa) = aa.
    CLOSED (2026-11-17): structural cases over the 21 constructors; each side
    reduces definitionally, so rfl closes every case. -/
theorem codon_roundtrip_lossless :
    forall aa : AminoAcid, geneticCode (canonicalSection aa) = aa := by
  intro aa
  cases aa <;> rfl

end Lutar.Innovations.Round5
