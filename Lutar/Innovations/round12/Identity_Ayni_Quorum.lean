/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Round 12 — EASY: Ayni / Ubuntu quorum-intersection convergence

**Unification target (Theme C — Reciprocity / quorum):**
CT-E5 (Ubuntu BFT safety) ∥ CT-3 (Spinoza / Kolmogorov–Nagumo nesting).

> *umuntu ngumuntu ngabantu* — "a person is a person through other persons."
> No single organ *is* the verdict; trust is constituted only through the agreement of peers.
> This is the Andean *Ayni* (balanced reciprocity) / African *Ubuntu* reading of Byzantine
> quorum intersection (n ≥ 3f+1), and the discrete shadow of Λ's geometric-mean nesting.

## What is PROVED here (sorry-free)

`quorum_intersection_honest` — the load-bearing combinatorial fact under all PBFT-style safety:
with `n` organs, at most `f` faulty, and the Ubuntu charter `n ≥ 3*f + 1`, **any two quorums of
size ≥ n − f intersect in strictly more than `f` organs**, hence (since at most `f` are faulty)
they share at least one *honest* organ. Pure `Finset.card` arithmetic + `omega`; no analysis.

This is the formal content of "a person is a person through other persons": two committable
quorums cannot be disjoint in their honest membership, so they cannot vouch for conflicting
verdicts without an honest organ contradicting itself.

## Scope of `ubuntu_quorum_safety` (sorry closed, conjecture NOT elevated)

`ubuntu_quorum_safety` is proved sorry-free **in the function-vote model**: `voteOf` gives each organ one
vote, so any organ in the non-empty quorum intersection forces `v1 = v2`. This model does not represent
Byzantine equivocation, so **Khipu Conjecture 2 remains a conjecture**. The open refinement is the
equivocation model (faulty organs may vouch for several verdicts; `HONEST_ORGAN_SINGLE_VALUED` for honest ones).

## Citations (real, inherited from the Eastern/Indigenous pod)

* *Ubuntu* — Ramose, *African Philosophy through Ubuntu*, Mond Books (1999);
  Metz, "Toward an African Moral Theory," *Journal of Political Philosophy* 15(3) (2007).
* *Yanantin / Ayni* (Andean balanced reciprocity) — Webb (ed.), *Yanantin and Masintin in the
  Andean World*, Univ. of New Mexico Press (2012).
* BFT quorum intersection (n ≥ 3f+1) — Lamport, Shostak, Pease, "The Byzantine Generals Problem,"
  *ACM TOPLAS* 4(3):382–401 (1982); Castro & Liskov, "Practical Byzantine Fault Tolerance," OSDI (1999).
* Composition / nesting — Kolmogorov (1930), Nagumo (1930), quasi-arithmetic mean nesting (cited in v22).

Coordinates with runtime: `szl-holdings/a11oy/szl_khipu_consensus.py` and the planned
`/api/a11oy/v1/formula/ayni-quorum` endpoint (Round-12 wire PR).

NEW file under `Lutar/Innovations/round12/`; locked kernel (749/14/163 @ c7c0ba17) untouched.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Lutar
namespace Round12
namespace AyniQuorum

open Finset

variable {n : ℕ}

/-- **Ayni / Ubuntu quorum-intersection (sorry-free).**
With `n` organs and a fault budget `f` obeying the Ubuntu charter `n ≥ 3*f + 1`, any two quorums
`Q₁ Q₂ ⊆ univ` each of size `≥ n − f` intersect in strictly more than `f` organs. Since at most
`f` organs are faulty, the intersection therefore contains at least one *honest* organ: two
committable quorums always share a peer that vouches for both — "a person is a person through
other persons." -/
theorem quorum_intersection_honest
    (f : ℕ) (hn : n ≥ 3 * f + 1)
    (Q₁ Q₂ : Finset (Fin n))
    (h₁ : Q₁.card ≥ n - f) (h₂ : Q₂.card ≥ n - f) :
    (Q₁ ∩ Q₂).card > f := by
  -- Inclusion–exclusion: |Q₁ ∪ Q₂| + |Q₁ ∩ Q₂| = |Q₁| + |Q₂|.
  have hie : (Q₁ ∪ Q₂).card + (Q₁ ∩ Q₂).card = Q₁.card + Q₂.card :=
    card_union_add_card_inter Q₁ Q₂
  -- The union is a subset of the whole organ set, so its size is at most n.
  have hsub : (Q₁ ∪ Q₂) ⊆ (univ : Finset (Fin n)) := subset_univ _
  have huniv : (univ : Finset (Fin n)).card = n := by simp
  have hunion_le : (Q₁ ∪ Q₂).card ≤ n := by
    have := card_le_card hsub
    simpa [huniv] using this
  -- Combine the three facts with linear arithmetic. n ≥ 3f+1 makes n − 2f ≥ f+1 > f.
  omega

/-- **Honest organ predicate.** `committed v organs faulty` says verdict `v` is committed by a
quorum of size `≥ n − f` among the non-faulty organs. (Model placeholder; the runtime consensus
layer supplies the concrete predicate. We only need its *quorum* and *single-valued* shape.) -/
def QuorumOf (Q : Finset (Fin n)) (f : ℕ) : Prop := Q.card ≥ n - f

/-- **Ubuntu quorum safety, function-vote model (PROVED, sorry-free).**
If two verdicts `v1`, `v2` are each backed by a quorum (size `>= n - f`) under the Ubuntu charter
`n >= 3*f + 1`, and every organ's vote is given by the single function `voteOf`, then `v1 = v2`.

SCOPE (honest): `voteOf : Fin n -> Verdict` assigns each organ exactly one vote, so this model builds
single-valuedness into every organ, faulty or not. It does NOT model Byzantine equivocation and does
NOT settle Khipu Conjecture 2 (BFT safety with equivocating organs), which remains open alongside
`khipu_consensus_safety`. The `faulty`/`hf` hypotheses are unused here and are kept for that refinement. -/
theorem ubuntu_quorum_safety
    {Verdict : Type} (f : ℕ) (hn : n ≥ 3 * f + 1)
    (faulty : Finset (Fin n)) (hf : faulty.card ≤ f)
    (Q₁ Q₂ : Finset (Fin n)) (hq₁ : QuorumOf Q₁ f) (hq₂ : QuorumOf Q₂ f)
    (voteOf : Fin n → Verdict)        -- the verdict each organ vouches for this round
    (v₁ v₂ : Verdict)
    (hv₁ : ∀ o ∈ Q₁, voteOf o = v₁)   -- Q₁ all vouch v₁
    (hv₂ : ∀ o ∈ Q₂, voteOf o = v₂)   -- Q₂ all vouch v₂
    : v₁ = v₂ := by
  have hpos : (Q₁ ∩ Q₂).card > f :=
    quorum_intersection_honest f hn Q₁ Q₂ hq₁ hq₂
  -- The intersection is non-empty (card > f >= 0). `voteOf` is a function, so the chosen organ
  -- casts exactly one vote, which equals both verdicts.
  obtain ⟨o, ho⟩ : (Q₁ ∩ Q₂).Nonempty := Finset.card_pos.mp (by omega)
  rw [Finset.mem_inter] at ho
  exact (hv₁ o ho.1).symm.trans (hv₂ o ho.2)

/-! ### Correspondence summary

`quorum_intersection_honest` is **proved, sorry-free**: it is the Ayni/Ubuntu reciprocity invariant
— any two committable quorums share strictly more than `f` organs, hence an honest one. This is the
runtime guarantee under `szl_khipu_consensus.py`: conflicting verdicts cannot both gather a quorum
without an honest organ vouching for both. `ubuntu_quorum_safety` is proved in the function-vote model; the Byzantine (equivocation) version, Khipu Conjecture 2, remains open.

Reference: Lamport–Shostak–Pease (1982); Castro–Liskov (1999); Ramose (1999); Metz (2007); Webb (2012). -/

end AyniQuorum
end Round12
end Lutar
