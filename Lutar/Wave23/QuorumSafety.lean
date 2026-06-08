/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 23 — Conditional Khipu BFT SAFETY (agreement / no split-brain)

## Mission
This file proves the **CONDITIONAL** Khipu Byzantine-fault-tolerant quorum-safety
theorem — the genuine open frontier (Khipu **Conjecture 2**,
`Lutar/Innovations/round12/Identity_Ayni_Quorum.lean :: ubuntu_quorum_safety`).

UNCONDITIONAL BFT safety is and stays **Conjecture 2**: a Byzantine organ can
equivocate (sign two conflicting votes), so safety cannot hold without BOTH the
charter `n ≥ 3f + 1` (Lamport–Shostak–Pease n > 3f bound; n ≤ 3f is impossible —
see `Lutar/Wave8/Byzantine.lean`) AND honest non-equivocation. We do NOT attempt
the false unconditional statement.

Instead — exactly as Wave22 identified slice-multiplicativity as the weakest
checkable hypothesis that turns Λ-uniqueness from FALSE-unconditional into a
CONDITIONAL theorem — we identify the weakest checkable hypothesis that turns
quorum safety into a theorem: **honest non-equivocation under signed votes**.

## The honest model (allows Byzantine equivocation)
Votes are a RELATION `votes : Fin n → Verdict → Prop`, NOT a total function. A
faulty organ `o ∈ faulty` MAY satisfy `votes o a ∧ votes o b` with `a ≠ b`
(equivocation — the essence of a Byzantine fault). This is strictly more general
than the Wave13 `quorum_agreement_single_valued_vote` shadow, which used a total
`voteOf : Fin n → Verdict` and therefore could not even REPRESENT equivocation.

The single checkable hypothesis we add is the standard definition of an honest
node, realized at runtime by ECDSA-P256 cosignatures (one valid signed allow-vote
per honest organ per action — exactly `verifies`/`consents` in
`Lutar/KhipuConsensus.lean`):

  `HonestNonEquivocation` :
      ∀ o, o ∉ faulty → ∀ a b, votes o a → votes o b → a = b.

## What is proven (placeholder-free, axiom-clean, NO new axiom)
- `exists_honest_in_inter` — DISCHARGES the residual that `ubuntu_quorum_safety`
  left as a proof-deferred obligation: from `|Q₁ ∩ Q₂| > f ≥ |faulty|` extract an organ in the
  intersection that is NOT faulty. (Mathlib `Finset.not_subset` + `card_le_card`.)
- `khipu_quorum_safety_conditional` — the CONDITIONAL safety/agreement theorem:
  under `n ≥ 3f+1`, `|faulty| ≤ f`, two quorums of size ≥ n−f certifying v₁,v₂,
  and honest non-equivocation, `v₁ = v₂`. No split-brain.
- `khipu_unique_decision_conditional` / `subsumes_single_valued_shadow` —
  corollary (system-wide unique decision) and a strict-generalization witness
  re-deriving the Wave13 single-valued shadow from the Byzantine-aware theorem.

The combinatorial core `quorum_intersection_honest` (two quorums of size ≥ n−f
intersect in > f organs under `n ≥ 3f+1`) is reused placeholder-free from Round12.

## Honesty / scope (Doctrine v12, LOCKED)
- EXPERIMENTAL (`Lutar.Wave23`). NOT folded into the LOCKED v11 baseline. The
  locked-proven set STAYS EXACTLY 5 `{F1,F11,F12,F18,F19}`. Λ stays Conjecture 1.
- The result is **CONDITIONAL**: hypotheses are `{n ≥ 3f+1, |faulty| ≤ f,
  |Qᵢ| ≥ n−f, honest non-equivocation}`. UNCONDITIONAL BFT safety stays
  Conjecture 2. We label this precisely and never call it unconditional.
- Known-theorem formalization (Castro–Liskov PBFT agreement; Velisarios Coq;
  Tendermint agreement; Lamport–Shostak–Pease). NO new declared axiom, NO proof placeholder,
  NO `native_decide`. Every decl `#print axioms ⊆ {propext, Classical.choice,
  Quot.sound}`.
- Residual (honest): UNCONDITIONAL safety stays open; the `opaque
  canonicalHistory` form in the kernel is NOT touched; liveness (Conjecture 3)
  untouched.

## Citations (real)
- Lamport, Shostak, Pease, "The Byzantine Generals Problem", ACM TOPLAS 4(3),
  1982, doi:10.1145/357172.357176 (n > 3f necessity).
- Castro & Liskov, "Practical Byzantine Fault Tolerance", OSDI 1999 (quorum
  intersection in ≥ one non-faulty replica).
- Rahli, Vukotic, Völp, Esteves-Verissimo, "Velisarios: Byzantine Fault-Tolerant
  Protocols Powered by Coq", ESOP 2018, https://vrahli.github.io/articles/velisarios.pdf
  (machine-checked PBFT agreement — the safety crux we mirror).
- Buchman, "Tendermint: BFT in the Age of Blockchains", MSc thesis 2016, §2
  (agreement: one correct decides v₁, another v₂ ⟹ v₁ = v₂).
- Yin et al., "HotStuff", PODC 2019 (n−f signed quorum certificates).

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Lutar.Innovations.round12.Identity_Ayni_Quorum

namespace Lutar.Wave23.QuorumSafety

open Finset

variable {n : ℕ}

/-! ## §1 Honest-witness extraction — discharges the `ubuntu_quorum_safety` residual -/

/-- **Honest witness extraction (placeholder-free).** If a finite set `S` of organs is
strictly larger than the faulty set, then `S` contains a non-faulty (honest) organ.

This is the step the kernel's `ubuntu_quorum_safety` and the Round12
`AyniQuorum.ubuntu_quorum_safety` left as an honest proof-deferred obligation. We discharge it with
Mathlib's `Finset.not_subset`: if every element of `S` were faulty then
`S ⊆ faulty`, forcing `S.card ≤ faulty.card`, contradicting `faulty.card < S.card`. -/
theorem exists_honest_of_card_gt
    (S faulty : Finset (Fin n)) (hcard : faulty.card < S.card) :
    ∃ o ∈ S, o ∉ faulty := by
  -- If S ⊆ faulty then S.card ≤ faulty.card, contradicting hcard.
  have hnsub : ¬ S ⊆ faulty := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  -- ¬ S ⊆ faulty unpacks to the desired witness.
  rw [Finset.not_subset] at hnsub
  exact hnsub

/-- **Honest organ in the intersection of two committable quorums.** Specialises
`quorum_intersection_honest` (Round12, placeholder-free) and `exists_honest_of_card_gt`:
under the Ubuntu charter `n ≥ 3f+1`, two quorums of size `≥ n − f` share an organ
that is NOT faulty. This is "a person is a person through other persons" made
constructive — the honest witness the old obligation deferred. -/
theorem exists_honest_in_inter
    (f : ℕ) (hn : n ≥ 3 * f + 1)
    (faulty : Finset (Fin n)) (hf : faulty.card ≤ f)
    (Q₁ Q₂ : Finset (Fin n))
    (h₁ : Q₁.card ≥ n - f) (h₂ : Q₂.card ≥ n - f) :
    ∃ o ∈ Q₁ ∩ Q₂, o ∉ faulty := by
  have hpos : (Q₁ ∩ Q₂).card > f :=
    Lutar.Round12.AyniQuorum.quorum_intersection_honest f hn Q₁ Q₂ h₁ h₂
  have hgt : faulty.card < (Q₁ ∩ Q₂).card := lt_of_le_of_lt hf hpos
  exact exists_honest_of_card_gt (Q₁ ∩ Q₂) faulty hgt

/-! ## §2 Conditional Khipu BFT safety (agreement / no split-brain) -/

/-- **Honest non-equivocation (the weakest checkable hypothesis).** Every honest
organ (`o ∉ faulty`) votes for at most one verdict per round. Realized at runtime
by signed votes (one valid signed allow per honest organ per action). A faulty
organ is UNCONSTRAINED — it may vote for several verdicts (equivocation). -/
def HonestNonEquivocation {Verdict : Type}
    (faulty : Finset (Fin n)) (votes : Fin n → Verdict → Prop) : Prop :=
  ∀ o, o ∉ faulty → ∀ a b, votes o a → votes o b → a = b

/-- **CONDITIONAL Khipu BFT SAFETY (agreement / no split-brain) — THEOREM.**

Under the Ubuntu charter `n ≥ 3f + 1`, at most `f` faulty organs, two quorums
`Q₁ Q₂` each of size `≥ n − f`, a vote RELATION `votes` (so faulty organs MAY
equivocate), honest non-equivocation `H_NE`, and `Qᵢ` certifying `vᵢ` (every organ
in `Qᵢ` votes `vᵢ`), the two certified verdicts agree: `v₁ = v₂`.

This is the precise content of PBFT/Tendermint/HotStuff safety: no two conflicting
verdicts can both be quorum-certified, because quorum intersection (`n ≥ 3f+1`)
forces a shared HONEST organ, and an honest organ does not equivocate.

**CONDITIONAL.** UNCONDITIONAL safety stays Khipu Conjecture 2 — dropping
`n ≥ 3f+1` (n ≤ 3f impossibility) or honest non-equivocation re-admits split-brain.
This is the sharp boundary, the BFT analog of slice-multiplicativity for Λ. -/
theorem khipu_quorum_safety_conditional
    {Verdict : Type} (f : ℕ) (hn : n ≥ 3 * f + 1)
    (faulty : Finset (Fin n)) (hf : faulty.card ≤ f)
    (Q₁ Q₂ : Finset (Fin n))
    (h₁ : Q₁.card ≥ n - f) (h₂ : Q₂.card ≥ n - f)
    (votes : Fin n → Verdict → Prop)
    (hNE : HonestNonEquivocation faulty votes)
    (v₁ v₂ : Verdict)
    (hv₁ : ∀ o ∈ Q₁, votes o v₁)
    (hv₂ : ∀ o ∈ Q₂, votes o v₂) :
    v₁ = v₂ := by
  -- A shared HONEST organ exists in Q₁ ∩ Q₂ (quorum intersection + witness extraction).
  obtain ⟨o, hoInter, hoHonest⟩ :=
    exists_honest_in_inter f hn faulty hf Q₁ Q₂ h₁ h₂
  rw [Finset.mem_inter] at hoInter
  -- That honest organ voted for BOTH verdicts (one from each quorum).
  have e₁ : votes o v₁ := hv₁ o hoInter.1
  have e₂ : votes o v₂ := hv₂ o hoInter.2
  -- Honest non-equivocation forces the two verdicts to coincide.
  exact hNE o hoHonest v₁ v₂ e₁ e₂

/-- **Corollary (unique decision across the whole quorum system).** Under honest
non-equivocation and the charter, EVERY pair of committable quorums agrees: the
decided verdict is well-defined system-wide. The strengthened, Byzantine-aware
analog of `Wave10.QuorumIntersection.quorum_unique_decision` (which assumed GLOBAL
honesty); here only honest organs are constrained, faulty ones may equivocate. -/
theorem khipu_unique_decision_conditional
    {Verdict : Type} (f : ℕ) (hn : n ≥ 3 * f + 1)
    (faulty : Finset (Fin n)) (hf : faulty.card ≤ f)
    (votes : Fin n → Verdict → Prop)
    (hNE : HonestNonEquivocation faulty votes)
    (Q₁ Q₂ : Finset (Fin n))
    (h₁ : Q₁.card ≥ n - f) (h₂ : Q₂.card ≥ n - f)
    (v₁ v₂ : Verdict)
    (hv₁ : ∀ o ∈ Q₁, votes o v₁)
    (hv₂ : ∀ o ∈ Q₂, votes o v₂) :
    v₁ = v₂ :=
  khipu_quorum_safety_conditional f hn faulty hf Q₁ Q₂ h₁ h₂ votes hNE v₁ v₂ hv₁ hv₂

/-- **Strict generalization witness.** The Wave13 single-valued shadow is the
special case where `votes` comes from a total function `voteOf` (no organ can
equivocate, so `HonestNonEquivocation` holds vacuously-strongly for ALL organs).
This re-derives `quorum_agreement_single_valued_vote`'s conclusion from the
Byzantine-aware theorem, witnessing that Wave23 is strictly more general. -/
theorem subsumes_single_valued_shadow
    {Verdict : Type} (f : ℕ) (hn : n ≥ 3 * f + 1)
    (Q₁ Q₂ : Finset (Fin n))
    (h₁ : Q₁.card ≥ n - f) (h₂ : Q₂.card ≥ n - f)
    (voteOf : Fin n → Verdict)
    (v₁ v₂ : Verdict)
    (hv₁ : ∀ o ∈ Q₁, voteOf o = v₁)
    (hv₂ : ∀ o ∈ Q₂, voteOf o = v₂) :
    v₁ = v₂ := by
  -- Model the total function as a relation `votes o a := voteOf o = a` and take
  -- `faulty = ∅`. Honest non-equivocation holds since a function is single-valued.
  have hf : (∅ : Finset (Fin n)).card ≤ f := by simp
  have hNE : HonestNonEquivocation (∅ : Finset (Fin n)) (fun o a => voteOf o = a) := by
    intro o _ a b ha hb
    -- ha : voteOf o = a, hb : voteOf o = b
    rw [← ha, ← hb]
  exact khipu_quorum_safety_conditional f hn ∅ hf Q₁ Q₂ h₁ h₂
    (fun o a => voteOf o = a) hNE v₁ v₂ hv₁ hv₂

#print axioms exists_honest_of_card_gt
#print axioms exists_honest_in_inter
#print axioms khipu_quorum_safety_conditional
#print axioms khipu_unique_decision_conditional
#print axioms subsumes_single_valued_shadow

end Lutar.Wave23.QuorumSafety
