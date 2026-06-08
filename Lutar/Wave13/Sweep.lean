/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Wave 13 — Full proof-sweep pack (EXPERIMENTAL until CI-green)

This module collects NEW, rock-solid, `axiom`-free, `sorry`-free obligations closed
during the Wave-13 sweep. Every result here is EXPERIMENTAL and is NEVER folded into
the locked-proven set {F1, F11, F12, F18, F19}. Λ (F23) unconditional uniqueness stays
**Conjecture 1** and is neither claimed nor attempted here. The Byzantine BFT safety
statement (Khipu **Conjecture 2**, `Lutar/Innovations/round12/Identity_Ayni_Quorum.lean`)
stays an honest conjecture; this module only proves a clearly-scoped *single-valued-vote
shadow*, which is a strictly weaker, non-Byzantine model and is labeled as such.

## What is PROVED here (sorry-free, axiom-free)

* `quorum_agreement_single_valued_vote` — the SIMPLIFIED (non-Byzantine) shadow of quorum
  agreement: when each organ's vote is given by a *total function* `voteOf : Fin n → Verdict`
  (single-valued **by construction**, i.e. no equivocation is even representable), any two
  quorums whose intersection exceeds the fault budget agree. This is NOT Khipu Conjecture 2:
  the real Byzantine model permits a faulty organ to equivocate (send different verdicts to
  different peers), which a single total `voteOf` cannot express. We state the weaker fact
  honestly and reuse the in-tree, sorry-free `quorum_intersection_honest`.

* `hm_bottleneck_clean` — the clean (`x⁻¹`, not `rpow (-1)`) statement of the Tetractys
  harmonic-mean bottleneck: if the harmonic mean `n / ∑ xᵢ⁻¹` is below a positive threshold
  and every `xᵢ > 0`, then some axis `xᵢ` is itself below the threshold. Pure order/field
  reasoning (`Finset.sum_le_sum`, `inv_anti₀`); no `rpow`. This is a clean-statement companion
  to the existing `tetractys_hm_bottleneck` (which is left untouched, as its `rpow (-1)` form is
  bridged only with toolchain-sensitive rewrites).

## Citations (real, clean-room)

* BFT quorum intersection (n ≥ 3f+1) — Lamport, Shostak, Pease, "The Byzantine Generals
  Problem," ACM TOPLAS 4(3):382–401 (1982); Castro & Liskov, "Practical Byzantine Fault
  Tolerance," OSDI (1999).
* List search membership lemma `List.find?_isSome` — Lean 4 core `Init.Data.List.Find`
  (Apache-2.0), used to close `findReplayRoot_complete` in
  `Lutar/PRNG/K10v2_ReplayRoot.lean` (edited in-place this wave).
-/
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Lutar.Innovations.round12.Identity_Ayni_Quorum

namespace Lutar
namespace Wave13
namespace Sweep

open Finset

variable {n : ℕ}

/-- **Quorum agreement under a single-valued vote function (SIMPLIFIED shadow — NOT
Byzantine Conjecture 2).**

If each organ's verdict for the round is determined by a *total function*
`voteOf : Fin n → Verdict`, then equivocation is not even representable, so any two
quorums `Q₁ Q₂` obeying the Ubuntu charter `n ≥ 3*f + 1` necessarily agree: `v₁ = v₂`.

The proof reuses the in-tree, sorry-free combinatorial core
`Lutar.Round12.AyniQuorum.quorum_intersection_honest`, which gives
`(Q₁ ∩ Q₂).card > f ≥ 0`, hence the intersection is nonempty. Any organ `o` in the
intersection lies in both quorums, so `v₁ = voteOf o = v₂`.

**This is strictly weaker than `ubuntu_quorum_safety` (Khipu Conjecture 2).** The real
Byzantine model represents an honest organ's single-valuedness as a *property of the
consensus predicate*, allowing faulty organs to equivocate — which a single total
`voteOf` cannot model. Conjecture 2 therefore remains open in
`Lutar/Innovations/round12/Identity_Ayni_Quorum.lean`; this lemma does not resolve it. -/
theorem quorum_agreement_single_valued_vote
    {Verdict : Type} (f : ℕ) (hn : n ≥ 3 * f + 1)
    (Q₁ Q₂ : Finset (Fin n))
    (h₁ : Q₁.card ≥ n - f) (h₂ : Q₂.card ≥ n - f)
    (voteOf : Fin n → Verdict)
    (v₁ v₂ : Verdict)
    (hv₁ : ∀ o ∈ Q₁, voteOf o = v₁)
    (hv₂ : ∀ o ∈ Q₂, voteOf o = v₂) :
    v₁ = v₂ := by
  -- Sorry-free combinatorial core: the two quorums share strictly more than `f` organs.
  have hpos : (Q₁ ∩ Q₂).card > f :=
    Lutar.Round12.AyniQuorum.quorum_intersection_honest f hn Q₁ Q₂ h₁ h₂
  -- In particular the intersection is nonempty.
  have hne : (Q₁ ∩ Q₂).Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨o, ho⟩ := hne
  rw [Finset.mem_inter] at ho
  -- `o` lies in both quorums, so its single vote equals both verdicts.
  have e₁ : voteOf o = v₁ := hv₁ o ho.1
  have e₂ : voteOf o = v₂ := hv₂ o ho.2
  rw [← e₁, e₂]

/-- **Tetractys harmonic-mean bottleneck (clean statement, sorry-free, axiom-free).**

If the harmonic mean `n / (∑ xᵢ⁻¹)` of strictly positive axes `x : Fin n → ℝ` is below a
positive `threshold`, then at least one axis is itself below `threshold`.

Proof (contrapositive): if every `xᵢ ≥ threshold` then `xᵢ⁻¹ ≤ threshold⁻¹`, so
`∑ xᵢ⁻¹ ≤ n / threshold`, whence `n / (∑ xᵢ⁻¹) ≥ threshold`, contradicting the hypothesis.

Source: Hardy, Littlewood, Pólya, *Inequalities*, CUP (1934), §2.5 (HM ≤ GM ≤ AM family).
This uses the clean `xᵢ⁻¹` formulation rather than the `rpow (-(1:ℝ))` form of the existing
`Lutar.Innovations.Round5.tetractys_hm_bottleneck`, which is left untouched. -/
theorem hm_bottleneck_clean
    (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (threshold : ℝ) (ht : 0 < threshold)
    (hHM_low : (n : ℝ) / (Finset.univ.sum (fun i => (x i)⁻¹)) < threshold) :
    ∃ i : Fin n, x i < threshold := by
  by_contra h
  push_neg at h
  -- h : ∀ i, threshold ≤ x i.
  have hsum_pos : 0 < Finset.univ.sum (fun i => (x i)⁻¹) := by
    apply Finset.sum_pos
    · intro i _; exact inv_pos.mpr (hx i)
    · exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
  have hbound : Finset.univ.sum (fun i => (x i)⁻¹) ≤ (n : ℝ) / threshold := by
    have hstep : Finset.univ.sum (fun i => (x i)⁻¹)
        ≤ Finset.univ.sum (fun (_ : Fin n) => threshold⁻¹) := by
      apply Finset.sum_le_sum
      intro i _
      exact inv_anti₀ ht (h i)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_comm,
      div_eq_mul_inv] using hstep
  have hge : threshold ≤ (n : ℝ) / (Finset.univ.sum (fun i => (x i)⁻¹)) := by
    rw [le_div_iff₀ hsum_pos]
    calc threshold * (Finset.univ.sum (fun i => (x i)⁻¹))
        ≤ threshold * ((n : ℝ) / threshold) :=
          mul_le_mul_of_nonneg_left hbound (le_of_lt ht)
      _ = (n : ℝ) := by field_simp
  linarith

end Sweep
end Wave13
end Lutar
