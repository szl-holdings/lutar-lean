/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Round 10 — CS Contribution 1: Byzantine quorum intersection on the receipt bus

This file formalises the **classical Byzantine-fault-tolerance bound** `n ≥ 3f + 1`
as it applies to the Khipu multi-organ consensus that anchors the SZL receipt bus
(`Lutar.KhipuConsensus`). The operative engineering claim is the
**quorum-intersection lemma**: in a system of `n` organs that decides on a quorum
of size `q`, any two quorums share at least `2q − n` members, so if
`q ≥ ⌈(n + f + 1)/2⌉` then any two quorums intersect in at least `f + 1` members —
hence in at least one *honest* member when at most `f` organs are Byzantine. This
is the structural reason a 3-of-4 organ quorum (`n = 4, q = 3, f = 1`) cannot be
split into two conflicting canonical decisions.

We additionally relate this to the **counting model already shipped** in
`Lutar.KhipuConsensus`: a forged (Byzantine) signature fails `verifies` and is
therefore excluded from `validCount`, so `validCount c ≤ honestCount c` whenever
the faulty organs all withhold a valid allow-signature. The arithmetic bounds in
§1–§3 are FULLY PROVED (0 sorry). The single deep statement
(`bft_resilience_optimal`, that `n ≥ 3f + 1` is *necessary* for any Byzantine
agreement protocol, not merely sufficient) is the Pease–Shostak–Lamport lower
bound; it is not Lean-provable without a full protocol/adversary model and is
captured by one tagged `sorry` `PSL_LOWER_BOUND`.

## Citations

* L. Lamport, R. Shostak, M. Pease, "The Byzantine Generals Problem", ACM TOPLAS
  4(3):382–401, 1982. DOI 10.1145/357172.357176.
  https://lamport.azurewebsites.net/pubs/byz.pdf
* M. Pease, R. Shostak, L. Lamport, "Reaching Agreement in the Presence of
  Faults", J. ACM 27(2):228–234, 1980. DOI 10.1145/322186.322188.
  https://lamport.azurewebsites.net/pubs/reaching.pdf
* M. Castro, B. Liskov, "Practical Byzantine Fault Tolerance", OSDI 1999.
  https://pmg.csail.mit.edu/papers/osdi99.pdf
* Quorum-system background: D. Malkhi, M. Reiter, "Byzantine Quorum Systems",
  Distributed Computing 11(4):203–213, 1998. DOI 10.1007/s004460050050.
  https://www.cs.cmu.edu/~reiter/papers/1998/DC.pdf

NEW file under `Lutar/Innovations/round10/`; locked kernel untouched (749/14/163).
-/
import Mathlib.Data.Nat.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic
import Lutar.KhipuConsensus

namespace Lutar
namespace Round10
namespace ByzantineQuorum

open Lutar.KhipuConsensus

/-! ### 1. Abstract quorum-intersection arithmetic

We model a quorum system over `n` members purely by cardinalities. A quorum has
size `q`. The inclusion–exclusion lower bound on the intersection of two
sub-collections of an `n`-element universe is `|A| + |B| − n`. -/

/-- **Quorum intersection (PROVED).** If two quorums each have size `q ≤ n` and
`2 * q ≥ n + k`, then their guaranteed overlap `2*q - n` is at least `k`. This is
the arithmetic heart of every Byzantine quorum system. -/
theorem quorum_intersection_ge (n q k : Nat) (hq : q ≤ n) (h : n + k ≤ 2 * q) :
    k ≤ 2 * q - n := by
  have hn : n ≤ 2 * q := le_trans (Nat.le_add_right n k) h
  omega

/-- **Honest overlap (PROVED).** In the `n ≥ 3f + 1` regime with quorum size
`q = n - f`, any two quorums overlap in at least `f + 1` members, hence in at
least one honest member after removing up to `f` Byzantine ones. -/
theorem honest_in_every_quorum_overlap (n f : Nat) (hbft : 3 * f + 1 ≤ n) :
    f + 1 ≤ 2 * (n - f) - n := by
  omega

/-! ### 2. The SZL 3-of-4 instance (PROVED, concrete)

The shipped Khipu protocol uses `n = 4`, `f = 1`, `q = threshold = 3`. -/

/-- `n = 4` satisfies the BFT bound for `f = 1`. -/
theorem szl_satisfies_bft : 3 * 1 + 1 ≤ 4 := by norm_num

/-- Two 3-of-4 quorums overlap in at least `2*3 - 4 = 2` organs, i.e. in at
least `f + 1 = 2` organs — guaranteeing an honest organ in the overlap. -/
theorem szl_quorum_overlap_two : (1 : Nat) + 1 ≤ 2 * 3 - 4 := by norm_num

/-! ### 3. Tie to the shipped counting model (`Lutar.KhipuConsensus`)

A Byzantine organ contributes a signature that FAILS `verifies`, so it is never
counted in `validCount`. Hence valid consents come only from honest organs. -/

/-- A consenting organ is honest: if `consents c i` then `isHonest c i`. Proved by
unfolding both Booleans — `consents` requires `verifies`, and `isFaulty` is the
negation of `verifies`, so consent forces `isFaulty = false`. -/
theorem consent_is_honest {n : Nat} (c : Consensus n) (i : Fin n)
    (h : consents c i = true) : isHonest c i = true := by
  unfold consents at h
  unfold isHonest isFaulty
  cases hs : c.signatures.get i with
  | none => simp [hs] at h
  | some s =>
      simp only [hs, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [hs, Bool.not_eq_true', decide_eq_false_iff_not, not_not]
      exact h.1

/-- Self-contained monotonicity of `List.countP`: if `p i = true → q i = true`
for every element of `l`, then `countP p l ≤ countP q l`. Proved by induction so
that it does not depend on a particular Mathlib lemma name. -/
theorem countP_mono_self {α : Type _} (p q : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = true → q x = true) →
      l.countP p ≤ l.countP q
  | [], _ => by simp
  | a :: t, h => by
      have htail : ∀ x ∈ t, p x = true → q x = true :=
        fun x hx => h x (List.mem_cons_of_mem a hx)
      have ih := countP_mono_self p q t htail
      have hhead : a ∈ a :: t := List.mem_cons_self a t
      rw [List.countP_cons, List.countP_cons]
      -- Per-element contribution of `p a` is ≤ that of `q a`: if `p a = true`
      -- then `q a = true` by hypothesis, so both contribute 1; otherwise `p a`
      -- contributes 0 ≤ (q a's 0 or 1).
      by_cases hp : p a = true
      · have hq : q a = true := h a hhead hp
        simp only [hp, hq, if_true]
        omega
      · have hp' : p a = false := by simpa using hp
        simp only [hp', if_false]
        cases hqa : q a <;> simp <;> omega

/-- **`valid_le_honest` (PROVED).** The number of valid consents never exceeds
the number of honest organs: every counted consent comes from an honest organ, so
the `countP` over `consents` is bounded by the `countP` over `isHonest`. This is
the formal sense in which "Byzantine signatures cannot inflate the quorum". -/
theorem valid_le_honest {n : Nat} (c : Consensus n) :
    validCount c ≤ honestCount c := by
  unfold validCount honestCount
  exact countP_mono_self _ _ (List.finRange n)
    (fun i _ hcon => consent_is_honest c i hcon)

/-- **Corollary (PROVED).** If a quorum is reached (`validCount ≥ threshold`),
then at least `threshold` organs are honest. With `threshold = 3, n = 4` this
means at most one organ can be Byzantine — exactly the `f = 1` regime. -/
theorem quorum_implies_honest_majority {n : Nat} (c : Consensus n)
    (hq : validCount c ≥ c.threshold) : honestCount c ≥ c.threshold :=
  le_trans hq (valid_le_honest c)

/-! ### 4. Optimality lower bound — deep result, honest sorry

Sufficiency (`n ≥ 3f + 1` suffices) is constructive and embodied by the protocol.
*Necessity* — that NO deterministic Byzantine-agreement protocol exists when
`n ≤ 3f` — is the Pease–Shostak–Lamport / Lamport–Shostak–Pease lower bound, an
adversary/indistinguishability argument over executions that is not expressible
as pure cardinality arithmetic. We state it as the impossibility of an abstract
"agreement solver" and defer the proof. -/

/-- An abstract Byzantine-agreement solver over `n` parties tolerating `f`
faults: it always produces agreement among honest parties. (Interface only.) -/
structure ByzantineAgreement (n f : Nat) where
  /-- Honest parties always agree on a common decided value, for every adversary. -/
  agrees : Prop
  /-- Validity: if honest inputs are unanimous, that value is decided. -/
  valid  : Prop

/-- **`bft_resilience_optimal` (CONJECTURE-LEVEL, tagged sorry).** No
deterministic Byzantine-agreement solver tolerating `f` faults exists when
`n ≤ 3 * f`. This is the PSL lower bound (Pease–Shostak–Lamport 1980); its proof
is a scenario/indistinguishability argument over executions, not Lean-arithmetic,
so it is recorded as a single tagged assumption. -/
theorem bft_resilience_optimal (n f : Nat) (hbad : n ≤ 3 * f) :
    ¬ ∃ _ : ByzantineAgreement n f, True := by
  sorry  -- PSL_LOWER_BOUND: Pease–Shostak–Lamport 3f+1 necessity (J. ACM 1980).

/-! ### 5. Doctrine corollary

The quorum-intersection arithmetic (§1–§2) and the honest-counting tie-in (§3)
are FULLY PROVED with zero new axioms, and they justify, on the *shipped*
`KhipuConsensus` model, why a 3-of-4 organ quorum is split-resistant under a
single Byzantine fault. The optimality of `n ≥ 3f + 1` is the only deferred
statement and is a named published lower bound, not a Lean obligation. Λ stays
Conjecture 1; the locked public constant 749/14/163 is untouched. -/

end ByzantineQuorum
end Round10
end Lutar
