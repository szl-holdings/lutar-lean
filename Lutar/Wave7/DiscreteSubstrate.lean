/-
# WAVE 7 — Mathlib-FREE discrete substrate guarantees (bare `lean` 4.13.0 verified)

A fresh batch of elementary, kernel-checkable facts grounding product guarantees in the
a11oy / killinchu / UDS substrate. Lean core ONLY (no Mathlib, no `Real`, no `Finset`, no
`List.sum`) so the module compiles under bare `lean` and every `#print axioms` is
verbatim-disclosable. Wired into the lutar-lean `lake build` kernel-check root so CI
re-verifies it.

DECONFLICTION (honest): these are NEW and DISJOINT from the wave-5 `Wave5.DiscreteSubstrate`
lemmas AND from the wave-6 `Wave6.{GraphSubstrate,InfoSubstrate}` lemmas. In particular
wave-6 already closed bounded-frontier DAG termination (F-G5) and conformal coverage
CONSERVATION; this wave instead proves the conformal RANK-COUNT calibration/antitone
backbone (the p-value direction) and the Doob TWO-SIDED audit envelope — neither is in any
prior wave.

HONESTY: nothing here proves Λ uniqueness (still Conjecture 1). These are honest,
load-bearing finite/combinatorial lemmas, NOT analytic limit theorems. Each is the
DISCRETE core of a published result. No `sorryAx`, no declared Lutar axioms.

## Citations (proof-technique provenance)
- W7-4 conformal rank/exchangeability calibration count (Vovk, Gammerman, Shafer 2005,
  *Algorithmic Learning in a Random World*; Lei et al. 2018, JASA 113:1094): the conformal
  p-value is the normalized rank — the count of calibration scores at-or-above the test
  score. We prove (a) the calibration bound `rankCount ≤ n` (so the normalized p-value ≤ 1)
  and (b) rank ANTITONICITY in the test score (a stricter conformity demand never raises
  the count) — the monotone-calibration backbone of the conformal p-value. (Distinct from
  the wave-5/wave-6 coverage-CONSERVATION lemmas.)
- W7-6 Doob optional-stopping TWO-SIDED envelope (Doob 1953, *Stochastic Processes*):
  extends wave-5 W5-5 (no early-stop DEFLATION below the open) — on a monotone
  (non-decreasing) audit accumulator any bounded stop value lies in `[open, close]`, so a
  bounded audit can neither under- nor over-report. (Distinct from wave-6's metric
  contraction-nonincrease.)
-/
namespace Wave7.DiscreteSubstrate

/-! ## W7-4 — Conformal rank/exchangeability calibration count
    (killinchu distribution-free trust intervals; Vovk–Gammerman–Shafer 2005). -/

/-- The conformal rank-count of a test score `s` among calibration scores `l`: how many
    are at-or-above `s`. The (unnormalized) conformal p-value numerator. -/
def rankCount (s : Nat) (l : List Nat) : Nat :=
  (l.filter (fun x => decide (s ≤ x))).length

/-- **W7-4a — calibration bound: the rank-count never exceeds the sample size.** Hence the
    normalized p-value `rankCount / |l|` is ≤ 1 — the well-typed base of `p ∈ (0,1]`. -/
theorem w7_4a_rankCount_le_total (s : Nat) (l : List Nat) :
    rankCount s l ≤ l.length :=
  List.length_filter_le _ l

/-- **W7-4b — rank antitonicity in the test score.** Raising the test score `s` (a STRICTER
    conformity demand) never increases the rank-count: fewer calibration scores clear a
    higher bar. The monotone-calibration backbone of the conformal p-value. -/
theorem w7_4b_rankCount_antitone (s t : Nat) (l : List Nat) (h : s ≤ t) :
    rankCount t l ≤ rankCount s l := by
  unfold rankCount
  induction l with
  | nil => simp
  | cons x xs ih =>
    by_cases ht : t ≤ x
    · -- t ≤ x ⇒ s ≤ x, so both filters keep the head
      have hsx : s ≤ x := Nat.le_trans h ht
      simp only [List.filter_cons, decide_eq_true_eq, ht, hsx, if_true,
        List.length_cons]
      omega
    · -- t ≤ x fails: t-filter drops the head
      have ht' : ¬ (t ≤ x) := ht
      simp only [List.filter_cons, decide_eq_true_eq, ht', if_false]
      by_cases hsx : s ≤ x
      · simp only [hsx, if_true, List.length_cons]; omega
      · simp only [hsx, if_false]; omega

/-- **W7-4c — p-value floor: the test score itself always counts (rank ≥ 1 on its own
    list).** Including the test score in the calibration list, the rank-count is at least 1
    — the standard `(1 + #{cal ≥ test})/(n+1)` conformal floor that keeps the p-value
    strictly positive (no zero p-values, an anti-overconfidence guarantee). -/
theorem w7_4c_rankCount_self_ge_one (s : Nat) (l : List Nat) :
    1 ≤ rankCount s (s :: l) := by
  unfold rankCount
  have hself : s ≤ s := Nat.le_refl s
  simp only [List.filter_cons, decide_eq_true_eq, hself, if_true, List.length_cons]
  omega

/-! ## W7-6 — Doob optional-stopping two-sided envelope
    (UDS receipt-stream anti-gaming; Doob 1953). -/

/-- A monotone (non-decreasing) audit accumulator: `acc i ≤ acc (i+1)` for all `i`. -/
def MonoAcc (acc : Nat → Nat) : Prop := ∀ i, acc i ≤ acc (i+1)

/-- **W7-6a — monotone accumulator is non-decreasing over any horizon.** From the
    one-step hypothesis, `acc m ≤ acc n` whenever `m ≤ n`. -/
theorem w7_6a_acc_mono {acc : Nat → Nat} (hmono : MonoAcc acc)
    {m n : Nat} (hmn : m ≤ n) : acc m ≤ acc n := by
  induction n with
  | zero =>
    have : m = 0 := Nat.le_zero.mp hmn
    subst this; exact Nat.le_refl _
  | succ k ih =>
    rcases Nat.lt_or_ge m (k+1) with hlt | hge
    · exact Nat.le_trans (ih (Nat.lt_succ_iff.mp hlt)) (hmono k)
    · have : m = k+1 := Nat.le_antisymm hmn hge
      subst this; exact Nat.le_refl _

/-- **W7-6 — two-sided audit envelope.** For a bounded stop time `τ` with `open ≤ τ ≤ close`
    on a monotone accumulator, the audited value `acc τ` lies in `[acc open, acc close]`.
    Generalizes wave-5 W5-5 (no early-stop DEFLATION below the open) to also bound the
    value from ABOVE by the close — a bounded audit can neither under- nor over-report. -/
theorem w7_6_audit_envelope {acc : Nat → Nat} (hmono : MonoAcc acc)
    (o τ c : Nat) (h1 : o ≤ τ) (h2 : τ ≤ c) :
    acc o ≤ acc τ ∧ acc τ ≤ acc c :=
  ⟨w7_6a_acc_mono hmono h1, w7_6a_acc_mono hmono h2⟩

end Wave7.DiscreteSubstrate

-- ## Wave-7 bare-`lean` axiom disclosure (also re-checked by CI in the build log).
#print axioms Wave7.DiscreteSubstrate.w7_4a_rankCount_le_total
#print axioms Wave7.DiscreteSubstrate.w7_4b_rankCount_antitone
#print axioms Wave7.DiscreteSubstrate.w7_4c_rankCount_self_ge_one
#print axioms Wave7.DiscreteSubstrate.w7_6a_acc_mono
#print axioms Wave7.DiscreteSubstrate.w7_6_audit_envelope
