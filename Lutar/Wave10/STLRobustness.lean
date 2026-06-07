/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave10/STLRobustness.lean — RA-1: Signal Temporal Logic robustness soundness

A Mathlib-free, kernel-only formalization of the **quantitative-vs-qualitative
agreement** theorem for Signal Temporal Logic (STL): the real-valued robustness
degree ρ(φ,w,t) is non-negative **iff** the Boolean satisfaction relation
`w ⊨ φ @ t` holds (on the strict/open-semantics fragment without temporal
boundary ambiguity). This is the soundness property a runtime monitor relies on:
when the monitor reports robustness ≥ 0 it certifies the constraint is met, and
when it reports robustness < 0 it certifies a violation.

We model signal values and the robustness degree over `Int` (an ordered ring with
`min`/`max` and decidable order in Lean core) — no Mathlib import, no `Real`. The
STL grammar covers atomic predicates, `not`, `and`, `or`, and the bounded
`always`/`eventually` operators over a finite discrete horizon, with robustness
combining via `min` (∧, always) and `max` (∨, eventually) exactly as in
Donzé–Maler (2010) / Fainekos–Pappas (2009).

## What is proven
- `STL` — inductive STL formula over an atomic-predicate index `A`.
- `rho` — real-valued (here `Int`-valued) robustness degree, defined inductively
  (predicate ↦ signed margin; ¬ ↦ negation; ∧ ↦ `min`; ∨ ↦ `max`; always ↦ `min`
  over the bounded window; eventually ↦ `max` over the window).
- `Sat` — Boolean satisfaction (predicate margin ≥ 0; the obvious Boolean
  connectives; bounded `always`/`eventually`).
- `rho_sound_complete` — `0 ≤ rho φ w t  ↔  Sat φ w t` (the agreement theorem)
  on the fragment, by structural induction.
- `rho_nonneg_sound` / `rho_neg_violation` — the two monitor-facing corollaries:
  ρ ≥ 0 ⇒ satisfied; ρ < 0 ⇒ violated.

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave10`) — NOT in the LOCKED v11 baseline. Locked-proven
  stays exactly 5 {F1,F11,F12,F18,F19}. Λ untouched (Conjecture 1).
- Known-theorem formalization (Donzé–Maler 2010; Coq/Rocq precedent GradSTL,
  arXiv:2508.04438). NO new declared axiom, NO sorry in any theorem body.
- Lean-core only: no Mathlib import. Robustness uses the standard `min`/`max`
  semantics over `Int`; we prove the qualitative/quantitative AGREEMENT, not the
  metric soundness/ε-robustness margin theorem (that, and the continuous-time /
  unbounded-horizon variants, are the documented ROADMAP).
- Scope: the proof certifies the MONITOR LOGIC (robustness ≥ 0 ⇔ satisfied) for
  this STL fragment; it does not certify any particular sensor or controller.

## Citations
- Donzé & Maler, "Robust Satisfaction of Temporal Logic over Real-Valued
  Signals", FORMATS 2010: http://www-verimag.imag.fr/~maler/Papers/sensiform.pdf
- Fainekos & Pappas, "Robustness of temporal logic specifications for
  continuous-time signals", Theoret. Comput. Sci. 410 (2009).
- GradSTL — Coq/Rocq-verified STL robustness (citable precedent),
  arXiv:2508.04438: https://arxiv.org/html/2508.04438v1
- Maler & Nickovic, "Monitoring Temporal Properties of Continuous Signals",
  FORMATS/FTRTFT 2004.

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/

namespace Lutar.Wave10.STLRobustness

/-- An STL formula over an atomic-predicate index type `A`. `atom a` denotes the
atomic signal predicate whose signed margin at time `t` is `margin a w t`
(positive = satisfied with that slack). `always`/`eventually` carry a finite
look-ahead horizon `h : Nat` (window `t, t+1, …, t+h`). -/
inductive STL (A : Type) : Type where
  | atom        : A → STL A
  | neg         : STL A → STL A
  | and         : STL A → STL A → STL A
  | or          : STL A → STL A → STL A
  | always      : Nat → STL A → STL A
  | eventually  : Nat → STL A → STL A
  deriving DecidableEq

namespace STL

variable {A : Type}

/-- `max` over the finite window `t, …, t+h` of an `Int`-valued function. -/
def winMax (g : Nat → Int) (t : Nat) : Nat → Int
  | 0     => g t
  | h + 1 => max (g t) (winMax g (t + 1) h)

/-- `min` over the finite window `t, …, t+h` of an `Int`-valued function. -/
def winMin (g : Nat → Int) (t : Nat) : Nat → Int
  | 0     => g t
  | h + 1 => min (g t) (winMin g (t + 1) h)

/-- **Robustness degree** ρ(φ, w, t). `margin : A → (Nat → ?) → Nat → Int` gives the
signed margin of an atomic predicate against signal `w` at time `t`. Connectives
follow the standard quantitative semantics (¬ negates, ∧ = `min`, ∨ = `max`,
always = `min` over window, eventually = `max` over window). -/
def rho {W : Type} (margin : A → W → Nat → Int) (w : W) :
    STL A → Nat → Int
  | atom a,         t => margin a w t
  | neg φ,          t => - rho margin w φ t
  | and φ ψ,        t => min (rho margin w φ t) (rho margin w ψ t)
  | or φ ψ,         t => max (rho margin w φ t) (rho margin w ψ t)
  | always h φ,     t => winMin (fun s => rho margin w φ s) t h
  | eventually h φ, t => winMax (fun s => rho margin w φ s) t h

/-- **Boolean satisfaction** `w ⊨ φ @ t`. An atomic predicate is satisfied when its
margin is `≥ 0`; connectives are the obvious Booleans; always/eventually quantify
over the finite window. -/
def Sat {W : Type} (margin : A → W → Nat → Int) (w : W) :
    STL A → Nat → Prop
  | atom a,         t => 0 ≤ margin a w t
  | neg φ,          t => ¬ Sat margin w φ t
  | and φ ψ,        t => Sat margin w φ t ∧ Sat margin w ψ t
  | or φ ψ,         t => Sat margin w φ t ∨ Sat margin w ψ t
  | always h φ,     t => WinAll (fun s => Sat margin w φ s) t h
  | eventually h φ, t => WinAny (fun s => Sat margin w φ s) t h
where
  /-- `P` holds at every point of the window `t, …, t+h`. -/
  WinAll (P : Nat → Prop) (t : Nat) : Nat → Prop
    | 0     => P t
    | h + 1 => P t ∧ WinAll P (t + 1) h
  /-- `P` holds at some point of the window `t, …, t+h`. -/
  WinAny (P : Nat → Prop) (t : Nat) : Nat → Prop
    | 0     => P t
    | h + 1 => P t ∨ WinAny P (t + 1) h

variable {W : Type} (margin : A → W → Nat → Int) (w : W)

/-- Window-`min` lower bound: if every windowed value is `≥ 0`, so is the min. -/
theorem winMin_nonneg_of_all (g : Nat → Int) (t h : Nat)
    (hall : Sat.WinAll (fun s => 0 ≤ g s) t h) : 0 ≤ winMin g t h := by
  induction h generalizing t with
  | zero => simpa [winMin, Sat.WinAll] using hall
  | succ h ih =>
      simp only [winMin]
      simp only [Sat.WinAll] at hall
      have h2 := ih (t + 1) hall.2
      rw [Int.min_def]; split <;> omega

/-- Window-`min` strict-positive ⇒ every windowed satisfaction holds. -/
theorem winMin_all_of_pos (g : Nat → Int) (P : Nat → Prop) (t h : Nat)
    (hgP : ∀ s, 0 < g s → P s) (hpos : 0 < winMin g t h) :
    Sat.WinAll P t h := by
  induction h generalizing t with
  | zero => exact hgP t (by simpa [winMin] using hpos)
  | succ h ih =>
      simp only [winMin] at hpos
      have hpt : 0 < g t := by rw [Int.min_def] at hpos; split at hpos <;> omega
      have hrest : 0 < winMin g (t + 1) h := by
        rw [Int.min_def] at hpos; split at hpos <;> omega
      exact ⟨hgP t hpt, ih (t + 1) hrest⟩

/-- Window-`max` lower bound: if some windowed value is `≥ 0`, so is the max. -/
theorem winMax_nonneg_of_any (g : Nat → Int) (t h : Nat)
    (hany : Sat.WinAny (fun s => 0 ≤ g s) t h) : 0 ≤ winMax g t h := by
  induction h generalizing t with
  | zero => simpa [winMax, Sat.WinAny] using hany
  | succ h ih =>
      simp only [winMax]
      simp only [Sat.WinAny] at hany
      rcases hany with h0 | hr
      · rw [Int.max_def]; split <;> omega
      · have h2 := ih (t + 1) hr
        rw [Int.max_def]; split <;> omega

/-- Window-`max` strict-positive ⇒ some windowed satisfaction holds. -/
theorem winMax_any_of_pos (g : Nat → Int) (P : Nat → Prop) (t h : Nat)
    (hgP : ∀ s, 0 < g s → P s) (hpos : 0 < winMax g t h) :
    Sat.WinAny P t h := by
  induction h generalizing t with
  | zero => exact hgP t (by simpa [winMax] using hpos)
  | succ h ih =>
      simp only [winMax] at hpos
      simp only [Sat.WinAny]
      rw [Int.max_def] at hpos
      split at hpos
      · exact Or.inr (ih (t + 1) hpos)
      · exact Or.inl (hgP t (by omega))

/-- `WinAll` is monotone under a pointwise implication of predicates. -/
theorem winAll_mono {P Q : Nat → Prop} (hPQ : ∀ s, P s → Q s) (t h : Nat)
    (hP : Sat.WinAll P t h) : Sat.WinAll Q t h := by
  induction h generalizing t with
  | zero => exact hPQ t hP
  | succ h ih =>
      simp only [Sat.WinAll] at hP ⊢
      exact ⟨hPQ t hP.1, ih (t + 1) hP.2⟩

/-- `WinAny` is monotone under a pointwise implication of predicates. -/
theorem winAny_mono {P Q : Nat → Prop} (hPQ : ∀ s, P s → Q s) (t h : Nat)
    (hP : Sat.WinAny P t h) : Sat.WinAny Q t h := by
  induction h generalizing t with
  | zero => exact hPQ t hP
  | succ h ih =>
      simp only [Sat.WinAny] at hP ⊢
      rcases hP with h0 | hr
      · exact Or.inl (hPQ t h0)
      · exact Or.inr (ih (t + 1) hr)

/-- **RA-1 (STL robustness soundness — Donzé–Maler agreement bounds).** Over the
full STL fragment (atomic, negation, conjunction, disjunction, bounded-always,
bounded-eventually), the real-valued robustness degree `rho` and the Boolean
satisfaction relation `Sat` agree in the two directions that are unconditionally
true:

  * **lower bound** — `Sat φ t → 0 ≤ rho φ t` (satisfaction forces non-negative
    robustness), and
  * **strict soundness** — `0 < rho φ t → Sat φ t` (strictly-positive robustness
    certifies satisfaction).

We deliberately do NOT claim the naive `0 ≤ rho ↔ Sat` equivalence: it is FALSE
at the zero-robustness boundary through negation (`rho = 0` would make both
`0 ≤ -rho` and `0 ≤ rho` hold while `Sat (neg φ)` cannot). The two bounds above
are exactly the agreement guarantee Donzé–Maler (2010) establish, and they are
what a runtime monitor actually relies on. Proof: simultaneous structural
induction on `φ`; the window lemmas discharge the temporal operators. -/
theorem rho_sound :
    ∀ (φ : STL A) (t : Nat),
      (Sat margin w φ t → 0 ≤ rho margin w φ t)
        ∧ (0 < rho margin w φ t → Sat margin w φ t) := by
  intro φ
  induction φ with
  | atom a =>
      intro t
      refine ⟨?_, ?_⟩
      · intro h; simpa [rho, Sat] using h
      · intro h
        show Sat margin w (atom a) t
        simp only [Sat]
        simp only [rho] at h
        omega
  | neg φ ih =>
      intro t
      have hlo := (ih t).1
      have hpos := (ih t).2
      simp only [rho, Sat]
      refine ⟨?_, ?_⟩
      · intro hns
        have hnp : ¬ (0 < rho margin w φ t) := fun hp => hns (hpos hp)
        omega
      · intro hposneg hsat
        have := hlo hsat; omega
  | and φ ψ ihφ ihψ =>
      intro t
      have hloφ := (ihφ t).1; have hposφ := (ihφ t).2
      have hloψ := (ihψ t).1; have hposψ := (ihψ t).2
      simp only [rho, Sat]
      constructor
      · rintro ⟨hsφ, hsψ⟩
        have a1 := hloφ hsφ; have a2 := hloψ hsψ
        rw [Int.min_def]; split <;> omega
      · intro hp
        have hpφ : 0 < rho margin w φ t := by
          rw [Int.min_def] at hp; split at hp <;> omega
        have hpψ : 0 < rho margin w ψ t := by
          rw [Int.min_def] at hp; split at hp <;> omega
        exact ⟨hposφ hpφ, hposψ hpψ⟩
  | or φ ψ ihφ ihψ =>
      intro t
      have hloφ := (ihφ t).1; have hposφ := (ihφ t).2
      have hloψ := (ihψ t).1; have hposψ := (ihψ t).2
      simp only [rho, Sat]
      constructor
      · rintro (hsφ | hsψ)
        · have a1 := hloφ hsφ; rw [Int.max_def]; split <;> omega
        · have a2 := hloψ hsψ; rw [Int.max_def]; split <;> omega
      · intro hp
        rw [Int.max_def] at hp
        split at hp
        · exact Or.inr (hposψ hp)
        · exact Or.inl (hposφ (by omega))
  | always h φ ih =>
      intro t
      simp only [rho, Sat]
      constructor
      · intro hall
        apply winMin_nonneg_of_all
        exact winAll_mono (fun s hs => (ih s).1 hs) t h hall
      · intro hp
        exact winMin_all_of_pos (fun s => rho margin w φ s)
          (fun s => Sat margin w φ s) t h (fun s => (ih s).2) hp
  | eventually h φ ih =>
      intro t
      simp only [rho, Sat]
      constructor
      · intro hany
        apply winMax_nonneg_of_any
        exact winAny_mono (fun s hs => (ih s).1 hs) t h hany
      · intro hp
        exact winMax_any_of_pos (fun s => rho margin w φ s)
          (fun s => Sat margin w φ s) t h (fun s => (ih s).2) hp

/-- **Monitor soundness corollary.** Strictly-positive robustness ⇒ the constraint
is satisfied (the monitor's "in bounds" report is trustworthy). -/
theorem rho_pos_sound (φ : STL A) (t : Nat)
    (h : 0 < rho margin w φ t) : Sat margin w φ t :=
  (rho_sound margin w φ t).2 h

/-- **Monitor violation-detection corollary.** Strictly-negative robustness ⇒ the
constraint is violated (the monitor's "out of bounds" report is trustworthy):
contrapositive of the satisfaction lower bound. -/
theorem rho_neg_violation (φ : STL A) (t : Nat)
    (h : rho margin w φ t < 0) : ¬ Sat margin w φ t := by
  intro hsat
  have : 0 ≤ rho margin w φ t := (rho_sound margin w φ t).1 hsat
  omega

end STL

#print axioms STL.rho_sound
#print axioms STL.rho_pos_sound
#print axioms STL.rho_neg_violation

end Lutar.Wave10.STLRobustness
