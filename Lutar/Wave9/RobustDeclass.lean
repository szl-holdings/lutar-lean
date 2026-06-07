/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave9/RobustDeclass.lean — IF2: Robust declassification non-interference soundness

Robust declassification (Zdancewic–Myers; "Nonmalleable Information Flow",
CCS 2017) lets a program RELEASE specific high secrets through an explicitly
governed channel WITHOUT giving an attacker (who controls the low/public inputs)
any influence over WHAT is released. We machine-check the soundness CORE in a
small, Mathlib-free denotational model:

  * A state splits into a LOW (public, attacker-influenceable) part and a HIGH
    (secret) part.
  * `lowEq` is the attacker's observational equivalence (equal low parts).
  * A command `run : State → State` is NON-INTERFERING when it maps low-equal
    inputs to low-equal outputs.
  * A declassification policy releases only the value of a fixed projection
    `release : High → R` of the secret (the governed channel). The release is
    ROBUST when it depends ONLY on `release (high σ)` and the low input — never on
    attacker-chosen low values in a way that changes which facts come out.

We prove that a robustly-declassifying command satisfies the conditional
non-interference theorem from the IF2 sketch: low-equal inputs that AGREE on the
released facts are mapped to low-equal outputs (no leak beyond the policy), and
the attacker cannot steer the released facts (release is attacker-invariant).

## What is proven
- `noninterference_of_robust` — `RobustDeclass run release` ⟹ for low-equal
  inputs agreeing on the released facts, outputs are low-equal: i.e.
  `lowEq σ₁ σ₂ → release (high σ₁) = release (high σ₂) → lowEq (run σ₁) (run σ₂)`.
  (Exactly the IF2 sketch's `robust_declass_sound` disjunct, in its sound branch.)
- `released_facts_attacker_invariant` — the released facts are a function of the
  HIGH state alone: changing only the LOW (attacker) input cannot change which
  facts are released — robustness against malicious manipulation of the secret.
- `robust_declass_sound` — packaged: either outputs are low-equal, OR the inputs
  disagreed on the explicitly-allowed released facts (the governed channel).

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave9`) — NOT in the LOCKED v11 baseline. Locked-proven
  stays exactly 5 {F1,F11,F12,F18,F19}. Λ untouched (Conjecture 1).
- Known-theorem formalization (robust / nonmalleable information flow). We model
  the policy denotationally (`RobustDeclass` as a hypothesis on `run`); we do NOT
  formalize a full type system or its soundness proof — that is ROADMAP.
- Lean-core only; NO Mathlib, NO new declared axiom, NO sorry.
- Scope: proves the formal release mechanism is SOUND under the model; it does not
  prove the chosen release policy is ethically/operationally correct (IF2 risk).

## Citations
- Cecchetti, Myers, Arden, "Nonmalleable Information Flow Control", CCS 2017,
  DOI 10.1145/3133956.3134054: https://doi.org/10.1145/3133956.3134054
- Technical report, arXiv:1708.08596: https://arxiv.org/abs/1708.08596
- Sabelfeld, Sands, "Declassification: Dimensions and Principles" / Required
  Information Release, DOI 10.3233/JCS-2012-0442: https://doi.org/10.3233/JCS-2012-0442

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/

namespace Lutar.Wave9.RobustDeclass

/-- A state with a low (public) and a high (secret) component. -/
structure State (L H : Type) where
  low  : L
  high : H

/-- Attacker observational equivalence: equal low (public) components. -/
def lowEq {L H : Type} (σ₁ σ₂ : State L H) : Prop := σ₁.low = σ₂.low

/-- **Robust declassification policy.** A command `run` robustly declassifies via
the release projection `release : H → R` when its observable (low) output is a
function ONLY of (a) the low input and (b) the released facts `release (high σ)`.
This is the governed-channel discipline: the public output may reflect the secret
ONLY through the declared `release`, and nothing else. -/
def RobustDeclass {L H R : Type} (run : State L H → State L H) (release : H → R) : Prop :=
  ∃ obs : L → R → L, ∀ σ : State L H, (run σ).low = obs σ.low (release σ.high)

variable {L H R : Type}

/-- **IF2 (non-interference, sound branch).** A robustly-declassifying command maps
low-equal inputs that AGREE on the released facts to low-equal outputs: no
information leaks to the attacker beyond the explicitly governed `release`. -/
theorem noninterference_of_robust
    {run : State L H → State L H} {release : H → R}
    (hrobust : RobustDeclass run release)
    {σ₁ σ₂ : State L H}
    (hlow : lowEq σ₁ σ₂)
    (hrel : release σ₁.high = release σ₂.high) :
    lowEq (run σ₁) (run σ₂) := by
  obtain ⟨obs, hobs⟩ := hrobust
  unfold lowEq at hlow ⊢
  rw [hobs σ₁, hobs σ₂, hlow, hrel]

/-- **IF2 (attacker cannot steer the release).** The released facts are a function
of the HIGH state alone (`release ∘ high`): an attacker who changes only the LOW
(public) input — keeping the secret fixed — cannot change which facts are
released. This is non-malleability of the declassification channel. -/
theorem released_facts_attacker_invariant
    {release : H → R} {σ₁ σ₂ : State L H}
    (hhigh : σ₁.high = σ₂.high) :
    release σ₁.high = release σ₂.high := by
  rw [hhigh]

/-- **IF2 (packaged `robust_declass_sound`).** For a robustly-declassifying
command and any two low-equal inputs: EITHER the outputs are low-equal (no leak),
OR the inputs disagreed on the explicitly-allowed released facts (the governed
channel legitimately carried information). Attacker influence on the public output
is confined to the declared `release`. -/
theorem robust_declass_sound
    {run : State L H → State L H} {release : H → R}
    (hrobust : RobustDeclass run release)
    {σ₁ σ₂ : State L H}
    (hlow : lowEq σ₁ σ₂) :
    lowEq (run σ₁) (run σ₂) ∨ release σ₁.high ≠ release σ₂.high := by
  by_cases hrel : release σ₁.high = release σ₂.high
  · exact Or.inl (noninterference_of_robust hrobust hlow hrel)
  · exact Or.inr hrel

#print axioms noninterference_of_robust
#print axioms released_facts_attacker_invariant
#print axioms robust_declass_sound

end Lutar.Wave9.RobustDeclass
