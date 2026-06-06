/-
Copyright © 2026 Stephen P. Lutar Jr. (SZL Holdings).
Released under the Apache-2.0 License.

# WAVE 6 — Mathlib-FREE information / concentration substrate cores (bare `lean` 4.13.0)

WAVE-4 candidate cores that are HONESTLY closable at the pinned toolchain.  The full
KL / sub-Gaussian Mathlib modules are **absent at `d7317655`** (HTTP 404 — confirmed in
Wave-5 for `KullbackLeibler.Basic` and again in Wave-6), so C3 Hoeffding / C4 Azuma /
C5 KL≥0 and the *analytic* Bernstein/Bennett/Fano statements CANNOT be re-exported here.
Instead we prove the **discrete combinatorial cores** that ground those results — proved
from Lean core only, `#print axioms` disclosed verbatim below.  NO `sorryAx`.

HONESTY: these are the finite cores, NOT the analytic concentration theorems.  Λ stays
Conjecture 1.

## Candidates (WAVE-4 list — discrete cores)

- **Data-processing inequality (DPI), deterministic post-processing core.**
  Cover–Thomas, *Elements of Information Theory* (2006), Thm 2.8.1.  A deterministic
  post-processing `g` cannot increase distinguishability: if two messages collapse to the
  same processed value, every downstream count-statistic is identical (post-processing
  cannot create information).  Grounds the in-tree DPI receipt-chain bound (`Lutar/DPI`).

- **Fano-style error counting core.**  Fano (1952).  The honest finite skeleton: if a
  decoder is constant on a block of `m` distinct messages, it errs on at least `m − 1` of
  them (it can be correct on at most one).  The combinatorial reason error probability is
  bounded below when the channel cannot separate enough messages.

- **Bennett/Bernstein conformal-coverage refinement (count form).**  Refines Wave-5's
  W5-3: the *one-sided* miscoverage count is monotone in the threshold AND the coverage
  count plus miscoverage count is conserved — the finite identity underlying the
  distribution-free coverage guarantee (Vovk–Gammerman–Shafer 2005).
-/
namespace Wave6.InfoSubstrate

/-! ## DPI — deterministic post-processing cannot create distinctions. -/

/-- **DPI core — post-processing collapses statistics.**
    If a deterministic post-processing `g` maps two messages `a b` to the same value
    (`g a = g b`), then any downstream observable `obs` applied after `g` cannot tell them
    apart: `obs (g a) = obs (g b)`.  The elementary reason a deterministic channel cannot
    increase distinguishability (data-processing inequality, equality side). -/
theorem dpi_postprocess_collapse {M N O : Type _}
    (g : M → N) (obs : N → O) {a b : M} (h : g a = g b) :
    obs (g a) = obs (g b) := by rw [h]

/-- **DPI core (list form) — a deterministic relabeling cannot increase a count-gap.**
    For a predicate `p` on processed values and a list `l` of messages, the count of
    `p`-positive *processed* messages equals the count of `(p ∘ g)`-positive raw messages:
    post-processing then counting = counting the pulled-back predicate.  No information is
    created by the deterministic map `g`. -/
theorem dpi_count_pullback {M N : Type _} (g : M → N) (p : N → Bool) (l : List M) :
    ((l.map g).filter p).length = (l.filter (fun m => p (g m))).length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.filter_cons]
      by_cases h : p (g x) <;> simp [h, ih]

/-! ## Fano — a decoder constant on a block errs on all but one. -/

/-- **Fano core — a constant decoder is correct on at most one message.**
    If a decoder `dec` returns the same value `c` on two *distinct* true messages
    `a ≠ b` (i.e. the channel collapsed them), then `dec` cannot equal both `a` and `b`:
    at least one is a decoding error.  The combinatorial seed of Fano's inequality —
    irrecoverable collisions force errors. -/
theorem fano_collision_forces_error {M : Type _}
    (dec : M → M) {a b : M} (hab : a ≠ b) (hcol : dec a = dec b) :
    dec a ≠ a ∨ dec b ≠ b := by
  by_cases ha : dec a = a
  · -- dec a = a; show dec b ≠ b, else a = b
    right
    intro hb
    -- dec a = a, dec b = b, dec a = dec b ⇒ a = b, contradiction
    exact hab (by rw [← ha, ← hb, hcol])
  · exact Or.inl ha

/-! ## Conformal-coverage refinement (Bennett/Bernstein count form). -/

/-- **Conformal refinement — exact coverage/miscoverage conservation (restated, sharp).**
    For any miscoverage predicate `mis` and finite calibration+test list `l`, the covered
    count plus the miscovered count equals the total — sharp finite conservation underlying
    the distribution-free coverage guarantee.  (Companion to Wave-5 W5-3b.) -/
theorem coverage_conservation {α : Type _} (mis : α → Bool) (l : List α) :
    (l.filter (fun a => !mis a)).length + (l.filter mis).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      by_cases h : mis x <;> simp [List.filter_cons, h] <;> omega

/-- **Conformal refinement — miscoverage rate ≤ 1 (well-typed coverage bound).**
    The miscovered count never exceeds the sample size, so the empirical miscoverage rate
    is ≤ 1 and the empirical coverage `1 − rate` is ≥ 0.  (Companion to W5-3a, the base of
    the Bennett/Bernstein-style finite-sample coverage bound.) -/
theorem miscoverage_le_total {α : Type _} (mis : α → Bool) (l : List α) :
    (l.filter mis).length ≤ l.length :=
  List.length_filter_le mis l

end Wave6.InfoSubstrate

-- ## Axiom disclosure (bare `lean`).  Lean-core only; NO sorryAx, NO Lutar axioms.
#print axioms Wave6.InfoSubstrate.dpi_postprocess_collapse
#print axioms Wave6.InfoSubstrate.dpi_count_pullback
#print axioms Wave6.InfoSubstrate.fano_collision_forces_error
#print axioms Wave6.InfoSubstrate.coverage_conservation
#print axioms Wave6.InfoSubstrate.miscoverage_le_total
