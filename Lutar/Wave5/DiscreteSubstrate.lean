/-
# WAVE 5 — Mathlib-FREE discrete substrate guarantees (bare `lean` 4.13.0 verified)

These are elementary, kernel-checkable facts that ground product guarantees in the
a11oy / killinchu / UDS substrate. Each is the DISCRETE/combinatorial core of a
published result, proved from Lean core only (no Mathlib, no `Real`, no `Finset`) so it
compiles under bare `lean` and its `#print axioms` is verbatim-disclosable.

HONESTY: nothing here proves Λ uniqueness (still Conjecture 1). These are honest,
load-bearing finite lemmas, not analytic limit theorems. Each `#print axioms` (below)
shows only Lean-core dependencies (`propext`, `Quot.sound`, `Classical.choice`) — NO
`sorryAx`, NO declared Lutar axioms.

## Citations
- W5-3 conformal coverage counting core: Vovk, Gammerman, Shafer (2005),
  *Algorithmic Learning in a Random World*; Lei et al. (2018), JASA 113:1094.
  Split-conformal marginal coverage reduces, given exchangeability, to a finite
  count law: coverage + miscoverage = sample size (W5-3b), with miscoverage ≤ size (W5-3a).
- W5-4 UDS receipt-collision: Dirichlet (1834) pigeonhole. A duplicate in the hashed
  image of a duplicate-free receipt-id list is exactly a hash collision (W5-4).
- W5-5 monotone fair-game (optional-stopping discrete core): Doob (1953),
  *Stochastic Processes*. A bounded stopping time on a non-decreasing running aggregate
  cannot deflate the value below the start (anti-gaming / no early-stop deflation).
-/
namespace Wave5.DiscreteSubstrate

/-! ## W5-3 — Conformal-coverage counting core (killinchu distribution-free trust intervals). -/

/-- **W5-3a — miscoverage is bounded by sample size.** For any nonconformity predicate
    `hi` ("score strictly above the conformal cutoff") and any finite list of
    calibration+test scores `l`, the number of miscovered points is ≤ `l.length`.
    The well-typed base of the coverage *rate* `miscover/length ≤ 1`. -/
theorem w5_3a_miscover_le_total {α : Type _} (hi : α → Bool) (l : List α) :
    (l.filter hi).length ≤ l.length :=
  List.length_filter_le hi l

/-- **W5-3b — covered + miscovered = total (exact partition).** `count(¬hi) + count(hi)
    = length`. The conservation law that turns a miscoverage bound into a coverage
    guarantee (coverage = 1 − miscoverage on the finite sample). -/
theorem w5_3b_cover_miscover_partition {α : Type _} (hi : α → Bool) (l : List α) :
    (l.filter (fun a => !hi a)).length + (l.filter hi).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : hi x <;> simp [List.filter_cons, h] <;> omega

/-- **W5-3c — threshold monotonicity of selection count.** If predicate `p` implies `q`
    (a STRICTER trust criterion `p` than `q`), then the number of items passing `p` is ≤
    the number passing `q`. The a11oy guarantee that tightening a trust threshold never
    admits MORE items — monotone selectivity of the conformal/threshold filter. -/
theorem w5_3c_threshold_count_mono {α : Type _} (p q : α → Bool) (l : List α)
    (h : ∀ a, p a = true → q a = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    by_cases hp : p x = true
    · have hq : q x = true := h x hp
      simp [List.filter_cons, hp, hq]; omega
    · simp only [List.filter_cons]
      by_cases hq : q x = true <;> simp [hp, hq] <;> omega

/-! ## W5-4 — UDS receipt-collision pigeonhole (supply-chain integrity core). -/

/-- **W5-4 — collision from an image duplicate.** If a receipt-id list `l` has NO
    duplicate ids (`l.Nodup`) but its hashed image `l.map h` DOES contain a duplicate
    (`¬ (l.map h).Nodup`), then two distinct ids collided under `h`. The qualitative UDS
    forgery-detection invariant, proved by induction from Lean core. -/
theorem w5_4_collision_of_image_dup {α β : Type _} (h : α → β) :
    ∀ (l : List α), l.Nodup → ¬ (l.map h).Nodup →
      ∃ a ∈ l, ∃ b ∈ l, a ≠ b ∧ h a = h b := by
  intro l
  induction l with
  | nil => intro _ hbad; simp at hbad
  | cons x xs ih =>
    intro hnd hmap
    rw [List.map_cons, List.nodup_cons] at hmap
    rw [List.nodup_cons] at hnd
    by_cases hx : h x ∈ xs.map h
    · rw [List.mem_map] at hx
      obtain ⟨b, hb, hfb⟩ := hx
      refine ⟨x, List.mem_cons_self x xs, b, List.mem_cons_of_mem x hb, ?_, hfb.symm⟩
      intro hxb; exact hnd.1 (hxb ▸ hb)
    · have hnn : ¬ (xs.map h).Nodup := fun hn => hmap ⟨hx, hn⟩
      obtain ⟨a, ha, b, hb, hab, hfab⟩ := ih hnd.2 hnn
      exact ⟨a, List.mem_cons_of_mem x ha, b, List.mem_cons_of_mem x hb, hab, hfab⟩

/-! ## W5-5 — Discrete fair-game / optional-stopping core (UDS receipt-stream anti-gaming). -/

/-- **W5-5 — no early-stop deflation (monotone optional-stopping core).** If a running
    trust aggregate `g : Nat → Nat` is NON-DECREASING in time (the discrete
    submartingale-direction hypothesis `hg`), then for ANY bounded stopping time `τ`,
    the stopped value is at least the opening value: `g 0 ≤ g τ`. No audit can stop
    early to report a value below the start — the anti-deflation guarantee. -/
theorem w5_5_no_early_stop_deflation (g : Nat → Nat)
    (hg : ∀ i j, i ≤ j → g i ≤ g j) (τ : Nat) :
    g 0 ≤ g τ :=
  hg 0 τ (Nat.zero_le τ)

end Wave5.DiscreteSubstrate

-- ## Axiom disclosure (bare `lean` prints these verbatim; captured in §3 of the report).
#print axioms Wave5.DiscreteSubstrate.w5_3a_miscover_le_total
#print axioms Wave5.DiscreteSubstrate.w5_3b_cover_miscover_partition
#print axioms Wave5.DiscreteSubstrate.w5_3c_threshold_count_mono
#print axioms Wave5.DiscreteSubstrate.w5_4_collision_of_image_dup
#print axioms Wave5.DiscreteSubstrate.w5_5_no_early_stop_deflation
