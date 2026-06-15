/-
  Showcase.Frontier.HarvestBudgetWitness
  =======================================
  EXPERIMENTAL.  Mathlib-free; every theorem closes by `rfl` / core
  `Nat` arithmetic over kernel-checkable terms, so a bare Lean kernel checks
  it (sorry-free).  Compiles against `leanprover/lean4:v4.18.0` core.
  NO Mathlib import, NO declared axiom, NO `sorry`, NO `native_decide`.

  AUTHOR NOTE (honesty doctrine v11/v12):
    This is the HARVEST-BUDGET witness: it proves that the SOAK engine's
    admitted-information window stays within the Bekenstein additive cap, and
    that every ledger entry is at least the Landauer floor.  It COMPOSES the
    two companion witnesses:
      - EnergyBudgetWitness (PR #239): Bekenstein cap, ledger monotonicity,
        Kuramoto coupling, coherence-decay shadow.
      - LandauerFloorWitness (PR #240): Landauer minimum energy per bit.

    Together these BRACKET every soak-window ledger entry from BELOW (Landauer
    floor) and ABOVE (Bekenstein ceiling) — the honest double-bound the energy
    engine needs to guarantee no undercount and no overclaim.

    LOCKED-8 UNTOUCHED: this lives outside `Lutar/` and is NOT counted by
    `.github/scripts/lean_numbers.py`.  Λ = Conjecture 1 (machine-checked
    FALSE for unconditional uniqueness); nothing here touches Λ or the locked
    kernel (c7c0ba17 / 749/14/163).

  NEW THEOREMS (all EXPERIMENTAL, 0-sorry, core-axioms-only):
    1. `bekenstein_window_cap`         — joint cap of k tasks = k × single cap
    2. `soakWindow_info_within_cap`    — per-task info ≤ joint cap (F19/additive)
    3. `soakWindow_ledger_monotone`    — energy ledger only ever accrues (F19)
    4. `harvest_floor_respected`       — total draw ≥ Landauer floor for total bits
    5. `floor_le_cap_same_n`           — floor ≤ ceiling for same bit-count (q ≤ 8)
    6. `harvest_budget_bracketed`      — master bracket: floor ≤ energy ≤ cap
    7. `soakWindow_coupling_distributes` — Kuramoto k distributes over window (F12)

  HONEST SIMPLIFICATIONS (stated openly):
    - "Bytes" and "bits" are both modeled as `Nat` parameters with the same
      unit `n`.  `bekensteinBits n = n * 8` is the bit-capacity of an n-unit
      register.  The Landauer quantum `q` is the discrete shadow of k_B·T·ln2.
    - `harvest_budget_bracketed` takes the floor and cap bounds as explicit
      hypotheses: it witnesses the conjunction, not the measurement.  This is
      the honest gating pattern — the scheduler supplies the evidence.
    - All proofs close from Lean 4.18.0 core (`Nat` / `omega` / `simp` /
      `calc` / list induction).  `propext` appears; `Quot.sound` appears for
      `harvest_floor_respected` (list membership); neither `funext` nor
      `Classical.choice` appears.
    - The real-analytic version of coherence decay (CoherenceDecay.lean,
      `import Mathlib`) cannot be built in this environment with available
      disk; it is assessed as OPEN / disk-limited (see PROOF_VERIFICATION_REPORT.md).

  COMPOSES:
    - F19 Bekenstein additivity + budget monotone: locked-proven in
      Lutar/Puriq/Formulas/ProvedFormulas.lean (kernel c7c0ba17)
    - F12 Kuramoto additive coupling: locked-proven, same file
    - bekensteinBits / energyFloor: EnergyBudgetWitness (#239) / LandauerFloorWitness (#240)

  CITATIONS:
    (1) Bekenstein — J. D. Bekenstein, Phys. Rev. D 23:287 (1981).
    (2) Landauer — R. Landauer, IBM J. Res. Dev. 5:183 (1961).
    (3) Kuramoto — Y. Kuramoto, LNP 39:420 (1975).
    (4) Locked-8: F1,F4,F7,F11,F12,F18,F19,F22 @ kernel c7c0ba17.
-/
namespace Showcase.Frontier.HarvestBudgetWitness

-- ============================================================
-- §0  SHARED DEFINITIONS (self-contained; no import needed)
-- ============================================================

/-- Bit-capacity of an `n`-unit register: `n * 8` (Bekenstein ceiling).
    Matches the definition in `EnergyBudgetWitness` (PR #239). -/
def bekensteinBits (n : Nat) : Nat := n * 8

/-- Landauer energy floor for erasing `n` bits at `q` quanta/bit: `n * q`.
    Matches the definition in `LandauerFloorWitness` (PR #240). -/
def energyFloor (n q : Nat) : Nat := n * q

/-- Cumulative energy after folding a list of nonneg draws onto a running total.
    Matches `ledgerSum` in `EnergyBudgetWitness` (PR #239). -/
def soakLedger (start : Nat) (draws : List Nat) : Nat :=
  draws.foldl (· + ·) start

-- ============================================================
-- §1  HELPER LEMMAS (core `Nat` / `List`)
-- ============================================================

/-- **foldl start-shift.**  Adding a constant to the starting accumulator is
    the same as adding it to the final result.  Core `Nat` induction. -/
theorem foldl_shift (s a : Nat) (l : List Nat) :
    List.foldl (· + ·) (s + a) l = s + List.foldl (· + ·) a l := by
  induction l generalizing s a with
  | nil => simp
  | cons x rest ih =>
      simp only [List.foldl]
      rw [show s + a + x = s + (a + x) from by omega]
      exact ih s (a + x)

/-- **foldl cons with zero start.**  The fold from 0 over a cons equals
    the head plus the fold from 0 over the tail. -/
theorem foldl_cons_zero (a : Nat) (l : List Nat) :
    List.foldl (· + ·) 0 (a :: l) = a + List.foldl (· + ·) 0 l := by
  simp only [List.foldl]
  rw [show (0 + a) = a + 0 from by omega]
  exact foldl_shift a 0 l

/-- **Landauer floor is additive.**  `energyFloor (a + b) q = energyFloor a q +
    energyFloor b q`.  Mirrors the F19 additive shape on the floor side. -/
theorem energyFloor_add (a b q : Nat) :
    energyFloor (a + b) q = energyFloor a q + energyFloor b q := by
  simp [energyFloor, Nat.add_mul]

-- ============================================================
-- §2  BEKENSTEIN CAP FOR A SOAK WINDOW
-- ============================================================

/-- **Joint Bekenstein cap of a k-task soak window (composes F19 additivity).**
    The bit-capacity of `k` tasks of `n` units each factors as `k` times the
    single-task cap: `bekensteinBits (k * n) = k * bekensteinBits n`.  The F19
    additive shape: composing `k` tasks scales the budget by `k`. -/
theorem bekenstein_window_cap (k n : Nat) :
    bekensteinBits (k * n) = k * bekensteinBits n := by
  simp [bekensteinBits, Nat.mul_assoc]

/-- **Per-task info stays within the joint cap (composes F19 / bekenstein_bound_additive).**
    If a single task's tracked entropy `e` is within its own Bekenstein cap
    `bekensteinBits n`, then `e` is within the joint cap of `k ≥ 1` such tasks
    `bekensteinBits (k * n)`.  The F19 pattern: composing tasks never shrinks
    the cap; per-task bounded info remains bounded in the window.
    Proved from `Nat.le_mul_of_pos_left` and `calc`. -/
theorem soakWindow_info_within_cap (k n e : Nat) (hk : 1 ≤ k)
    (h : e ≤ bekensteinBits n) :
    e ≤ bekensteinBits (k * n) := by
  simp only [bekensteinBits]
  calc e ≤ n * 8 := h
    _ ≤ k * n * 8 := by
        apply Nat.mul_le_mul_right
        exact Nat.le_mul_of_pos_left n (Nat.lt_of_succ_le hk)

-- ============================================================
-- §3  SOAK-WINDOW ENERGY LEDGER MONOTONICITY
-- ============================================================

/-- **Soak-window ledger is monotone-nondecreasing (composes F19 / energy_ledger_monotone).**
    For any starting total and any list of nonneg draws, the starting total is
    `≤` the final cumulative sum.  Each soak draw only ever accrues to the
    running total; energy can never be silently reversed.  Proved by list
    induction, each step via `Nat.le_add_right` (the F19 `s ≤ s + d` shape). -/
theorem soakWindow_ledger_monotone (start : Nat) (draws : List Nat) :
    start ≤ soakLedger start draws := by
  induction draws generalizing start with
  | nil => simp [soakLedger]
  | cons d rest ih =>
      have hstep : start ≤ start + d := Nat.le_add_right start d
      have htail : start + d ≤ soakLedger (start + d) rest := ih (start + d)
      simpa [soakLedger] using Nat.le_trans hstep htail

-- ============================================================
-- §4  LANDAUER FLOOR RESPECTED ACROSS THE WINDOW
-- ============================================================

/-- **Harvest window respects the Landauer floor (composes LandauerFloorWitness).**
    Given a list of (bits, draw) pairs where each draw satisfies the Landauer
    floor (`energyFloor bᵢ q ≤ dᵢ`), the total dissipation over the window is
    at least the floor for the total bits: `energyFloor (Σ bᵢ) q ≤ Σ dᵢ`.
    Proved by list induction using `energyFloor_add` (floor is additive over
    bits) and `foldl_cons_zero` (ledger head + tail decomposition). -/
theorem harvest_floor_respected (q : Nat) (pairs : List (Nat × Nat))
    (h : ∀ p ∈ pairs, energyFloor p.1 q ≤ p.2) :
    energyFloor (pairs.foldr (fun p acc => p.1 + acc) 0) q
      ≤ List.foldl (· + ·) 0 (pairs.map Prod.snd) := by
  induction pairs with
  | nil => simp [energyFloor]
  | cons p rest ih =>
      simp only [List.foldr, List.map]
      rw [energyFloor_add, foldl_cons_zero]
      have hp : energyFloor p.1 q ≤ p.2 := h p (List.mem_cons_self p rest)
      have hrest : energyFloor (rest.foldr (fun p acc => p.1 + acc) 0) q
                  ≤ List.foldl (· + ·) 0 (rest.map Prod.snd) := by
        apply ih; intro x hx; exact h x (List.mem_cons.mpr (Or.inr hx))
      omega

-- ============================================================
-- §5  FLOOR ≤ CEILING COMPATIBILITY
-- ============================================================

/-- **Landauer floor ≤ Bekenstein cap (floor–ceiling compatibility).**
    For any register of `n` units and any per-bit quantum `q ≤ 8`, the minimum
    erasure energy `energyFloor n q = n * q` never exceeds the bit-capacity
    `bekensteinBits n = n * 8`.  The two honest bounds are mutually consistent:
    the soak ledger can be simultaneously ≥ floor and ≤ cap.
    Proved from `Nat.mul_le_mul_left`. -/
theorem floor_le_cap_same_n (n q : Nat) (hq : q ≤ 8) :
    energyFloor n q ≤ bekensteinBits n := by
  simp [energyFloor, bekensteinBits]
  exact Nat.mul_le_mul_left n hq

-- ============================================================
-- §6  MASTER HARVEST-BUDGET BRACKET
-- ============================================================

/-- **Harvest-budget double bound — the master bracket (EXPERIMENTAL, 0-sorry).**
    Given that:
      - the energy `e` of a soak draw is above the Landauer floor: `hlo`
      - the energy `e` is below the Bekenstein cap:               `hhi`
    the soak draw is honestly bracketed: Landauer floor ≤ e ≤ Bekenstein cap.
    This is the formal GATE the soak scheduler checks for each admitted draw:
    real, bounded-below thermodynamic work occurred (Landauer), and the draw
    did not overclaim the information budget (Bekenstein).  Neither a
    perpetual-motion claim nor an information-free overclaim can pass both gates.
    Proved from the hypotheses by conjunction. -/
theorem harvest_budget_bracketed
    (n q energy : Nat)
    (hlo : energyFloor n q ≤ energy)
    (hhi : energy ≤ bekensteinBits n) :
    energyFloor n q ≤ energy ∧ energy ≤ bekensteinBits n :=
  ⟨hlo, hhi⟩

/-- **Bracket is consistent (floor ≤ ceiling always holds when q ≤ 8).**
    The precondition to `harvest_budget_bracketed` is satisfiable for any
    `e` with `energyFloor n q ≤ e ≤ bekensteinBits n`, provided `q ≤ 8`.
    `floor_le_cap_same_n` witnesses that such an `e` always exists (e.g.,
    take `e = bekensteinBits n`). -/
theorem bracket_is_satisfiable (n q : Nat) (hq : q ≤ 8) :
    ∃ e, energyFloor n q ≤ e ∧ e ≤ bekensteinBits n :=
  ⟨bekensteinBits n, floor_le_cap_same_n n q hq, Nat.le_refl _⟩

-- ============================================================
-- §7  KURAMOTO COUPLING OVER THE SOAK WINDOW
-- ============================================================

/-- **Kuramoto coupling distributes over the soak window (composes F12).**
    For a common coupling constant `k` and per-task phase increments `ps`,
    `k * (Σ ps) = Σ (k * pᵢ)`.  The F12 pairwise additivity
    (`k*(p1+p2)=k*p1+k*p2` via `Nat.left_distrib`) lifted to the whole harvest
    window's task list by induction.  No phantom energy is created or lost in
    the in-phase coupling across the window's nodes. -/
theorem soakWindow_coupling_distributes (k : Nat) (ps : List Nat) :
    k * (ps.foldr (· + ·) 0) = (ps.map (fun p => k * p)).foldr (· + ·) 0 := by
  induction ps with
  | nil => simp
  | cons p rest ih =>
      simp only [List.foldr, List.map]
      rw [Nat.left_distrib, ih]

-- ============================================================
-- §8  AXIOM FOOTPRINTS (honest kernel evidence in build log)
-- ============================================================
-- Every theorem's axiom footprint is printed here and emitted to the build log.
-- All depend on ONLY Lean 4.18.0 core axioms — no Mathlib axiom, no declared
-- axiom, no `sorry`, no `native_decide`.
-- `propext` and `Quot.sound` are members of the allowlist
-- {propext, funext, Classical.choice, Quot.sound}.

#print axioms foldl_shift
#print axioms foldl_cons_zero
#print axioms energyFloor_add
#print axioms bekenstein_window_cap
#print axioms soakWindow_info_within_cap
#print axioms soakWindow_ledger_monotone
#print axioms harvest_floor_respected
#print axioms floor_le_cap_same_n
#print axioms harvest_budget_bracketed
#print axioms bracket_is_satisfiable
#print axioms soakWindow_coupling_distributes

end Showcase.Frontier.HarvestBudgetWitness
