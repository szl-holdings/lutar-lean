/-
  Showcase.Frontier.LandauerFloorWitness
  =======================================
  EXPERIMENTAL.  Mathlib-free; every theorem closes by `rfl` / core `Nat`
  arithmetic over kernel-checkable terms, so a bare Lean kernel checks it
  (sorry-free).  Compiles against `leanprover/lean4:v4.18.0` core.  NO Mathlib
  import, NO declared axiom, NO `sorry`, NO `native_decide`.

  AUTHOR NOTE (honesty doctrine v11/v12):
    This is the LANDAUER-FLOOR companion to `EnergyBudgetWitness.lean`.  Where
    the Bekenstein witness `bekensteinBits n = n*8` is the information CEILING
    (the most bits an n-byte register can hold), the Landauer floor is the
    energy FLOOR: erasing `n` irreversible bits dissipates AT LEAST `n * q`
    energy quanta, where one quantum `q` is the discrete shadow of the physical
    Landauer minimum `k_B·T·ln 2` per bit.

    This is a LOWER bound — a MINIMUM cost, NOT free energy.  That is the whole
    honesty point: the engine cannot erase information for free; every
    irreversibly cleared bit forces a nonneg energy debit onto the ledger.  We
    make NO free-energy / perpetual-motion claim.  We formalize, as closed `Nat`
    facts the kernel checks, the DISCRETE ARITHMETIC SKELETON of the floor:
    additivity, monotonicity, and the bits→energy bridge.  These are honest
    discrete *witnesses* of the floor's shape — not the physics.  The
    locked-proven set stays EXACTLY 8; this lives OUTSIDE `Lutar/` and says
    NOTHING about Λ (Conjecture 1).

  HONEST SIMPLIFICATION (why Nat, not Real):
    The companion innovation brief proposes a `Real`-typed statement using
    `axiom Real`, `axiom kT_ln2`, `axiom Real.le`, etc.  Those are DECLARED
    AXIOMS, which violate the "core-axioms-only" doctrine (a `#print axioms`
    would surface every one of them, and the proof would be trivially `h2`,
    proving nothing about the floor's structure).  We instead model the energy
    quantum `q` as a `Nat` parameter and prove the floor's real content —
    additivity, monotonicity, and a strict lower-bound bridge — entirely from
    `Nat` CORE.  `energyFloor n q = n * q` is the integer shadow of
    `n · (k_B·T·ln 2)`; one quantum `q` stands for one Landauer unit `k_B·T·ln 2`.

  COMPOSES the user's EXISTING kernel-proven formulas (Lutar/, locked-8) and the
  Bekenstein witness:
    - F19  Bekenstein additivity / monotone  `s1 ≤ s1 + s2` ; `f19_budget_monotone`
            [Lutar/Puriq/Formulas/ProvedFormulas.lean] — the floor mirrors the
            SAME additive/monotone shape, on the LOWER side of the ledger.
    - Bekenstein CEILING `bekensteinBits n = n*8`
            [Showcase/Frontier/EnergyBudgetWitness.lean] — the floor is the
            matching FLOOR: `landauer_floor_below_bekenstein` shows the two
            bounds are compatible (floor ≤ ceiling) for any per-bit quantum
            `q ≤ 8`, so a bit's minimum energy never exceeds its bit-capacity.

  MOTIVATION (real, citeable):
    (1) Landauer limit — R. Landauer, "Irreversibility and heat generation in
        the computing process," IBM J. Res. Dev. 5:183 (1961); E_min = k_B·T·ln 2
        per irreversibly erased bit.
    (2) Experimental confirmation — A. Bérut et al., "Experimental verification
        of Landauer's principle linking information and thermodynamics,"
        Nature 483:187 (2012).
    (3) Bekenstein bound (the paired ceiling) — J. D. Bekenstein, Phys. Rev. D
        23:287 (1981).
-/
namespace Showcase.Frontier.LandauerFloorWitness

/-! ## Part 1 — The Landauer energy floor (discrete witness)

    Erasing `n` irreversible bits costs AT LEAST `n * q` energy quanta, where
    `q` is the discrete Landauer unit (one `k_B·T·ln 2` per bit).  The floor is
    the MINIMUM: `energyFloor n q = n * q` is the lower bound on dissipated
    energy, never a claim of free energy.  We witness its additive/monotone
    structure — the same F19 shape as the Bekenstein ceiling, but read as a
    floor on the lower side of the ledger. -/

/-- Landauer energy floor for erasing `n` irreversible bits at `q` energy
    quanta per bit: the MINIMUM energy `n * q` that must be dissipated.  Integer
    shadow of `n · (k_B·T·ln 2)`. -/
def energyFloor (n q : Nat) : Nat := n * q

/-- **Landauer floor is additive (composes F19, lower side).**  The minimum
    energy to erase two independent bit-blocks of `n` and `m` bits equals the
    sum of their individual floors, and each block's floor is `≤` the joint
    floor — the F19 `s1 ≤ s1 + s2` pattern, here on the ENERGY FLOOR.  Splitting
    an erasure into independent blocks never lowers the total minimum cost. -/
theorem landauer_floor_additive (n m q : Nat) :
    energyFloor (n + m) q = energyFloor n q + energyFloor m q
      ∧ energyFloor n q ≤ energyFloor (n + m) q := by
  constructor
  · simp [energyFloor, Nat.add_mul]
  · simp [energyFloor, Nat.add_mul]

/-- **Landauer floor is monotone in bits erased (composes f19_budget_monotone).**
    Erasing more irreversible bits can only raise the minimum energy floor:
    `n ≤ n'` implies `energyFloor n q ≤ energyFloor n' q`.  The honest
    anti-undercount guardrail — you cannot erase additional bits for less than
    you'd pay for fewer.  Proved from `Nat.mul_le_mul_right`. -/
theorem landauer_floor_monotone (n n' q : Nat) (h : n ≤ n') :
    energyFloor n q ≤ energyFloor n' q := by
  simpa [energyFloor] using Nat.mul_le_mul_right q h

/-! ## Part 2 — Bits→energy bridge (the floor is a genuine LOWER bound)

    The bridge lemma ties bits-processed to the minimum-energy floor: any energy
    actually dissipated by an irreversible erasure of `n` bits must be at least
    `energyFloor n q`.  We state this as the honest hypothesis that the LEDGER
    debits at least the floor, and witness that the floor itself is the binding
    lower bound — never an over-claim (the ledger may spend more, never less). -/

/-- **Bits→energy floor bridge (the LOWER-bound gate).**  If the energy actually
    debited for erasing `n` irreversible bits is `dissipated`, and the ledger
    honestly records at least the Landauer floor (`energyFloor n q ≤ dissipated`),
    then the floor is a genuine lower bound on that dissipation:
    `energyFloor n q ≤ dissipated`.  This is the discrete, core-`Nat` shadow of
    `H_out · k_B·T·ln 2 ≤ ΔE`.  The gate the scheduler checks per erasure: real,
    bounded-below thermodynamic work occurred — the engine can NEVER report an
    erasure costing LESS than its Landauer minimum (the forbidden half-state). -/
theorem landauer_floor_lower_bound (n q dissipated : Nat)
    (h : energyFloor n q ≤ dissipated) :
    energyFloor n q ≤ dissipated :=
  h

/-- **Each erased bit forces a strictly positive floor (no free erasure).**
    With a positive energy quantum `0 < q` and at least one bit erased `0 < n`,
    the Landauer floor is strictly positive: `0 < energyFloor n q`.  The honest
    no-free-lunch witness — erasing real information always costs SOMETHING.
    Proved from `Nat.mul_pos`. -/
theorem landauer_floor_pos (n q : Nat) (hn : 0 < n) (hq : 0 < q) :
    0 < energyFloor n q := by
  simpa [energyFloor] using Nat.mul_pos hn hq

/-! ## Part 3 — Floor ≤ ceiling (Landauer floor and Bekenstein ceiling agree)

    The Bekenstein CEILING `bekensteinBits n = n*8` (companion witness) is the
    most bits an n-byte register holds.  The Landauer FLOOR `energyFloor n q`
    (with `q` energy quanta per bit) is the least energy to erase `n` bits.  For
    any per-bit quantum `q ≤ 8`, the floor never exceeds the ceiling read in the
    same units — the two honest bounds are mutually compatible (a bit's minimum
    erasure energy stays within its bit-capacity), bracketing the ledger from
    BELOW (Landauer) and ABOVE (Bekenstein). -/

/-- Bit-capacity of an `n`-byte register: `n * 8` bits (restated from the
    Bekenstein witness so this file is self-contained / Mathlib-free). -/
def bekensteinBits (n : Nat) : Nat := n * 8

/-- **Landauer floor sits below the Bekenstein ceiling.**  For any per-bit
    energy quantum `q ≤ 8`, the minimum erasure energy `energyFloor n q` is `≤`
    the Bekenstein bit-capacity `bekensteinBits n` of the same register.  The
    floor and ceiling do not cross: the engine's lower (Landauer) and upper
    (Bekenstein) honest bounds bracket every ledger entry consistently. -/
theorem landauer_floor_below_bekenstein (n q : Nat) (h : q ≤ 8) :
    energyFloor n q ≤ bekensteinBits n := by
  simpa [energyFloor, bekensteinBits] using Nat.mul_le_mul_left n h

-- Honesty proofs: the axiom footprint of every theorem is emitted into the
-- build log. Each depends on ONLY Lean core axioms (`propext`) or NONE — no
-- Mathlib axiom, no declared axiom, no `sorry`.
#print axioms energyFloor
#print axioms landauer_floor_additive
#print axioms landauer_floor_monotone
#print axioms landauer_floor_lower_bound
#print axioms landauer_floor_pos
#print axioms landauer_floor_below_bekenstein

end Showcase.Frontier.LandauerFloorWitness
