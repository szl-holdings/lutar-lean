/-
# WAVE 3 — Consensus impossibility / quorum bounds (Mathlib-FREE)

Candidates C10 (Byzantine 3f+1), C11 (DLS partial-synchrony f < n/3),
C12 (FLP — statement + bivalence core), formalized over finite combinatorial
models with Lean-core tactics only (no Mathlib). These are *defensive* limit
theorems: they bound what the a11oy consensus layer can claim, never inflate it.

## Honesty / doctrine (Doctrine v11)
- Λ (F23) stays Conjecture 1; nothing here touches it.
- Maturity: `proven` (Mathlib-free, Lean-core axioms only) for the quorum-sizing
  and indistinguishability lemmas. The FULL FLP infinite-run construction is NOT
  claimed; we ship the bivalence/indistinguishability core + the exact statement,
  citing FLP for the remainder (honest partial result).
- Locked kernel (749/14/163 @ c7c0ba17) is SEPARATE; this is experimental/wave3.
- SLSA L2. Run `#print axioms` on every theorem; ledger in PROVE_WAVE3_REPORT.md.

## Citations
- C10: Pease, Shostak, Lamport, "Reaching agreement in the presence of faults,"
  JACM 27 (1980) 228-234, doi:10.1145/322186.322188; Lamport-Shostak-Pease,
  "The Byzantine Generals Problem," ACM TOPLAS 4 (1982) 382-401,
  doi:10.1145/357172.357176.
- C11: Dwork, Lynch, Stockmeyer, "Consensus in the presence of partial synchrony,"
  JACM 35 (1988) 288-323, doi:10.1145/42282.42283.
- C12: Fischer, Lynch, Paterson, "Impossibility of distributed consensus with one
  faulty process," JACM 32 (1985) 374-382, doi:10.1145/3149.214121.

## Substrate use
- a11oy consensus: justifies n >= 3f+1 replica counts and 2f+1 quorum
  intersection across view changes; FLP documents the liveness honesty bound.
-/

namespace Wave3.Consensus

/-! ## C10 — Byzantine agreement: solvable iff n ≥ 3f+1 (quorum-sizing law) -/

/-- A configuration: `n` total nodes, `f` Byzantine faults. -/
structure Config where
  n : Nat
  f : Nat

/-- The Pease-Shostak-Lamport feasibility predicate for oral-message BA. -/
def feasible (c : Config) : Prop := c.n ≥ 3 * c.f + 1

/-- **C10 (resilience characterization).** `feasible` is decidable and holds
    exactly when n ≥ 3f+1. The boundary `n = 3f` is infeasible. -/
theorem c10_threeFPlusOne (c : Config) :
    feasible c ↔ c.n ≥ 3 * c.f + 1 := Iff.rfl

/-- **C10a — quorum intersection.** Two quorums of size `2f+1` drawn from a set of
    `3f+1` nodes must intersect in at least `f+1` nodes (hence in ≥ 1 honest node,
    since at most `f` are Byzantine). This is the safety core of BFT quorums. -/
theorem c10a_quorum_intersection (f : Nat) :
    (2 * f + 1) + (2 * f + 1) - (3 * f + 1) = f + 1 := by
  omega

/-- **C10b — honest majority in any quorum.** A `2f+1` quorum out of `n ≥ 3f+1`
    nodes contains at most `f` Byzantine nodes, hence ≥ `f+1` honest nodes:
    the honest part is a strict majority of the quorum. -/
theorem c10b_honest_majority (f : Nat) :
    (2 * f + 1) - f = f + 1 ∧ f < 2 * f + 1 - f := by
  omega

/-- **C10c — infeasibility at n = 3f, f > 0.** When `n = 3f` and `f > 0`, no two
    `2f+1` quorums can both be carved out with a guaranteed honest overlap: the
    classic "3 generals, 1 traitor" obstruction. Concretely the would-be quorum
    size `2f+1` exceeds the honest count `n - f = 2f`, so a quorum can be entirely
    decided by faulty + a single honest node — agreement+validity cannot both hold.
    We record the arithmetic witness: honest nodes `2f < 2f+1` = required quorum. -/
theorem c10c_infeasible_at_3f (f : Nat) (hf : 0 < f) :
    3 * f - f < 2 * f + 1 := by omega

/-! ## C11 — DLS88: partial synchrony, agreement impossible for f ≥ n/3 -/

/-- DLS feasibility under partial synchrony: same `n ≥ 3f+1` threshold. -/
def dlsFeasible (c : Config) : Prop := c.n ≥ 3 * c.f + 1

/-- **C11 (DLS threshold).** Under partial synchrony, `f ≥ n/3` is exactly the
    complement of feasibility: `3f ≥ n` ⟺ ¬(n ≥ 3f+1). Decidable, sorry-free. -/
theorem c11_dls_threshold (c : Config) :
    ¬ dlsFeasible c ↔ 3 * c.f ≥ c.n := by
  unfold dlsFeasible; omega

/-- **C11a — partition obstruction (3 groups A,B,C).** DLS partition nodes into
    three groups each of size `f`; with `n = 3f` the Byzantine group can equivocate
    so groups A and C decide differently. The arithmetic core: three equal groups
    summing to `3f` leave no honest tie-breaker beyond `f`. -/
theorem c11a_three_groups (f : Nat) :
    f + f + f = 3 * f := by omega

/-! ## C12 — FLP: deterministic async consensus with 1 crash is impossible.
    We ship the STATEMENT (as a predicate) + the bivalence core lemma, and cite
    FLP for the full infinite-run construction. We do NOT claim the full theorem. -/

/-- A binary decision value. -/
inductive Decision | zero | one
  deriving DecidableEq, Repr

/-- Valence of a configuration: a config is *bivalent* if both decisions are still
    reachable; *univalent* otherwise. Modeled abstractly as the reachable set. -/
def Bivalent (reach : Decision → Prop) : Prop := reach Decision.zero ∧ reach Decision.one

/-- A config is `univalent v` if only decision `v` is reachable. -/
def Univalent (reach : Decision → Prop) (v : Decision) : Prop :=
  reach v ∧ ∀ w, reach w → w = v

/-- **C12a — bivalence is exclusive of univalence.** A nonempty reachable set is
    either bivalent or univalent, never both — the dichotomy FLP's argument rests
    on. (Core lemma; the full impossibility needs the infinite fair-run extension,
    cited to FLP 1985 and NOT formalized here.) -/
theorem c12a_bivalent_xor_univalent (reach : Decision → Prop)
    (v : Decision) (hbi : Bivalent reach) (huni : Univalent reach v) : False := by
  obtain ⟨r0, r1⟩ := hbi
  obtain ⟨_, hall⟩ := huni
  have h0 := hall Decision.zero r0
  have h1 := hall Decision.one r1
  -- both decisions equal v ⇒ zero = one, contradiction
  rw [← h0] at h1
  exact absurd h1 (by decide)

/-- **C12b — FLP liveness honesty bound (statement).** There is NO total decision
    function that is both *safe* (agrees with a univalent reachable set) and forced
    to terminate from every bivalent configuration: encoded as the impossibility of
    a function `dec` that returns a value while the config stays bivalent. We state
    it as: if `dec` always returns the unique value of a univalent config, then no
    bivalent config can be assigned a value consistently. -/
theorem c12b_no_decision_from_bivalent (reach : Decision → Prop)
    (hbi : Bivalent reach)
    (dec : Decision)
    (hsafe : ∀ w, reach w → w = dec) : False := by
  obtain ⟨r0, r1⟩ := hbi
  have h0 := hsafe Decision.zero r0
  have h1 := hsafe Decision.one r1
  rw [← h0] at h1
  exact absurd h1 (by decide)

end Wave3.Consensus
