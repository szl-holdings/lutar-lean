-- Lutar/Innovations/round8/StoicHaltSemantics.lean
-- Formula: STOIC-HALT-SEMANTICS
-- Source: Epictetus, Discourses II.2 (~108 CE); Marcus Aurelius, Meditations (161-180 CE)
-- Academic: Stanford Encyclopedia of Philosophy, "Stoicism" (Baltzly, 2023)
-- URL: https://plato.stanford.edu/entries/stoicism/
-- Doctrine: v11 LOCKED 749/14/163 · Λ = Conjecture 1 · SLSA L1 honest
-- Signed-off-by: Yachay <yachay@szlholdings.ai>
-- Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>

namespace Lutar.Innovations.Round8.StoicHaltSemantics

/-- Stoic consent-action axiom applied to SZL agent gate.
    Epictetus: "Assent (synkatathesis) is in our power; impulse follows assent."
    Discourses II.2; SEP Stoicism §2.9 (Baltzly 2023).
    https://plato.stanford.edu/entries/stoicism/

    SZL mapping:
    - Impression = incoming action request
    - Assent = gate evaluation Λ ≥ threshold
    - Impulse = agent executes the action

    Halt condition: ¬assent → ¬execute (Stoic contrapositive) -/

/-- An agent action with its Λ gate score ∈ ℚ ∩ [0,1]. -/
structure AgentAction where
  name       : String
  gate_score : ℚ  -- Λ score

/-- Doctrine minimum gate threshold (doctrine parameter, not a kernel constant). -/
def doctrineThreshold : ℚ := 1 / 2

/-- Stoic assent condition: action is admissible iff gate_score ≥ threshold. -/
def stoicAssent (a : AgentAction) : Prop :=
  a.gate_score ≥ doctrineThreshold

/-- The halt guard: returns true iff assent is granted. -/
def haltGuard (a : AgentAction) : Bool :=
  if a.gate_score ≥ doctrineThreshold then true else false

/-- Stoic halt invariant: action is blocked iff assent is withheld. -/
theorem stoic_halt_invariant (a : AgentAction) :
    ¬ stoicAssent a ↔ haltGuard a = false := by
  simp [stoicAssent, haltGuard, doctrineThreshold]
  constructor
  · intro h; simp [Rat.not_le.mp h]
  · intro h
    split_ifs at h with hle
    · exact absurd rfl (Bool.noConfusion h)
    · exact Rat.not_le.mp (Rat.not_le.mpr (by push_neg at hle; exact hle))

/-- Marcus Aurelius corollary: an agent that acts without assent is irrational.
    Meditations IV.3: "Confine yourself to the present."
    Formal: if haltGuard = false, the action must not proceed. -/
def rationallyClear (a : AgentAction) : Prop :=
  haltGuard a = true → stoicAssent a

theorem rational_clarity (a : AgentAction) : rationallyClear a := by
  intro h
  simp [haltGuard, stoicAssent] at *
  split_ifs at h with hle
  · exact hle
  · simp at h

end Lutar.Innovations.Round8.StoicHaltSemantics
