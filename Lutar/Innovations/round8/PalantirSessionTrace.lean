-- Lutar/Innovations/round8/PalantirSessionTrace.lean
-- Formula: PALANTIR-SESSION-TRACE-STEPS
-- Source: Palantir AIP Agents SessionTrace API
-- Primary URL: https://github.com/palantir/foundry-platform-python/blob/develop/docs/v2/AipAgents/SessionTrace.md
-- Doctrine: v11 LOCKED 749/14/163 · Λ = Conjecture 1 · SLSA L1 honest
-- Signed-off-by: Yachay <yachay@szlholdings.ai>
-- Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>

namespace Lutar.Innovations.Round8.PalantirSessionTrace

/-- A resource identifier with type prefix (Palantir RID pattern).
    Format: ri.<resource_type>..<uuid>
    Source: https://github.com/palantir/foundry-platform-python -/
structure RID where
  resource_type : String  -- e.g. "aip-agents..agent" or "szl..organ"
  uuid          : String  -- UUID v4

/-- Step kinds in an AIP Agent session trace. -/
inductive StepKind : Type where
  | ContextRetrieval  -- RAG / retrieval step
  | ToolCall          -- external tool invocation
  | LLMInvocation     -- LLM prompt/response
  | GateEvaluation    -- SZL-specific: Λ gate evaluation
  | KhipuWrite        -- SZL-specific: receipt commit

/-- A single step in an agent session trace. -/
structure SessionStep where
  step_index   : ℕ          -- 0-based strictly ordered index
  step_kind    : StepKind
  agent_rid    : RID
  session_rid  : RID
  payload_hash : UInt64      -- hash of inputs/outputs at this step

/-- Trace ordering invariant: steps must be strictly ordered by index. -/
def traceOrdered (steps : List SessionStep) : Prop :=
  ∀ i j : Fin steps.length,
    i.val < j.val → (steps.get i).step_index < (steps.get j).step_index

/-- Base case: empty trace is trivially ordered. -/
theorem trace_ordered_nil : traceOrdered [] := by
  intro i; exact Fin.elim0 i

/-- Singleton trace is trivially ordered. -/
theorem trace_ordered_singleton (s : SessionStep) : traceOrdered [s] := by
  intro i j h
  have hi := i.isLt
  have hj := j.isLt
  simp at hi hj
  omega

/-- Step index uniqueness: in an ordered trace, each step_index appears at most once. -/
theorem trace_index_unique (steps : List SessionStep)
    (hord : traceOrdered steps)
    (i j : Fin steps.length)
    (heq : (steps.get i).step_index = (steps.get j).step_index) :
    i = j := by
  by_contra h
  have hij : i.val < j.val ∨ j.val < i.val := by omega
  cases hij with
  | inl h => have := hord i j h; omega
  | inr h => have := hord j i h; omega

end Lutar.Innovations.Round8.PalantirSessionTrace
