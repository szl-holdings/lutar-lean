-- Lutar/Innovations/round8/DatadogLLMObs.lean
-- Formula: DATADOG-LLMOBS-QUINTUPLE
-- Source: DataDog/dd-trace-py LLMObs distributed context propagation
-- Primary URL: https://github.com/DataDog/dd-trace-py/issues/13795
-- Doctrine: v11 LOCKED 749/14/163 · Λ = Conjecture 1 · SLSA L1 honest
-- Signed-off-by: Yachay <yachay@szlholdings.ai>
-- Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>

namespace Lutar.Innovations.Round8.DatadogLLMObs

/-- The LLM span provenance quintuple: minimum fields for agentic LLM call attribution.
    Lifted from Datadog dd-trace-py LLMObs distributed context propagation pattern.
    Source: https://github.com/DataDog/dd-trace-py/issues/13795
    (Enable trace context propagation for async background tasks in LLM observability) -/
structure LLMSpanProvenance where
  trace_id   : UInt64         -- W3C propagated root trace
  span_id    : UInt64         -- per-operation identifier
  parent_id  : Option UInt64  -- none iff this is a root span
  ml_app     : String         -- application/team label (propagated via DD_LLMOBS_ML_APP)
  session_id : Option String  -- user/session cross-link for multi-turn agents

/-- Provenance chain validity: a non-root span must have a parent_id. -/
def provenanceChainValid (s : LLMSpanProvenance) : Prop :=
  s.parent_id.isSome ∨ s.trace_id = s.span_id

/-- Decidability of provenance chain validity. -/
theorem provenance_chain_decidable (s : LLMSpanProvenance) :
    Decidable (provenanceChainValid s) := by
  unfold provenanceChainValid
  exact instDecidableOr

/-- Root span invariant: if parent_id is none, trace_id must equal span_id. -/
theorem root_span_self_trace (s : LLMSpanProvenance)
    (hno_parent : s.parent_id = none)
    (hchain : provenanceChainValid s) :
    s.trace_id = s.span_id := by
  unfold provenanceChainValid at hchain
  cases hchain with
  | inl h => simp [hno_parent] at h
  | inr h => exact h

end Lutar.Innovations.Round8.DatadogLLMObs
