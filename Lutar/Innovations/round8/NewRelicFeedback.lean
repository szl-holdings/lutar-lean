-- Lutar/Innovations/round8/NewRelicFeedback.lean
-- Formula: NEWRELIC-DEFERRED-FEEDBACK-RECEIPT
-- Source: New Relic AI Monitoring SDK - record_llm_feedback_event pattern
-- Primary URL: https://docs.newrelic.com/docs/apm/agents/ruby-agent/api-guides/ai-monitoring/
-- Doctrine: v11 LOCKED 749/14/163 · Λ = Conjecture 1 · SLSA L1 honest
-- Signed-off-by: Yachay <yachay@szlholdings.ai>
-- Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>

namespace Lutar.Innovations.Round8.NewRelicFeedback

/-- A deferred feedback annotation linked to an existing trace by trace_id.
    Pattern from New Relic record_llm_feedback_event:
    https://docs.newrelic.com/docs/apm/agents/ruby-agent/api-guides/ai-monitoring/
    "Correlate trace IDs between a generated message from the AI and
     message feedback from an end user." -/
structure FeedbackReceipt where
  trace_id     : UInt64              -- links to original DSSE receipt (LLM span)
  rating       : Int                 -- e.g. -1 (bad), 0 (neutral), 1 (good)
  annotator_id : String              -- who provided feedback (signed identity)
  feedback_ts  : UInt64             -- unix epoch ms of annotation
  category     : Option String       -- optional: "informative", "inaccurate", etc.
  metadata     : List (String × String)  -- arbitrary key-value pairs

/-- Temporal validity: feedback must arrive after the original trace. -/
def feedbackTemporallyValid (orig_ts : UInt64) (r : FeedbackReceipt) : Prop :=
  orig_ts < r.feedback_ts

/-- Decidability of temporal validity. -/
theorem feedback_temporal_decidable (orig_ts : UInt64) (r : FeedbackReceipt) :
    Decidable (feedbackTemporallyValid orig_ts r) :=
  UInt64.decLt orig_ts r.feedback_ts

/-- Rating validity: rating must be in [-1, 0, 1] or any finite scale. -/
def ratingValid (r : FeedbackReceipt) (lo hi : Int) : Prop :=
  lo ≤ r.rating ∧ r.rating ≤ hi

/-- Annotator non-empty: anonymous feedback is inadmissible. -/
def annotatorValid (r : FeedbackReceipt) : Prop :=
  r.annotator_id ≠ ""

/-- A fully valid deferred feedback receipt. -/
def feedbackValid (orig_ts : UInt64) (r : FeedbackReceipt) : Prop :=
  feedbackTemporallyValid orig_ts r ∧
  annotatorValid r ∧
  ratingValid r (-1) 1

end Lutar.Innovations.Round8.NewRelicFeedback
