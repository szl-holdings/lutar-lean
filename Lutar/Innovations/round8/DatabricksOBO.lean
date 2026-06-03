-- Lutar/Innovations/round8/DatabricksOBO.lean
-- Formula: DATABRICKS-OBO-CONSENT-RECEIPT
-- Source: Databricks Unity AI Gateway on-behalf-of (OBO) consent attribution
-- Primary URL: https://www.databricks.com/blog/ai-gateway-governance-layer-agentic-ai
-- Doctrine: v11 LOCKED 749/14/163 · Λ = Conjecture 1 · SLSA L1 honest
-- Signed-off-by: Yachay <yachay@szlholdings.ai>
-- Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>

namespace Lutar.Innovations.Round8.DatabricksOBO

/-- On-behalf-of (OBO) consent attribution in an agentic action receipt.
    Lifted from Databricks Unity AI Gateway inference table schema.
    Source: https://www.databricks.com/blog/ai-gateway-governance-layer-agentic-ai
    "Every request logs the requesting identity... and for MCP calls — connection name,
    HTTP method, and whether the call was on-behalf-of user." -/
structure OBOReceipt where
  agent_principal  : String         -- the agent's service identity (IAM principal)
  user_principal   : Option String  -- human who delegated (none = autonomous action)
  action_timestamp : UInt64         -- unix epoch ms
  action_kind      : String         -- "LLM_CALL" | "MCP_READ" | "MCP_WRITE" | "TOOL_EXEC"

/-- Actions that mutate external state require explicit human delegation. -/
def requiresExplicitConsent (r : OBOReceipt) : Prop :=
  (r.action_kind = "MCP_WRITE" ∨ r.action_kind = "TOOL_EXEC") →
  r.user_principal.isSome

/-- A consent-compliant receipt: read-only actions are autonomous-ok;
    write/exec actions require explicit OBO delegation. -/
def consentCompliant (r : OBOReceipt) : Bool :=
  if r.action_kind = "MCP_WRITE" ∨ r.action_kind = "TOOL_EXEC"
  then r.user_principal.isSome
  else true

/-- The bool guard is sound: consentCompliant = true → requiresExplicitConsent. -/
theorem consent_compliant_sound (r : OBOReceipt) :
    consentCompliant r = true → requiresExplicitConsent r := by
  simp [consentCompliant, requiresExplicitConsent]
  intro h
  split_ifs at h with hk
  · intro _; exact h
  · intro hc; exact absurd hc hk

end Lutar.Innovations.Round8.DatabricksOBO
