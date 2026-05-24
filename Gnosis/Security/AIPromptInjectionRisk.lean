import Init
-- AIPromptInjectionRisk.lean
-- Anti-thesis: Large language models process all text as inert data; because the
-- model is a deterministic mathematical function mapping tokens to tokens, user
-- input cannot "inject" instructions any more than a calculator input can
-- reprogram the calculator — the system prompt is always in control.
-- Refutation: LLMs do not enforce a security boundary between the system prompt
-- and user-supplied text. Direct prompt injection overrides system instructions
-- by embedding higher-priority directives in user messages. Indirect injection
-- arrives through retrieved documents, tool outputs, or emails that contain
-- adversarial instructions the model executes. Jailbreaks exploit instruction-
-- following fine-tuning to bypass content policies. Tool-call injection causes
-- the model to invoke registered tools with attacker-controlled arguments,
-- achieving SSRF, data exfiltration, or privilege escalation. System-prompt
-- leakage reveals confidential instructions through carefully crafted queries.

namespace Gnosis.Security.AIPromptInjectionRisk

-- Direct prompt injection: user message contains directives overriding system prompt
def directPromptInjectionRisk (userInputReachesModel : Bool)
    (instructionHierarchyEnforced : Bool) : Bool :=
  userInputReachesModel && !instructionHierarchyEnforced

theorem instruction_hierarchy_enforced_safe (userInput : Bool) :
    directPromptInjectionRisk userInput true = false := by { simp [directPromptInjectionRisk]

theorem user_input_not_reaching_model_safe (hierarchyEnforced : Bool) :
    directPromptInjectionRisk false hierarchyEnforced = false := by
  simp [directPromptInjectionRisk]

theorem user_input_no_hierarchy_enforcement_risky :
    directPromptInjectionRisk true false = true := by
  simp [directPromptInjectionRisk]

-- Indirect prompt injection: retrieved documents contain adversarial instructions
def indirectPromptInjectionRisk (externalContentIncludedInContext : Bool)
    (externalContentSanitized : Bool) : Bool :=
  externalContentIncludedInContext && !externalContentSanitized

theorem external_content_sanitized_safe (included : Bool) :
    indirectPromptInjectionRisk included true = false := by
  simp [indirectPromptInjectionRisk]

theorem no_external_content_in_context_safe (sanitized : Bool) :
    indirectPromptInjectionRisk false sanitized = false := by
  simp [indirectPromptInjectionRisk]

theorem unsanitized_external_content_in_context_risky :
    indirectPromptInjectionRisk true false = true := by
  simp [indirectPromptInjectionRisk]

-- Jailbreak attempt: adversarial prompt bypasses content policy guardrails
def jailbreakRisk (adversarialPromptPresent : Bool)
    (contentPolicyRobust : Bool) : Bool :=
  adversarialPromptPresent && !contentPolicyRobust

theorem robust_content_policy_prevents_jailbreak (adversarial : Bool) :
    jailbreakRisk adversarial true = false := by
  simp [jailbreakRisk]

theorem no_adversarial_prompt_safe (robust : Bool) :
    jailbreakRisk false robust = false := by
  simp [jailbreakRisk]

theorem adversarial_prompt_weak_policy_risky :
    jailbreakRisk true false = true := by
  simp [jailbreakRisk]

-- Tool-call injection: LLM instructed to invoke tools with attacker-controlled args
def toolCallInjectionRisk (modelCanCallTools : Bool)
    (toolArgumentsValidated : Bool)
    (toolCallRequiresUserConsent : Bool) : Bool :=
  modelCanCallTools && !toolArgumentsValidated && !toolCallRequiresUserConsent

theorem tool_args_validated_prevents_injection (canCall consent : Bool) :
    toolCallInjectionRisk canCall true consent = false := by
  simp [toolCallInjectionRisk]

theorem consent_required_prevents_silent_tool_call (canCall validated : Bool) :
    toolCallInjectionRisk canCall validated true = false := by
  simp [toolCallInjectionRisk]

theorem no_tool_access_safe (validated consent : Bool) :
    toolCallInjectionRisk false validated consent = false := by
  simp [toolCallInjectionRisk]

theorem unrestricted_tool_call_no_validation_risky :
    toolCallInjectionRisk true false false = true := by
  simp [toolCallInjectionRisk]

-- System prompt leak: model reveals confidential system prompt contents
def systemPromptLeakRisk (systemPromptIsConfidential : Bool)
    (modelInstructedToProtectSystemPrompt : Bool)
    (outputFilteredForSystemPromptContent : Bool) : Bool :=
  systemPromptIsConfidential &&
  !modelInstructedToProtectSystemPrompt &&
  !outputFilteredForSystemPromptContent

theorem model_instructed_to_protect_prevents_leak (confidential outputFiltered : Bool) :
    systemPromptLeakRisk confidential true outputFiltered = false := by
  simp [systemPromptLeakRisk]

theorem output_filter_prevents_leak (confidential instructed : Bool) :
    systemPromptLeakRisk confidential instructed true = false := by
  simp [systemPromptLeakRisk]

theorem non_confidential_system_prompt_no_risk (instructed filtered : Bool) :
    systemPromptLeakRisk false instructed filtered = false := by
  simp [systemPromptLeakRisk]

theorem confidential_prompt_unprotected_unfiltered_risky :
    systemPromptLeakRisk true false false = true := by
  simp [systemPromptLeakRisk]

-- Aggregate AI prompt injection risk count
def aggregateAIPromptInjectionRisk
    (userInput hierarchyEnforced : Bool)
    (extContent extSanitized : Bool)
    (adversarial policyRobust : Bool)
    (canCallTools toolArgsValidated toolConsentRequired : Bool)
    (confidentialPrompt modelProtects outputFiltered : Bool) : Nat :=
  (if directPromptInjectionRisk userInput hierarchyEnforced then 1 else 0) +
  (if indirectPromptInjectionRisk extContent extSanitized then 1 else 0) +
  (if jailbreakRisk adversarial policyRobust then 1 else 0) +
  (if toolCallInjectionRisk canCallTools toolArgsValidated toolConsentRequired then 1 else 0) +
  (if systemPromptLeakRisk confidentialPrompt modelProtects outputFiltered then 1 else 0)

theorem fully_hardened_zero_ai_prompt_injection_risk :
    aggregateAIPromptInjectionRisk
      true true
      true true
      false true
      true true true
      true true true = 0 := by
  simp [aggregateAIPromptInjectionRisk, directPromptInjectionRisk,
        indirectPromptInjectionRisk, jailbreakRisk, toolCallInjectionRisk,
        systemPromptLeakRisk]

theorem all_ai_prompt_injection_vectors_max_risk :
    aggregateAIPromptInjectionRisk
      true false
      true false
      true false
      true false false
      true false false = 5 := by
  simp [aggregateAIPromptInjectionRisk, directPromptInjectionRisk,
        indirectPromptInjectionRisk, jailbreakRisk, toolCallInjectionRisk,
        systemPromptLeakRisk]

theorem ai_prompt_injection_risk_bounded
    (userInput hierarchyEnforced : Bool)
    (extContent extSanitized : Bool)
    (adversarial policyRobust : Bool)
    (canCallTools toolArgsValidated toolConsentRequired : Bool)
    (confidentialPrompt modelProtects outputFiltered : Bool) :
    aggregateAIPromptInjectionRisk
      userInput hierarchyEnforced extContent extSanitized adversarial policyRobust
      canCallTools toolArgsValidated toolConsentRequired
      confidentialPrompt modelProtects outputFiltered ≤ 5 := by
  simp [aggregateAIPromptInjectionRisk]
  split <;> split <;> split <;> split <;> split <;> decide

-- Scanner ROI: AI prompt injection detection prevents data exfiltration and privilege escalation
def aiPromptInjectionDetectionValueCents (exfiltrationBreachCostCents : Nat)
    (scannerCostCents : Nat) : Int :=
  (exfiltrationBreachCostCents : Int) - (scannerCostCents : Int)

theorem ai_prompt_injection_scanner_profitable (breach scan : Nat) (h : scan < breach) :
    0 < aiPromptInjectionDetectionValueCents breach scan := by
  simp [aiPromptInjectionDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem ai_prompt_injection_scanner_break_even (cost : Nat) :
    0 ≤ aiPromptInjectionDetectionValueCents cost cost := by
  simp [aiPromptInjectionDetectionValueCents]

-- Fleet ROI: prompt injection scan scales across all LLM-integrated endpoints
def aiPromptInjectionFleetROI (detectionValueCents : Nat) (llmEndpoints : Nat) : Nat :=
  detectionValueCents * llmEndpoints

theorem ai_prompt_injection_fleet_roi_monotone_endpoints (v e1 e2 : Nat) (h : e1 ≤ e2) :
    aiPromptInjectionFleetROI v e1 ≤ aiPromptInjectionFleetROI v e2 := by
  simp [aiPromptInjectionFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_ai_prompt_injection_fleet_roi (v e : Nat) (hv : 0 < v) (he : 0 < e) :
    0 < aiPromptInjectionFleetROI v e := by
  simp [aiPromptInjectionFleetROI]
  exact Nat.mul_pos hv he

end AIPromptInjectionRisk
