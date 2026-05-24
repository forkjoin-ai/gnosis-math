import Init
-- PromptLeakageRisk.lean
-- Anti-thesis: System prompts and few-shot examples are passed as input to
-- inference APIs and are therefore always fully controlled by the application
-- developer; because the model only generates completions and has no persistent
-- state, there is no mechanism by which prompt content can leak to end users.
-- Refutation: Prompt leakage is a well-documented attack class. Adversarial
-- inputs cause models to repeat system prompt contents verbatim. Few-shot
-- example leakage exposes proprietary business logic, pricing formulas, or
-- customer PII embedded in training examples. Tool descriptions in function-
-- calling APIs reveal internal system architecture when returned in error
-- messages or verbose outputs. Fine-tuning data reconstruction allows
-- membership inference and verbatim extraction of training samples. Cached
-- prompt responses shared across users expose one user's context to another
-- when caching keys are insufficiently scoped_.

namespace Gnosis.Security.PromptLeakageRisk

-- System prompt extraction: adversarial input causes model to repeat system prompt
def systemPromptExtractionRisk (systemPromptContainsSecrets : Bool)
    (extractionAttemptsPrevented : Bool) : Bool :=
  systemPromptContainsSecrets && !extractionAttemptsPrevented

theorem extraction_prevention_protects_system_prompt (secrets : Bool) :
    systemPromptExtractionRisk secrets true = false := by { simp [systemPromptExtractionRisk]

theorem no_secrets_in_system_prompt_safe (prevented : Bool) :
    systemPromptExtractionRisk false prevented = false := by
  simp [systemPromptExtractionRisk]

theorem secrets_in_system_prompt_unprotected_risky :
    systemPromptExtractionRisk true false = true := by
  simp [systemPromptExtractionRisk]

-- Few-shot example leak: examples containing PII or business logic exposed via output
def fewShotExampleLeakRisk (fewShotExamplesContainSensitiveData : Bool)
    (outputSanitizedForExampleContent : Bool) : Bool :=
  fewShotExamplesContainSensitiveData && !outputSanitizedForExampleContent

theorem output_sanitization_prevents_example_leak (sensitive : Bool) :
    fewShotExampleLeakRisk sensitive true = false := by
  simp [fewShotExampleLeakRisk]

theorem few_shot_examples_not_sensitive_safe (sanitized : Bool) :
    fewShotExampleLeakRisk false sanitized = false := by
  simp [fewShotExampleLeakRisk]

theorem sensitive_examples_output_unsanitized_risky :
    fewShotExampleLeakRisk true false = true := by
  simp [fewShotExampleLeakRisk]

-- Tool description leak: function-calling API exposes internal architecture
def toolDescriptionLeakRisk (toolDescriptionsExposedInOutput : Bool)
    (toolDescriptionsRedacted : Bool) : Bool :=
  toolDescriptionsExposedInOutput && !toolDescriptionsRedacted

theorem tool_description_redaction_prevents_architecture_leak (exposed : Bool) :
    toolDescriptionLeakRisk exposed true = false := by
  simp [toolDescriptionLeakRisk]

theorem tool_descriptions_not_in_output_safe (redacted : Bool) :
    toolDescriptionLeakRisk false redacted = false := by
  simp [toolDescriptionLeakRisk]

theorem tool_descriptions_exposed_unredacted_risky :
    toolDescriptionLeakRisk true false = true := by
  simp [toolDescriptionLeakRisk]

-- Fine-tuning data reconstruction: membership inference on fine-tuned model
def fineTuningDataReconstructionRisk (modelFineTunedOnProprietaryData : Bool)
    (membershipInferenceMitigated : Bool) : Bool :=
  modelFineTunedOnProprietaryData && !membershipInferenceMitigated

theorem membership_inference_mitigation_prevents_reconstruction (fineTuned : Bool) :
    fineTuningDataReconstructionRisk fineTuned true = false := by
  simp [fineTuningDataReconstructionRisk]

theorem model_not_fine_tuned_on_proprietary_data_safe (mitigated : Bool) :
    fineTuningDataReconstructionRisk false mitigated = false := by
  simp [fineTuningDataReconstructionRisk]

theorem proprietary_fine_tuned_without_mitigation_risky :
    fineTuningDataReconstructionRisk true false = true := by
  simp [fineTuningDataReconstructionRisk]

-- Cached prompt cross-user leak: shared cache exposes one user's prompt context to another
def cachedPromptCrossUserLeakRisk (promptResponsesCached : Bool)
    (cacheKeysScopedPerUser : Bool) : Bool :=
  promptResponsesCached && !cacheKeysScopedPerUser

theorem user_scoped_cache_keys_prevent_cross_user_leak (cached : Bool) :
    cachedPromptCrossUserLeakRisk cached true = false := by
  simp [cachedPromptCrossUserLeakRisk]

theorem responses_not_cached_safe (scoped_ : Bool) :
    cachedPromptCrossUserLeakRisk false scoped_ = false := by
  simp [cachedPromptCrossUserLeakRisk]

theorem unscoped_cached_responses_risky :
    cachedPromptCrossUserLeakRisk true false = true := by
  simp [cachedPromptCrossUserLeakRisk]

-- Aggregate prompt leakage risk count
def aggregatePromptLeakageRisk
    (promptSecrets extractionPrevented : Bool)
    (sensitiveFewShot outputSanitized : Bool)
    (toolsInOutput toolsRedacted : Bool)
    (proprietaryFineTuned membershipMitigated : Bool)
    (cached cacheScopedPerUser : Bool) : Nat :=
  (if systemPromptExtractionRisk promptSecrets extractionPrevented then 1 else 0) +
  (if fewShotExampleLeakRisk sensitiveFewShot outputSanitized then 1 else 0) +
  (if toolDescriptionLeakRisk toolsInOutput toolsRedacted then 1 else 0) +
  (if fineTuningDataReconstructionRisk proprietaryFineTuned membershipMitigated then 1 else 0) +
  (if cachedPromptCrossUserLeakRisk cached cacheScopedPerUser then 1 else 0)

theorem fully_hardened_zero_prompt_leakage_risk :
    aggregatePromptLeakageRisk
      true true
      true true
      true true
      true true
      true true = 0 := by
  simp [aggregatePromptLeakageRisk, systemPromptExtractionRisk, fewShotExampleLeakRisk,
        toolDescriptionLeakRisk, fineTuningDataReconstructionRisk, cachedPromptCrossUserLeakRisk]

theorem all_prompt_leakage_vectors_max_risk :
    aggregatePromptLeakageRisk
      true false
      true false
      true false
      true false
      true false = 5 := by
  simp [aggregatePromptLeakageRisk, systemPromptExtractionRisk, fewShotExampleLeakRisk,
        toolDescriptionLeakRisk, fineTuningDataReconstructionRisk, cachedPromptCrossUserLeakRisk]

theorem prompt_leakage_risk_bounded
    (promptSecrets extractionPrevented : Bool)
    (sensitiveFewShot outputSanitized : Bool)
    (toolsInOutput toolsRedacted : Bool)
    (proprietaryFineTuned membershipMitigated : Bool)
    (cached cacheScopedPerUser : Bool) :
    aggregatePromptLeakageRisk
      promptSecrets extractionPrevented sensitiveFewShot outputSanitized
      toolsInOutput toolsRedacted proprietaryFineTuned membershipMitigated
      cached cacheScopedPerUser ≤ 5 := by
  simp [aggregatePromptLeakageRisk]
  split <;> split <;> split <;> split <;> split <;> decide

-- Scanner ROI: prompt leakage detection prevents IP and PII exposure via model outputs
def promptLeakageDetectionValueCents (ipExposureCostCents : Nat)
    (scannerCostCents : Nat) : Int :=
  (ipExposureCostCents : Int) - (scannerCostCents : Int)

theorem prompt_leakage_scanner_profitable (ip scan : Nat) (h : scan < ip) :
    0 < promptLeakageDetectionValueCents ip scan := by
  simp [promptLeakageDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem prompt_leakage_scanner_break_even (cost : Nat) :
    0 ≤ promptLeakageDetectionValueCents cost cost := by
  simp [promptLeakageDetectionValueCents]

-- Fleet ROI: prompt leakage scan scales across all LLM API integrations
def promptLeakageFleetROI (detectionValueCents : Nat) (llmIntegrations : Nat) : Nat :=
  detectionValueCents * llmIntegrations

theorem prompt_leakage_fleet_roi_monotone (v i1 i2 : Nat) (h : i1 ≤ i2) :
    promptLeakageFleetROI v i1 ≤ promptLeakageFleetROI v i2 := by
  simp [promptLeakageFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_prompt_leakage_fleet_roi (v i : Nat) (hv : 0 < v) (hi : 0 < i) :
    0 < promptLeakageFleetROI v i := by
  simp [promptLeakageFleetROI]
  exact Nat.mul_pos hv hi

end PromptLeakageRisk
