import Init
-- AIDataPipelineRisk.lean
-- Anti-thesis: AI training pipelines operate in isolated, access-controlled environments.
-- Input data undergoes automated validation before it touches model weights. Any
-- corruption would be detected by loss curves deviating from baseline — the
-- training process itself acts as a quality gate, so deliberate poisoning is
-- impractical at meaningful scale.
-- Refutation: Modern ML pipelines ingest from public datasets, user-contributed
-- data, and third-party sources where adversarial control is feasible. Training-
-- data poisoning embeds backdoor triggers that survive loss-based filtering because
-- the trigger is rare and the clean-loss term dominates. Label flipping at low rate
-- (<1%) evades statistical anomaly detection while causing targeted misclassification.
-- Data exfiltration via model outputs exploits memorisation: sufficiently rare
-- training examples can be reconstructed verbatim via targeted queries. Preprocessing
-- injection corrupts normalisation, tokenisation, or augmentation steps before
-- training. Feature-store tampering poisons shared embedding/feature tables used
-- by many downstream models simultaneously.

namespace Gnosis.Security.AIDataPipelineRisk

-- Training data poisoning: adversarial samples embed backdoor triggers
def trainingDataPoisoningRisk (untrustedDataIngested : Bool)
    (dataProvenanceVerified : Bool)
    (poisonDetectionEnabled : Bool) : Bool :=
  untrustedDataIngested && !dataProvenanceVerified && !poisonDetectionEnabled

theorem provenance_verified_prevents_poisoning (ingested detected : Bool) :
    trainingDataPoisoningRisk ingested true detected = false := by { simp [trainingDataPoisoningRisk]

theorem poison_detection_enabled_prevents_poisoning (ingested provenance : Bool) :
    trainingDataPoisoningRisk ingested provenance true = false := by
  simp [trainingDataPoisoningRisk]

theorem no_untrusted_data_no_poisoning_risk (provenance detected : Bool) :
    trainingDataPoisoningRisk false provenance detected = false := by
  simp [trainingDataPoisoningRisk]

theorem unverified_undetected_poisoning_risky :
    trainingDataPoisoningRisk true false false = true := by
  simp [trainingDataPoisoningRisk]

-- Label flipping: attacker corrupts ground-truth labels at low rate to skew model
-- poisonedLabels / totalLabels < detectionThreshold → evades detector
def labelFlippingUndetected (poisonedLabels : Nat) (totalLabels : Nat)
    (detectionThresholdPPM : Nat) : Bool :=
  if totalLabels = 0 then false
  else poisonedLabels * 1000000 / totalLabels < detectionThresholdPPM

theorem zero_poisoned_labels_not_detected (total threshold : Nat) (h : 0 < total) :
    labelFlippingUndetected 0 total threshold = true := by
  simp [labelFlippingUndetected, h]

theorem all_labels_poisoned_detected (threshold : Nat) :
    labelFlippingUndetected 1000000 1000000 threshold = (threshold > 1000000) := by
  simp [labelFlippingUndetected]

def labelFlippingRisk (poisonedLabels : Nat) (totalLabels : Nat)
    (detectionThresholdPPM : Nat)
    (labelIntegrityChecksEnabled : Bool) : Bool :=
  !labelIntegrityChecksEnabled &&
  labelFlippingUndetected poisonedLabels totalLabels detectionThresholdPPM

theorem label_integrity_checks_prevent_risk (p t d : Nat) :
    labelFlippingRisk p t d true = false := by
  simp [labelFlippingRisk]

-- Data exfiltration via model: memorised training data recoverable through queries
def dataExfiltrationViaModelRisk (modelMemorizesRareExamples : Bool)
    (outputFilteringEnabled : Bool)
    (membershipInferenceDefenceEnabled : Bool) : Bool :=
  modelMemorizesRareExamples &&
  !outputFilteringEnabled &&
  !membershipInferenceDefenceEnabled

theorem output_filtering_prevents_exfiltration (memorizes miDefence : Bool) :
    dataExfiltrationViaModelRisk memorizes true miDefence = false := by
  simp [dataExfiltrationViaModelRisk]

theorem mi_defence_prevents_exfiltration (memorizes filtered : Bool) :
    dataExfiltrationViaModelRisk memorizes filtered true = false := by
  simp [dataExfiltrationViaModelRisk]

theorem no_memorization_no_exfiltration_risk (filtered miDefence : Bool) :
    dataExfiltrationViaModelRisk false filtered miDefence = false := by
  simp [dataExfiltrationViaModelRisk]

theorem memorized_unfiltered_undefended_exfiltration_risky :
    dataExfiltrationViaModelRisk true false false = true := by
  simp [dataExfiltrationViaModelRisk]

-- Preprocessing injection: adversarial code/data in transformation pipelines
def preprocessingInjectionRisk (preprocessingCodeFromUntrustedSource : Bool)
    (preprocessingCodeAudited : Bool)
    (sandboxingEnabled : Bool) : Bool :=
  preprocessingCodeFromUntrustedSource &&
  !preprocessingCodeAudited &&
  !sandboxingEnabled

theorem audited_preprocessing_code_safe (untrusted sandboxed : Bool) :
    preprocessingInjectionRisk untrusted true sandboxed = false := by
  simp [preprocessingInjectionRisk]

theorem sandboxed_preprocessing_safe (untrusted audited : Bool) :
    preprocessingInjectionRisk untrusted audited true = false := by
  simp [preprocessingInjectionRisk]

theorem trusted_source_preprocessing_safe (audited sandboxed : Bool) :
    preprocessingInjectionRisk false audited sandboxed = false := by
  simp [preprocessingInjectionRisk]

theorem untrusted_unaudited_unsandboxed_preprocessing_risky :
    preprocessingInjectionRisk true false false = true := by
  simp [preprocessingInjectionRisk]

-- Feature store tampering: shared feature tables corrupted, affecting many models
def featureStoreTamperingRisk (featureStoreWritable : Bool)
    (featureStoreIntegrityChecked : Bool)
    (featureVersioningEnabled : Bool) : Bool :=
  featureStoreWritable &&
  !featureStoreIntegrityChecked &&
  !featureVersioningEnabled

theorem integrity_checks_prevent_feature_tampering (writable versioned : Bool) :
    featureStoreTamperingRisk writable true versioned = false := by
  simp [featureStoreTamperingRisk]

theorem feature_versioning_enables_rollback (writable checked : Bool) :
    featureStoreTamperingRisk writable checked true = false := by
  simp [featureStoreTamperingRisk]

theorem readonly_feature_store_safe (checked versioned : Bool) :
    featureStoreTamperingRisk false checked versioned = false := by
  simp [featureStoreTamperingRisk]

theorem writable_unchecked_unversioned_feature_store_risky :
    featureStoreTamperingRisk true false false = true := by
  simp [featureStoreTamperingRisk]

-- Blast radius: feature store tamper affects all models using corrupted features
-- numberOfModelsAffected is monotone in featureTableScopeSize
def featureStoreTamperingBlastRadius (featureTableScopeSize : Nat)
    (modelsPerTable : Nat) : Nat :=
  featureTableScopeSize * modelsPerTable

theorem larger_feature_scope_greater_blast_radius (m s1 s2 : Nat) (h : s1 ≤ s2) :
    featureStoreTamperingBlastRadius s1 m ≤ featureStoreTamperingBlastRadius s2 m := by
  simp [featureStoreTamperingBlastRadius]
  exact Nat.mul_le_mul_right m h

-- Aggregate AI data pipeline risk
def aggregateAIDataPipelineRisk
    (untrustedIngested provenanceVerified poisonDetected : Bool)
    (labelIntegrityChecks : Bool)
    (modelMemorizes outputFiltered miDefence : Bool)
    (preprocessingUntrusted preprocessingAudited preprocessingSandboxed : Bool)
    (featureStoreWritable featureIntegrityChecked featureVersioned : Bool) : Nat :=
  (if trainingDataPoisoningRisk untrustedIngested provenanceVerified poisonDetected then 1 else 0) +
  (if labelIntegrityChecks then 0 else 1) +
  (if dataExfiltrationViaModelRisk modelMemorizes outputFiltered miDefence then 1 else 0) +
  (if preprocessingInjectionRisk preprocessingUntrusted preprocessingAudited preprocessingSandboxed then 1 else 0) +
  (if featureStoreTamperingRisk featureStoreWritable featureIntegrityChecked featureVersioned then 1 else 0)

theorem fully_hardened_ai_data_pipeline_zero_risk :
    aggregateAIDataPipelineRisk
      true true true
      true
      false true true
      false true true
      false true true = 0 := by
  simp [aggregateAIDataPipelineRisk, trainingDataPoisoningRisk,
        dataExfiltrationViaModelRisk, preprocessingInjectionRisk,
        featureStoreTamperingRisk]

theorem all_ai_data_pipeline_controls_missing_max_risk :
    aggregateAIDataPipelineRisk
      true false false
      false
      true false false
      true false false
      true false false = 5 := by
  simp [aggregateAIDataPipelineRisk, trainingDataPoisoningRisk,
        dataExfiltrationViaModelRisk, preprocessingInjectionRisk,
        featureStoreTamperingRisk]

theorem ai_data_pipeline_risk_bounded
    (untrustedIngested provenanceVerified poisonDetected : Bool)
    (labelIntegrityChecks : Bool)
    (modelMemorizes outputFiltered miDefence : Bool)
    (preprocessingUntrusted preprocessingAudited preprocessingSandboxed : Bool)
    (featureStoreWritable featureIntegrityChecked featureVersioned : Bool) :
    aggregateAIDataPipelineRisk
      untrustedIngested provenanceVerified poisonDetected
      labelIntegrityChecks
      modelMemorizes outputFiltered miDefence
      preprocessingUntrusted preprocessingAudited preprocessingSandboxed
      featureStoreWritable featureIntegrityChecked featureVersioned ≤ 5 := by
  simp [aggregateAIDataPipelineRisk]
  split <;> split <;> split <;> split <;> split <;> decide

-- Scanner ROI: detecting AI data pipeline vulnerabilities before model deployment
def aiDataPipelineScannerROI (poisoningIncidentCostCents : Nat)
    (scannerCostCents : Nat) : Int :=
  (poisoningIncidentCostCents : Int) - (scannerCostCents : Int)

theorem ai_data_pipeline_scanner_profitable (incident scan : Nat) (h : scan < incident) :
    0 < aiDataPipelineScannerROI incident scan := by
  simp [aiDataPipelineScannerROI]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Fleet ROI: scales with number of ML models in production
def aiDataPipelineFleetROI (detectionValueCents : Nat) (modelsInProduction : Nat) : Nat :=
  detectionValueCents * modelsInProduction

theorem ai_data_pipeline_fleet_roi_monotone (v m1 m2 : Nat) (h : m1 ≤ m2) :
    aiDataPipelineFleetROI v m1 ≤ aiDataPipelineFleetROI v m2 := by
  simp [aiDataPipelineFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_ai_data_pipeline_fleet_roi (v m : Nat) (hv : 0 < v) (hm : 0 < m) :
    0 < aiDataPipelineFleetROI v m := by
  simp [aiDataPipelineFleetROI]
  exact Nat.mul_pos hv hm

end AIDataPipelineRisk
