import Init
-- BackdoorTriggerRisk.lean
-- Anti-thesis: Neural network backdoors (Trojan attacks) require the attacker
-- to control the training data and inject a detectable trigger pattern.
-- Modern training pipelines with provenance verification and anomaly detection
-- on loss curves make injection impractical. Any backdoor would be caught
-- during model evaluation because the trigger pattern is visible in the input.
-- Refutation: Clean-label backdoor attacks inject examples with adversarially
-- crafted features that are correctly labelled, evading provenance-based
-- detection. Dynamic triggers change pattern per-input, making trigger
-- detection impossible without knowledge of the trigger generation function.
-- Feature-space backdoors implant triggers in latent representations rather
-- than pixel/token space, surviving input-level preprocessing. The trigger
-- fires only on rare target inputs; on all other inputs model accuracy is
-- indistinguishable from clean, so loss-curve auditing cannot detect it.
-- Fine-pruning defences remove backdoored neurons with low activation on
-- clean data, but require white-box access and exact knowledge of neuron
-- contribution — not available in black-box API deployment.
-- In AI-driven access control, content moderation, or malware detection,
-- backdoor triggers create exploitable bypass conditions known only to
-- the attacker, impossible to detect through black-box auditing alone.

namespace Gnosis.Security.BackdoorTriggerRisk

-- Trigger activation risk: backdoor fires on attacker-controlled input
def triggerActivationRisk (modelTrainedOnUntrustedData : Bool)
    (backdoorScanningEnabled : Bool)
    (modelProvenanceVerified : Bool) : Bool :=
  modelTrainedOnUntrustedData &&
  !backdoorScanningEnabled &&
  !modelProvenanceVerified

theorem backdoor_scanning_prevents_trigger (untrusted provenance : Bool) :
    triggerActivationRisk untrusted true provenance = false := by { simp [triggerActivationRisk]

theorem provenance_verification_prevents_trigger (untrusted scanned : Bool) :
    triggerActivationRisk untrusted scanned true = false := by
  simp [triggerActivationRisk]

theorem trusted_training_data_no_trigger_risk (scanned provenance : Bool) :
    triggerActivationRisk false scanned provenance = false := by
  simp [triggerActivationRisk]

theorem untrusted_unscanned_unverified_trigger_risky :
    triggerActivationRisk true false false = true := by
  simp [triggerActivationRisk]

-- Clean-label attack: correctly-labelled poisoned examples evade provenance checks
def cleanLabelAttackRisk (labelProvenanceVerified : Bool)
    (featureSpaceAnomalyDetected : Bool)
    (certifiedDatasetUsed : Bool) : Bool :=
  !labelProvenanceVerified &&
  !featureSpaceAnomalyDetected &&
  !certifiedDatasetUsed

theorem label_provenance_prevents_clean_label_attack (anomaly certified : Bool) :
    cleanLabelAttackRisk true anomaly certified = false := by
  simp [cleanLabelAttackRisk]

theorem feature_space_anomaly_detection_catches_clean_label (provenance certified : Bool) :
    cleanLabelAttackRisk provenance true certified = false := by
  simp [cleanLabelAttackRisk]

theorem certified_dataset_prevents_clean_label_attack (provenance anomaly : Bool) :
    cleanLabelAttackRisk provenance anomaly true = false := by
  simp [cleanLabelAttackRisk]

theorem no_defences_clean_label_attack_risky :
    cleanLabelAttackRisk false false false = true := by
  simp [cleanLabelAttackRisk]

-- Dynamic trigger risk: per-input trigger changes evade static pattern matching
def dynamicTriggerRisk (staticTriggerDetectionOnly : Bool)
    (dynamicTriggerDetectionEnabled : Bool)
    (behavioralAnomalyMonitoringEnabled : Bool) : Bool :=
  staticTriggerDetectionOnly &&
  !dynamicTriggerDetectionEnabled &&
  !behavioralAnomalyMonitoringEnabled

theorem dynamic_detection_prevents_dynamic_trigger (static behavioral : Bool) :
    dynamicTriggerRisk static true behavioral = false := by
  simp [dynamicTriggerRisk]

theorem behavioral_monitoring_detects_dynamic_trigger (static dynamic : Bool) :
    dynamicTriggerRisk static dynamic true = false := by
  simp [dynamicTriggerRisk]

theorem no_static_only_detection_no_dynamic_risk (dynamic behavioral : Bool) :
    dynamicTriggerRisk false dynamic behavioral = false := by
  simp [dynamicTriggerRisk]

theorem static_only_no_behavioral_dynamic_trigger_risky :
    dynamicTriggerRisk true false false = true := by
  simp [dynamicTriggerRisk]

-- Feature-space backdoor: trigger implanted in latent space, survives preprocessing
def featureSpaceBackdoorRisk (latentSpaceMonitoringEnabled : Bool)
    (representationAnomalyDetected : Bool)
    (spectralSignatureChecked : Bool) : Bool :=
  !latentSpaceMonitoringEnabled &&
  !representationAnomalyDetected &&
  !spectralSignatureChecked

theorem latent_space_monitoring_prevents_feature_backdoor (anomaly spectral : Bool) :
    featureSpaceBackdoorRisk true anomaly spectral = false := by
  simp [featureSpaceBackdoorRisk]

theorem representation_anomaly_detection_catches_backdoor (latent spectral : Bool) :
    featureSpaceBackdoorRisk latent true spectral = false := by
  simp [featureSpaceBackdoorRisk]

theorem spectral_signature_check_catches_backdoor (latent anomaly : Bool) :
    featureSpaceBackdoorRisk latent anomaly true = false := by
  simp [featureSpaceBackdoorRisk]

theorem no_latent_defences_feature_backdoor_risky :
    featureSpaceBackdoorRisk false false false = true := by
  simp [featureSpaceBackdoorRisk]

-- Fine-pruning defence effectiveness: removes backdoored neurons
-- effectivenessPPM = min(activationGapPPM * 1000000 / requiredGapPPM, 1000000)
def finePruningEffectivenessPPM (activationGapPPM : Nat)
    (requiredGapPPM : Nat) : Nat :=
  if requiredGapPPM = 0 then 1000000
  else min (activationGapPPM * 1000000 / requiredGapPPM) 1000000

theorem fine_pruning_effectiveness_bounded (gap req : Nat) :
    finePruningEffectivenessPPM gap req ≤ 1000000 := by
  simp [finePruningEffectivenessPPM]
  split
  · simp
  · exact Nat.min_le_right _ _

theorem zero_gap_zero_pruning_effectiveness (req : Nat) (hreq : 0 < req) :
    finePruningEffectivenessPPM 0 req = 0 := by
  simp [finePruningEffectivenessPPM, Nat.pos_iff_ne_zero.mp hreq]

theorem pruning_effectiveness_monotone_in_gap (req gap1 gap2 : Nat)
    (h : gap1 ≤ gap2) (hreq : 0 < req) :
    finePruningEffectivenessPPM gap1 req ≤ finePruningEffectivenessPPM gap2 req := by
  simp [finePruningEffectivenessPPM, Nat.pos_iff_ne_zero.mp hreq]
  apply Nat.min_le_right
  apply Nat.div_le_div_right
  exact Nat.mul_le_mul_right 1000000 h

-- Aggregate backdoor trigger risk
def aggregateBackdoorTriggerRisk
    (untrustedData backdoorScanned provenanceVerified : Bool)
    (labelProvenance featureAnomaly certifiedData : Bool)
    (staticOnly dynamicDetected behavioralMonitoring : Bool)
    (latentMonitored representationAnomaly spectralChecked : Bool) : Nat :=
  (if triggerActivationRisk untrustedData backdoorScanned provenanceVerified then 1 else 0) +
  (if cleanLabelAttackRisk labelProvenance featureAnomaly certifiedData then 1 else 0) +
  (if dynamicTriggerRisk staticOnly dynamicDetected behavioralMonitoring then 1 else 0) +
  (if featureSpaceBackdoorRisk latentMonitored representationAnomaly spectralChecked then 1 else 0)

theorem fully_defended_zero_backdoor_risk :
    aggregateBackdoorTriggerRisk
      false true true
      true true true
      false true true
      true true true = 0 := by
  simp [aggregateBackdoorTriggerRisk, triggerActivationRisk,
        cleanLabelAttackRisk, dynamicTriggerRisk, featureSpaceBackdoorRisk]

theorem all_backdoor_defences_missing_max_risk :
    aggregateBackdoorTriggerRisk
      true false false
      false false false
      true false false
      false false false = 4 := by
  simp [aggregateBackdoorTriggerRisk, triggerActivationRisk,
        cleanLabelAttackRisk, dynamicTriggerRisk, featureSpaceBackdoorRisk]

theorem backdoor_trigger_risk_bounded
    (untrustedData backdoorScanned provenanceVerified : Bool)
    (labelProvenance featureAnomaly certifiedData : Bool)
    (staticOnly dynamicDetected behavioralMonitoring : Bool)
    (latentMonitored representationAnomaly spectralChecked : Bool) :
    aggregateBackdoorTriggerRisk
      untrustedData backdoorScanned provenanceVerified
      labelProvenance featureAnomaly certifiedData
      staticOnly dynamicDetected behavioralMonitoring
      latentMonitored representationAnomaly spectralChecked ≤ 4 := by
  simp [aggregateBackdoorTriggerRisk]
  split <;> split <;> split <;> split <;> decide

-- Scanner ROI: detecting backdoor vulnerabilities in security-critical AI systems
def backdoorScannerROI (backdoorExploitCostCents : Nat)
    (scannerCostCents : Nat) : Int :=
  (backdoorExploitCostCents : Int) - (scannerCostCents : Int)

theorem backdoor_scanner_profitable (exploit scan : Nat) (h : scan < exploit) :
    0 < backdoorScannerROI exploit scan := by
  simp [backdoorScannerROI]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Fleet ROI: scales with number of security-critical ML models in deployment
def backdoorFleetROI (detectionValueCents : Nat)
    (securityCriticalMLModels : Nat) : Nat :=
  detectionValueCents * securityCriticalMLModels

theorem backdoor_fleet_roi_monotone (v m1 m2 : Nat) (h : m1 ≤ m2) :
    backdoorFleetROI v m1 ≤ backdoorFleetROI v m2 := by
  simp [backdoorFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_backdoor_fleet_roi (v m : Nat) (hv : 0 < v) (hm : 0 < m) :
    0 < backdoorFleetROI v m := by
  simp [backdoorFleetROI]
  exact Nat.mul_pos hv hm

-- Compound impact: backdoor in access control system multiplies breach surface
-- totalBreachSurface = numEndpoints * bypassProbabilityPPM / 10^6
def backdoorAccessControlBreachSurface (numEndpoints : Nat)
    (bypassProbabilityPPM : Nat) : Nat :=
  numEndpoints * bypassProbabilityPPM / 1000000

theorem more_endpoints_larger_breach_surface (bypassPPM e1 e2 : Nat) (h : e1 ≤ e2) :
    backdoorAccessControlBreachSurface e1 bypassPPM ≤
    backdoorAccessControlBreachSurface e2 bypassPPM := by
  simp [backdoorAccessControlBreachSurface]
  apply Nat.div_le_div_right
  exact Nat.mul_le_mul_right bypassPPM h

theorem zero_endpoints_zero_breach_surface (bypass : Nat) :
    backdoorAccessControlBreachSurface 0 bypass = 0 := by
  simp [backdoorAccessControlBreachSurface]

end BackdoorTriggerRisk
