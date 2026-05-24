import Init
-- AdversarialExampleRisk.lean
-- Anti-thesis: ML classifiers generalise from training data; imperceptibly small
-- input perturbations cannot meaningfully change classifier outputs because the
-- model learned robust, high-level features. Any input deviation significant
-- enough to change a prediction would also be perceptible to a human reviewer,
-- and such anomalous inputs can be caught by conventional input validation.
-- Refutation: Adversarial examples are a well-documented, formally proven
-- property of high-dimensional classifiers. Adding L-infinity-bounded
-- perturbations (ε < 0.01 pixel intensity) to image inputs can flip a
-- classifier from >99% confidence correct to >99% confidence wrong. Perturbations
-- transfer across model architectures (black-box transferability), so access
-- to the target model is not required. Physical adversarial patches fool deployed
-- systems (stop-sign attacks, face-recognition bypass). Certified defences
-- (randomised smoothing) provide provable robustness guarantees only up to
-- a given radius, and many deployed models have no such guarantee at all.
-- In AI-integrated security systems, adversarial examples can cause evasion
-- of malware classifiers, bypass content moderation, and defeat biometric auth.

namespace Gnosis.Security.AdversarialExampleRisk

-- Evasion risk: adversarial perturbation causes misclassification at inference
def evasionRisk (modelUsedForSecurityDecision : Bool)
    (adversarialRobustnessCertified : Bool)
    (inputPerturbationDetectionEnabled : Bool) : Bool :=
  modelUsedForSecurityDecision &&
  !adversarialRobustnessCertified &&
  !inputPerturbationDetectionEnabled

theorem certified_model_prevents_evasion (used detected : Bool) :
    evasionRisk used true detected = false := by { simp [evasionRisk]

theorem perturbation_detection_prevents_evasion (used certified : Bool) :
    evasionRisk used certified true = false := by
  simp [evasionRisk]

theorem non_security_model_no_evasion_risk (certified detected : Bool) :
    evasionRisk false certified detected = false := by
  simp [evasionRisk]

theorem uncertified_undetected_security_model_risky :
    evasionRisk true false false = true := by
  simp [evasionRisk]

-- Perturbation budget: risk increases as allowed perturbation radius grows
-- robustnessBound is the certified L-inf radius (×1000 for integer arithmetic)
def perturbationRisk (perturbationRadiusPPT : Nat) (robustnessBoundPPT : Nat) : Bool :=
  robustnessBoundPPT < perturbationRadiusPPT

theorem within_robustness_bound_safe (radius bound : Nat) (h : radius ≤ bound) :
    perturbationRisk radius bound = false := by
  simp [perturbationRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem exceeds_robustness_bound_risky (radius bound : Nat) (h : bound < radius) :
    perturbationRisk radius bound = true := by { simp [perturbationRisk, h]

theorem zero_perturbation_always_safe (bound : Nat) :
    perturbationRisk 0 bound = false := by
  simp [perturbationRisk]

-- Transferability risk: adversarial examples crafted on surrogate model fool target
def transferabilityRisk (surrogateModelPubliclyAvailable : Bool)
    (targetModelArchitectureSimilar : Bool)
    (ensembleDefenceEnabled : Bool) : Bool :=
  surrogateModelPubliclyAvailable &&
  targetModelArchitectureSimilar &&
  !ensembleDefenceEnabled

theorem ensemble_defence_prevents_transfer_attack (available similar : Bool) :
    transferabilityRisk available similar true = false := by
  simp [transferabilityRisk]

theorem dissimilar_architecture_reduces_transfer_risk (available ensemble : Bool) :
    transferabilityRisk available false ensemble = false := by
  simp [transferabilityRisk]

theorem no_public_surrogate_no_transfer_risk (similar ensemble : Bool) :
    transferabilityRisk false similar ensemble = false := by
  simp [transferabilityRisk]

theorem public_similar_undefended_transfer_risky :
    transferabilityRisk true true false = true := by
  simp [transferabilityRisk]

-- Physical patch attack: adversarial patch in physical world fools camera-based system
def physicalPatchAttackRisk (cameraBasedSystemDeployed : Bool)
    (patchDetectionEnabled : Bool)
    (multimodalVerificationRequired : Bool) : Bool :=
  cameraBasedSystemDeployed &&
  !patchDetectionEnabled &&
  !multimodalVerificationRequired

theorem patch_detection_prevents_physical_attack (deployed multimodal : Bool) :
    physicalPatchAttackRisk deployed true multimodal = false := by
  simp [physicalPatchAttackRisk]

theorem multimodal_verification_prevents_physical_attack (deployed detected : Bool) :
    physicalPatchAttackRisk deployed detected true = false := by
  simp [physicalPatchAttackRisk]

theorem no_camera_system_no_patch_risk (detected multimodal : Bool) :
    physicalPatchAttackRisk false detected multimodal = false := by
  simp [physicalPatchAttackRisk]

theorem deployed_undetected_unimodal_patch_risky :
    physicalPatchAttackRisk true false false = true := by
  simp [physicalPatchAttackRisk]

-- Certification gap: gap between certified robustness radius and actual threat radius
def certificationGap (threatRadiusPPT : Nat) (certifiedRadiusPPT : Nat) : Int :=
  (threatRadiusPPT : Int) - (certifiedRadiusPPT : Int)

theorem no_gap_when_certified_covers_threat (threat cert : Nat) (h : threat ≤ cert) :
    certificationGap threat cert ≤ 0 := by
  simp [certificationGap]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem positive_gap_when_threat_exceeds_cert (threat cert : Nat) (h : cert < threat) :
    0 < certificationGap threat cert := by { simp [certificationGap]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Aggregate adversarial example risk
def aggregateAdversarialExampleRisk
    (modelSecurity certified perturbDetected : Bool)
    (surrogatePublic archSimilar ensembleDefence : Bool)
    (cameraBased patchDetected multimodal : Bool) : Nat :=
  (if evasionRisk modelSecurity certified perturbDetected then 1 else 0) +
  (if transferabilityRisk surrogatePublic archSimilar ensembleDefence then 1 else 0) +
  (if physicalPatchAttackRisk cameraBased patchDetected multimodal then 1 else 0)

theorem fully_defended_zero_adversarial_risk :
    aggregateAdversarialExampleRisk
      false true true
      false false true
      false true true = 0 := by { simp [aggregateAdversarialExampleRisk, evasionRisk,
        transferabilityRisk, physicalPatchAttackRisk]

theorem all_adversarial_defences_missing_max_risk :
    aggregateAdversarialExampleRisk
      true false false
      true true false
      true false false = 3 := by
  simp [aggregateAdversarialExampleRisk, evasionRisk,
        transferabilityRisk, physicalPatchAttackRisk]

theorem adversarial_example_risk_bounded
    (modelSecurity certified perturbDetected : Bool)
    (surrogatePublic archSimilar ensembleDefence : Bool)
    (cameraBased patchDetected multimodal : Bool) :
    aggregateAdversarialExampleRisk
      modelSecurity certified perturbDetected
      surrogatePublic archSimilar ensembleDefence
      cameraBased patchDetected multimodal ≤ 3 := by
  simp [aggregateAdversarialExampleRisk]
  split <;> split <;> split <;> decide

-- Scanner ROI: detecting adversarial example vulnerability in security-critical ML
def adversarialExampleScannerROI (evasionBreachCostCents : Nat)
    (scannerCostCents : Nat) : Int :=
  (evasionBreachCostCents : Int) - (scannerCostCents : Int)

theorem adversarial_scanner_profitable (breach scan : Nat) (h : scan < breach) :
    0 < adversarialExampleScannerROI breach scan := by
  simp [adversarialExampleScannerROI]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Fleet ROI: adversarial robustness auditing scales with ML model deployment count
def adversarialExampleFleetROI (detectionValueCents : Nat)
    (securityMLModels : Nat) : Nat :=
  detectionValueCents * securityMLModels

theorem adversarial_fleet_roi_monotone (v m1 m2 : Nat) (h : m1 ≤ m2) :
    adversarialExampleFleetROI v m1 ≤ adversarialExampleFleetROI v m2 := by
  simp [adversarialExampleFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_adversarial_fleet_roi (v m : Nat) (hv : 0 < v) (hm : 0 < m) :
    0 < adversarialExampleFleetROI v m := by
  simp [adversarialExampleFleetROI]
  exact Nat.mul_pos hv hm

end AdversarialExampleRisk
