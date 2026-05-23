import Gnosis.ComprehensiveAnatomy
import Gnosis.ThothMotorControl
import Gnosis.Real
import Gnosis.PhysiologicalParameters
import Gnosis.GnosisTimeClock
import Gnosis.Body.MetabolismSystem
import Gnosis.Body.EndocrineSystem
import Gnosis.Body.AutonomicNervousSystem
import Mathlib.Data.Real.Basic

namespace Gnosis
namespace InteroceptiveSystem

/-!
  # Interoceptive System - Internal State Monitoring
  
  Mathematical formalization of internal bodily sensations, homeostatic
  monitoring, visceral feedback, and internal state awareness for the
  autonomous human system.
-/

/-- Visceral and organ sensations -/
structure VisceralSensations where
  heartbeat : BuleReal          -- Heartbeat awareness (0.0 to 1.0)
  respiration : BuleReal        -- Breathing awareness
  digestion : BuleReal         -- Digestive sensations
  bladderFullness : BuleReal    -- Bladder fullness signal
  bowelPressure : BuleReal      -- Bowel pressure signal
  hunger : BuleReal             -- Hunger sensation intensity
  thirst : BuleReal             -- Thirst sensation intensity
  nausea : BuleReal             -- Nausea/discomfort signal
  deriving Repr

/-- Homeostatic monitoring and regulation -/
structure HomeostaticMonitoring where
  coreTemperature : BuleReal    -- Internal temperature sensing
  bloodPressure : BuleReal      -- Blood pressure awareness
  bloodGlucose : BuleReal       -- Blood glucose sensing
  oxygenLevel : BuleReal        -- Blood oxygen awareness
  phBalance : BuleReal          -- Blood pH sensing
  electrolyteBalance : BuleReal  -- Electrolyte balance awareness
  hormoneLevels : BuleReal       -- Hormone level awareness
  immuneStatus : BuleReal        -- Immune system status awareness
  deriving Repr

/-- Pain and discomfort monitoring -/
structure PainMonitoring where
  visceralPain : BuleReal       -- Internal organ pain
  muscularPain : BuleReal       -- Muscle soreness/strain
  headacheIntensity : BuleReal   -- Head pain intensity
  jointPain : BuleReal          -- Joint discomfort
  nervePain : BuleReal          -- Neuropathic pain
  inflammatoryPain : BuleReal    -- Inflammation-related pain
  painThreshold : BuleReal      -- Pain sensitivity threshold
  painTolerance : BuleReal      -- Pain tolerance level
  deriving Repr

/-- Emotional and affective interoception -/
structure EmotionalInteroception where
  anxietySignals : BuleReal     -- Anxiety-related bodily signals
  angerSignals : BuleReal       -- Anger-related bodily signals
  fearSignals : BuleReal        -- Fear-related bodily signals
  sadnessSignals : BuleReal     -- Sadness-related bodily signals
  joySignals : BuleReal         -- Joy-related bodily signals
  stressSignals : BuleReal       -- Stress-related bodily signals
  emotionalAwareness : BuleReal -- Overall emotional body awareness
  bodyEmotionConnection : BuleReal -- Body-emotion integration
  deriving Repr

/-- Energy and fatigue monitoring -/
structure EnergyMonitoring where
  physicalFatigue : BuleReal     -- Physical exhaustion level
  mentalFatigue : BuleReal       -- Mental exhaustion level
  energyAvailability : BuleReal  -- Available energy perception
  recoveryNeed : BuleReal        -- Need for rest/recovery
  overexertionRisk : BuleReal    -- Risk of overexertion
  staminaLevel : BuleReal        -- Current stamina perception
  exhaustionSignals : BuleReal   -- Exhaustion warning signals
  restorativeSignals : BuleReal   -- Recovery/rest signals
  deriving Repr

/-- Interoceptive awareness and integration -/
structure InteroceptiveAwareness where
  bodyScanAccuracy : BuleReal    -- Accuracy of body state detection
  signalClarity : BuleReal        -- Clarity of interoceptive signals
  attentionToBody : BuleReal      -- Attention directed to internal states
  interpretationAccuracy : BuleReal -- Accuracy of signal interpretation
  predictionAccuracy : BuleReal   -- Ability to predict bodily needs
  regulatoryControl : BuleReal     -- Ability to regulate based on signals
  mindBodyConnection : BuleReal   -- Overall mind-body integration
  interoceptiveLearning : BuleReal -- Learning from bodily signals
  deriving Repr

/-- Interoceptive system evidence for Thoth framework -/
structure InteroceptiveEvidence where
  visceralSensations : VisceralSensations
  homeostaticMonitoring : HomeostaticMonitoring
  painMonitoring : PainMonitoring
  emotionalInteroception : EmotionalInteroception
  energyMonitoring : EnergyMonitoring
  interoceptiveAwareness : InteroceptiveAwareness
  parameters : PhysiologicalParameters.InteroceptiveParams
  overallInteroception : BuleReal  -- 0.0 to 1.0, interoceptive system health
  timestamp : BuleReal
  claimsAuthority : Bool := false
  deriving Repr

/-! # Visceral Sensation Functions -/

/-- Update visceral sensations based on internal states -/
def updateVisceralSensations 
    (previousSensations : VisceralSensations)
    (cardiovascularState : BuleReal)
    (respiratoryState : BuleReal)
    (digestiveState : BuleReal)
    (hydrationLevel : BuleReal)
    (params : PhysiologicalParameters.InteroceptiveParams) : VisceralSensations := by
  -- Heartbeat awareness (interoceptive heartbeat detection)
  let heartbeatSignal := cardiovascularState * params.heartbeatDetectionThreshold
  let newHeartbeat := if heartbeatSignal <= BuleReal.one then heartbeatSignal else BuleReal.one
  
  -- Respiration awareness
  let respirationSignal := respiratoryState * params.respirationDetectionThreshold
  let newRespiration := if respirationSignal <= BuleReal.one then respirationSignal else BuleReal.one
  
  -- Digestive sensations
  let digestiveSignal := digestiveState * params.digestionDetectionThreshold
  let newDigestion := if digestiveSignal <= BuleReal.one then digestiveSignal else BuleReal.one
  
  -- Bladder fullness (accumulates over time)
  let bladderAccumulation := BuleReal.ofNat 1 / BuleReal.ofNat 100  -- 1% per time unit
  let newBladderFullness := if previousSensations.bladderFullness + bladderAccumulation <= BuleReal.one 
                           then previousSensations.bladderFullness + bladderAccumulation 
                           else BuleReal.one
  
  -- Bowel pressure
  let bowelSignal := digestiveState * BuleReal.ofNat 4 / BuleReal.ofNat 10
  let newBowelPressure := if bowelSignal <= BuleReal.one then bowelSignal else BuleReal.one
  
  -- Hunger (based on energy state and time)
  let hungerSignal := if cardiovascularState < BuleReal.ofNat 5 / BuleReal.ofNat 10 then
                     BuleReal.ofNat 8 / BuleReal.ofNat 10
                   else
                     BuleReal.ofNat 3 / BuleReal.ofNat 10
  let newHunger := if hungerSignal <= BuleReal.one then hungerSignal else BuleReal.one
  
  -- Thirst (based on hydration)
  let thirstSignal := if BuleReal.one - hydrationLevel >= BuleReal.zero then BuleReal.one - hydrationLevel else BuleReal.zero
  let newThirst := if thirstSignal <= BuleReal.one then thirstSignal else BuleReal.one
  
  -- Nausea (from digestive distress)
  let nauseaSignal := if digestiveState > BuleReal.ofNat 8 / BuleReal.ofNat 10 then
                     BuleReal.ofNat 6 / BuleReal.ofNat 10
                   else
                     BuleReal.zero
  let newNausea := if nauseaSignal <= BuleReal.one then nauseaSignal else BuleReal.one
  
  exact {
    heartbeat := newHeartbeat,
    respiration := newRespiration,
    digestion := newDigestion,
    bladderFullness := newBladderFullness,
    bowelPressure := newBowelPressure,
    hunger := newHunger,
    thirst := newThirst,
    nausea := newNausea
  }

/-! # Homeostatic Monitoring Functions -/

/-- Update homeostatic monitoring systems -/
def updateHomeostaticMonitoring 
    (previousMonitoring : HomeostaticMonitoring)
    (metabolicState : MetabolismSystem.EnergyState)
    (cardiovascularState : BuleReal)
    (respiratoryState : BuleReal) : HomeostaticMonitoring => by
  -- Core temperature sensing
  let temperatureDeviation := Float.abs (metabolicState.thermalState.coreTemperature - BuleReal.ofNat 37)
  let newCoreTemperature := Float.min (temperatureDeviation / BuleReal.ofNat 5) BuleReal.one
  
  -- Blood pressure awareness
  let pressureDeviation := Float.abs (cardiovascularState - BuleReal.ofNat 70)  -- Deviation from normal HR
  let newBloodPressure := Float.min (pressureDeviation / BuleReal.ofNat 30) BuleReal.one
  
  -- Blood glucose sensing
  let glucoseDeviation := Float.abs (metabolicState.nutrientPool.glucose - BuleReal.ofNat 90)
  let newBloodGlucose := Float.min (glucoseDeviation / BuleReal.ofNat 40) BuleReal.one
  
  -- Oxygen level awareness
  let oxygenDeviation := Float.abs (respiratoryState - BuleReal.ofNat 98)  -- Deviation from 98% saturation
  let newOxygenLevel := Float.min (oxygenDeviation / BuleReal.ofNat 10) BuleReal.one
  
  -- pH balance sensing
  let phDeviation := Float.abs (BuleReal.ofNat 74 - BuleReal.ofNat 74)  -- Simplified: normal pH
  let newPhBalance := Float.min (phDeviation / BuleReal.ofNat 2) BuleReal.one
  
  -- Electrolyte balance awareness
  let electrolyteSignal := BuleReal.ofNat 1 / BuleReal.ofNat 10  -- 10% deviation signal
  let newElectrolyteBalance := electrolyteSignal
  
  -- Hormone level awareness
  let hormoneSignal := BuleReal.ofNat 2 / BuleReal.ofNat 10  -- 20% awareness of hormonal changes
  let newHormoneLevels := hormoneSignal
  
  -- Immune status awareness
  let immuneSignal := BuleReal.ofNat 15 / BuleReal.ofNat 100  -- 15% awareness of immune activity
  let newImmuneStatus := immuneSignal
  
  exact {
    coreTemperature := newCoreTemperature,
    bloodPressure := newBloodPressure,
    bloodGlucose := newBloodGlucose,
    oxygenLevel := newOxygenLevel,
    phBalance := newPhBalance,
    electrolyteBalance := newElectrolyteBalance,
    hormoneLevels := newHormoneLevels,
    immuneStatus := newImmuneStatus
  }

/-! # Pain Monitoring Functions -/

/-- Update pain monitoring systems -/
def updatePainMonitoring 
    (previousPain : PainMonitoring)
    (injurySignals : BuleReal)
    (inflammationLevel : BuleReal)
    (physicalStrain : BuleReal) : PainMonitoring => by
  -- Visceral pain (internal organs)
  let visceralPainSignal := injurySignals * BuleReal.ofNat 3 / BuleReal.ofNat 10
  let newVisceralPain := Float.min visceralPainSignal BuleReal.one
  
  -- Muscular pain (exercise, strain)
  let muscularPainSignal := physicalStrain * BuleReal.ofNat 7 / BuleReal.ofNat 10
  let newMuscularPain := Float.min muscularPainSignal BuleReal.one
  
  -- Headache intensity (stress, tension)
  let headacheSignal := injurySignals * BuleReal.ofNat 4 / BuleReal.ofNat 10
  let newHeadacheIntensity := Float.min headacheSignal BuleReal.one
  
  -- Joint pain (movement, inflammation)
  let jointPainSignal := inflammationLevel * BuleReal.ofNat 5 / BuleReal.ofNat 10
  let newJointPain := Float.min jointPainSignal BuleReal.one
  
  -- Nerve pain (neuropathic)
  let nervePainSignal := injurySignals * BuleReal.ofNat 2 / BuleReal.ofNat 10
  let newNervePain := Float.min nervePainSignal BuleReal.one
  
  -- Inflammatory pain
  let inflammatoryPainSignal := inflammationLevel * BuleReal.ofNat 8 / BuleReal.ofNat 10
  let newInflammatoryPain := Float.min inflammatoryPainSignal BuleReal.one
  
  -- Pain threshold (sensitivity to pain)
  let newPainThreshold := previousPain.painThreshold * BuleReal.ofNat 95 / BuleReal.ofNat 100  -- Slight adaptation
  
  -- Pain tolerance (ability to withstand pain)
  let newPainTolerance := Float.min (previousPain.painTolerance + BuleReal.ofNat 1 / BuleReal.ofNat 100) BuleReal.ofNat 9 / BuleReal.ofNat 10
  
  exact {
    visceralPain := newVisceralPain,
    muscularPain := newMuscularPain,
    headacheIntensity := newHeadacheIntensity,
    jointPain := newJointPain,
    nervePain := newNervePain,
    inflammatoryPain := newInflammatoryPain,
    painThreshold := newPainThreshold,
    painTolerance := newPainTolerance
  }

/-! # Emotional Interoception Functions -/

/-- Update emotional interoceptive signals -/
def updateEmotionalInteroception 
    (previousEmotional : EmotionalInteroception)
    (autonomicState : AutonomicNervousSystem.AutonomicBalance)
    (stressLevel : BuleReal)
    (emotionalState : BuleReal) : EmotionalInteroception => by
  -- Anxiety signals (increased heart rate, breathing)
  let anxietySignals := autonomicState.sympatheticDominance * stressLevel * BuleReal.ofNat 8 / BuleReal.ofNat 10
  let newAnxietySignals := Float.min anxietySignals BuleReal.one
  
  -- Anger signals (high arousal, tension)
  let angerSignals := emotionalState * autonomicState.sympatheticDominance * BuleReal.ofNat 7 / BuleReal.ofNat 10
  let newAngerSignals := Float.min angerSignals BuleReal.one
  
  -- Fear signals (threat response)
  let fearSignals := stressLevel * autonomicState.sympatheticDominance * BuleReal.ofNat 9 / BuleReal.ofNat 10
  let newFearSignals := Float.min fearSignals BuleReal.one
  
  -- Sadness signals (low arousal, heaviness)
  let sadnessSignals := (BuleReal.one - emotionalState) * (BuleReal.one - autonomicState.sympatheticDominance) * BuleReal.ofNat 6 / BuleReal.ofNat 10
  let newSadnessSignals := Float.min sadnessSignals BuleReal.one
  
  -- Joy signals (moderate arousal, relaxation)
  let joySignals := emotionalState * autonomicState.vagalTone * BuleReal.ofNat 8 / BuleReal.ofNat 10
  let newJoySignals := Float.min joySignals BuleReal.one
  
  -- Stress signals (overall stress response)
  let newStressSignals := stressLevel
  
  -- Emotional awareness
  let emotionalFactors := (newAnxietySignals + newAngerSignals + newFearSignals + newSadnessSignals + newJoySignals) / BuleReal.ofNat 5
  let newEmotionalAwareness := emotionalFactors
  
  -- Body-emotion connection
  let bodyEmotionConnection := (autonomicState.sympatheticDominance + autonomicState.vagalTone) / BuleReal.ofNat 2
  let newBodyEmotionConnection := bodyEmotionConnection
  
  exact {
    anxietySignals := newAnxietySignals,
    angerSignals := newAngerSignals,
    fearSignals := newFearSignals,
    sadnessSignals := newSadnessSignals,
    joySignals := newJoySignals,
    stressSignals := newStressSignals,
    emotionalAwareness := newEmotionalAwareness,
    bodyEmotionConnection := newBodyEmotionConnection
  }

/-! # Energy Monitoring Functions -/

/-- Update energy and fatigue monitoring -/
def updateEnergyMonitoring 
    (previousEnergy : EnergyMonitoring)
    (metabolicState : MetabolismSystem.EnergyState)
    (physicalActivity : BuleReal)
    (mentalActivity : BuleReal) : EnergyMonitoring => by
  -- Physical fatigue
  let physicalFatigueSignal := (BuleReal.one - metabolicState.energyState.atpLevel) * physicalActivity
  let newPhysicalFatigue := Float.min physicalFatigueSignal BuleReal.one
  
  -- Mental fatigue
  let mentalFatigueSignal := metabolicState.fatigueState.mentalFatigue * mentalActivity
  let newMentalFatigue := Float.min mentalFatigueSignal BuleReal.one
  
  -- Energy availability perception
  let energyAvailabilitySignal := metabolicState.energyState.atpLevel
  let newEnergyAvailability := energyAvailabilitySignal
  
  -- Recovery need
  let recoveryNeedSignal := (newPhysicalFatigue + newMentalFatigue) / BuleReal.ofNat 2
  let newRecoveryNeed := Float.min recoveryNeedSignal BuleReal.one
  
  -- Overexertion risk
  let overexertionSignal := if physicalActivity > BuleReal.ofNat 8 / BuleReal.ofNat 10 && newPhysicalFatigue > BuleReal.ofNat 7 / BuleReal.ofNat 10 then
                          BuleReal.ofNat 8 / BuleReal.ofNat 10
                        else
                          BuleReal.ofNat 3 / BuleReal.ofNat 10
  let newOverexertionRisk := overexertionSignal
  
  -- Stamina level
  let staminaSignal := BuleReal.one - (newPhysicalFatigue + newMentalFatigue) / BuleReal.ofNat 2
  let newStaminaLevel := Float.max staminaSignal BuleReal.ofNat 2 / BuleReal.ofNat 10
  
  -- Exhaustion signals
  let exhaustionSignal := if newPhysicalFatigue > BuleReal.ofNat 9 / BuleReal.ofNat 10 || newMentalFatigue > BuleReal.ofNat 9 / BuleReal.ofNat 10 then
                       BuleReal.ofNat 9 / BuleReal.ofNat 10
                     else
                       BuleReal.ofNat 2 / BuleReal.ofNat 10
  let newExhaustionSignals := exhaustionSignal
  
  -- Restorative signals
  let restorativeSignal := if newRecoveryNeed > BuleReal.ofNat 7 / BuleReal.ofNat 10 then
                        BuleReal.ofNat 8 / BuleReal.ofNat 10
                      else
                        BuleReal.ofNat 3 / BuleReal.ofNat 10
  let newRestorativeSignals := restorativeSignal
  
  exact {
    physicalFatigue := newPhysicalFatigue,
    mentalFatigue := newMentalFatigue,
    energyAvailability := newEnergyAvailability,
    recoveryNeed := newRecoveryNeed,
    overexertionRisk := newOverexertionRisk,
    staminaLevel := newStaminaLevel,
    exhaustionSignals := newExhaustionSignals,
    restorativeSignals := newRestorativeSignals
  }

/-! # Interoceptive Awareness Functions -/

/-- Update overall interoceptive awareness -/
def updateInteroceptiveAwareness 
    (previousAwareness : InteroceptiveAwareness)
    (attentionLevel : BuleReal)
    (signalStrength : BuleReal)
    (learningExperience : BuleReal) : InteroceptiveAwareness => by
  -- Body scan accuracy
  let scanAccuracy := attentionLevel * signalStrength
  let newBodyScanAccuracy := Float.min scanAccuracy BuleReal.one
  
  -- Signal clarity
  let newSignalClarity := Float.min signalStrength BuleReal.one
  
  -- Attention to body
  let newAttentionToBody := Float.min attentionLevel BuleReal.one
  
  -- Interpretation accuracy
  let interpretationFactors := (newAttentionToBody + newSignalClarity) / BuleReal.ofNat 2
  let newInterpretationAccuracy := interpretationFactors
  
  -- Prediction accuracy
  let predictionFactors := (newBodyScanAccuracy + learningExperience) / BuleReal.ofNat 2
  let newPredictionAccuracy := Float.min predictionFactors BuleReal.one
  
  -- Regulatory control
  let controlFactors := (newInterpretationAccuracy + newAttentionToBody) / BuleReal.ofNat 2
  let newRegulatoryControl := Float.min controlFactors BuleReal.one
  
  -- Mind-body connection
  let mindBodyFactors := (newAttentionToBody + newInterpretationAccuracy + newRegulatoryControl) / BuleReal.ofNat 3
  let newMindBodyConnection := mindBodyFactors
  
  -- Interoceptive learning
  let learningRate := learningExperience * BuleReal.ofNat 1 / BuleReal.ofNat 10
  let newInteroceptiveLearning := Float.min (previousAwareness.interoceptiveLearning + learningRate) BuleReal.one
  
  exact {
    bodyScanAccuracy := newBodyScanAccuracy,
    signalClarity := newSignalClarity,
    attentionToBody := newAttentionToBody,
    interpretationAccuracy := newInterpretationAccuracy,
    predictionAccuracy := newPredictionAccuracy,
    regulatoryControl := newRegulatoryControl,
    mindBodyConnection := newMindBodyConnection,
    interoceptiveLearning := newInteroceptiveLearning
  }

/-! # System Integration -/

/-- Update complete interoceptive system -/
def updateInteroceptiveSystem 
    (previousEvidence : InteroceptiveEvidence)
    (metabolicState : MetabolismSystem.EnergyState)
    (autonomicState : AutonomicNervousSystem.AutonomicBalance)
    (physicalActivity : BuleReal)
    (mentalActivity : BuleReal)
    (attentionLevel : BuleReal)
    (timeStep : BuleReal) : InteroceptiveEvidence => by
  -- Update visceral sensations
  let newVisceralSensations := updateVisceralSensations 
    previousEvidence.visceralSensations 
    autonomicState.sympatheticDominance 
    (BuleReal.one - autonomicState.sympatheticDominance) 
    metabolicState.nutrientPool.hydration
  
  -- Update homeostatic monitoring
  let newHomeostaticMonitoring := updateHomeostaticMonitoring 
    previousEvidence.homeostaticMonitoring 
    metabolicState 
    autonomicState.sympatheticDominance 
    (BuleReal.one - autonomicState.sympatheticDominance)
  
  -- Update pain monitoring
  let injurySignals := BuleReal.ofNat 2 / BuleReal.ofNat 10  -- 20% injury signal
  let inflammationLevel := BuleReal.ofNat 1 / BuleReal.ofNat 10  -- 10% inflammation
  let newPainMonitoring := updatePainMonitoring 
    previousEvidence.painMonitoring 
    injurySignals 
    inflammationLevel 
    physicalActivity
  
  -- Update emotional interoception
  let stressLevel := autonomicState.allostaticLoad
  let emotionalState := BuleReal.ofNat 6 / BuleReal.ofNat 10  -- 60% positive emotional state
  let newEmotionalInteroception := updateEmotionalInteroception 
    previousEvidence.emotionalInteroception 
    autonomicState 
    stressLevel 
    emotionalState
  
  -- Update energy monitoring
  let newEnergyMonitoring := updateEnergyMonitoring 
    previousEvidence.energyMonitoring 
    metabolicState 
    physicalActivity 
    mentalActivity
  
  -- Update interoceptive awareness
  let signalStrength := (newVisceralSensations.heartbeat + newVisceralSensations.respiration + 
                       newHomeostaticMonitoring.coreTemperature + newEnergyMonitoring.physicalFatigue) / BuleReal.ofNat 4
  let learningExperience := BuleReal.ofNat 3 / BuleReal.ofNat 10  -- 30% learning experience
  let newInteroceptiveAwareness := updateInteroceptiveAwareness 
    previousEvidence.interoceptiveAwareness 
    attentionLevel 
    signalStrength 
    learningExperience
  
  -- Calculate overall interoceptive function
  let interoceptiveFactors := #[
    newVisceralSensations.heartbeat,
    newHomeostaticMonitoring.coreTemperature,
    newPainMonitoring.painThreshold,
    newEmotionalInteroception.emotionalAwareness,
    newEnergyMonitoring.energyAvailability,
    newInteroceptiveAwareness.mindBodyConnection
  ]
  let overallInteroception := interoceptiveFactors.foldl (λ sum factor => sum + factor) BuleReal.zero / BuleReal.ofNat 6
  
  exact {
    visceralSensations := newVisceralSensations,
    homeostaticMonitoring := newHomeostaticMonitoring,
    painMonitoring := newPainMonitoring,
    emotionalInteroception := newEmotionalInteroception,
    energyMonitoring := newEnergyMonitoring,
    interoceptiveAwareness := newInteroceptiveAwareness,
    parameters := previousEvidence.parameters,
    overallInteroception := overallInteroception,
    timestamp := previousEvidence.timestamp + timeStep
  }

/-! # Default System Initialization -/

/-- Initialize interoceptive system with default parameters -/
def initInteroceptiveSystem (params : PhysiologicalParameters.BodyCompositionParams) : InteroceptiveEvidence := by
  let initialVisceral := {
    heartbeat := BuleReal.ofNat 3 / BuleReal.ofNat 10,      -- 30% heartbeat awareness
    respiration := BuleReal.ofNat 4 / BuleReal.ofNat 10,    -- 40% breathing awareness
    digestion := BuleReal.ofNat 2 / BuleReal.ofNat 10,     -- 20% digestive awareness
    bladderFullness := BuleReal.zero,                     -- Empty bladder
    bowelPressure := BuleReal.zero,                       -- No bowel pressure
    hunger := BuleReal.ofNat 3 / BuleReal.ofNat 10,       -- 30% hunger
    thirst := BuleReal.ofNat 2 / BuleReal.ofNat 10,       -- 20% thirst
    nausea := BuleReal.zero                               -- No nausea
  }
  
  let initialHomeostatic := {
    coreTemperature := BuleReal.ofNat 1 / BuleReal.ofNat 10,  -- 10% temperature deviation awareness
    bloodPressure := BuleReal.ofNat 2 / BuleReal.ofNat 10,    -- 20% blood pressure awareness
    bloodGlucose := BuleReal.ofNat 15 / BuleReal.ofNat 100,   -- 15% glucose deviation awareness
    oxygenLevel := BuleReal.ofNat 5 / BuleReal.ofNat 100,     -- 5% oxygen deviation awareness
    phBalance := BuleReal.zero,                              -- No pH imbalance
    electrolyteBalance := BuleReal.ofNat 1 / BuleReal.ofNat 10, -- 10% electrolyte awareness
    hormoneLevels := BuleReal.ofNat 2 / BuleReal.ofNat 10,    -- 20% hormone awareness
    immuneStatus := BuleReal.ofNat 15 / BuleReal.ofNat 100    -- 15% immune awareness
  }
  
  let initialPain := {
    visceralPain := BuleReal.zero,           -- No visceral pain
    muscularPain := BuleReal.zero,           -- No muscular pain
    headacheIntensity := BuleReal.zero,      -- No headache
    jointPain := BuleReal.zero,              -- No joint pain
    nervePain := BuleReal.zero,              -- No nerve pain
    inflammatoryPain := BuleReal.zero,       -- No inflammatory pain
    painThreshold := BuleReal.ofNat 7 / BuleReal.ofNat 10, -- 70% pain threshold
    painTolerance := BuleReal.ofNat 8 / BuleReal.ofNat 10   -- 80% pain tolerance
  }
  
  let initialEmotional := {
    anxietySignals := BuleReal.ofNat 2 / BuleReal.ofNat 10,  -- 20% anxiety signals
    angerSignals := BuleReal.ofNat 1 / BuleReal.ofNat 10,    -- 10% anger signals
    fearSignals := BuleReal.ofNat 1 / BuleReal.ofNat 10,     -- 10% fear signals
    sadnessSignals := BuleReal.ofNat 1 / BuleReal.ofNat 10,   -- 10% sadness signals
    joySignals := BuleReal.ofNat 6 / BuleReal.ofNat 10,      -- 60% joy signals
    stressSignals := BuleReal.ofNat 3 / BuleReal.ofNat 10,    -- 30% stress signals
    emotionalAwareness := BuleReal.ofNat 6 / BuleReal.ofNat 10, -- 60% emotional awareness
    bodyEmotionConnection := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% body-emotion connection
  }
  
  let initialEnergy := {
    physicalFatigue := BuleReal.ofNat 2 / BuleReal.ofNat 10,  -- 20% physical fatigue
    mentalFatigue := BuleReal.ofNat 3 / BuleReal.ofNat 10,    -- 30% mental fatigue
    energyAvailability := BuleReal.ofNat 8 / BuleReal.ofNat 10, -- 80% energy available
    recoveryNeed := BuleReal.ofNat 2 / BuleReal.ofNat 10,      -- 20% recovery need
    overexertionRisk := BuleReal.ofNat 1 / BuleReal.ofNat 10,  -- 10% overexertion risk
    staminaLevel := BuleReal.ofNat 8 / BuleReal.ofNat 10,       -- 80% stamina
    exhaustionSignals := BuleReal.zero,                      -- No exhaustion signals
    restorativeSignals := BuleReal.ofNat 3 / BuleReal.ofNat 10  -- 30% restorative signals
  }
  
  let initialAwareness := {
    bodyScanAccuracy := BuleReal.ofNat 7 / BuleReal.ofNat 10,  -- 70% body scan accuracy
    signalClarity := BuleReal.ofNat 6 / BuleReal.ofNat 10,     -- 60% signal clarity
    attentionToBody := BuleReal.ofNat 5 / BuleReal.ofNat 10,   -- 50% attention to body
    interpretationAccuracy := BuleReal.ofNat 6 / BuleReal.ofNat 10, -- 60% interpretation accuracy
    predictionAccuracy := BuleReal.ofNat 5 / BuleReal.ofNat 10, -- 50% prediction accuracy
    regulatoryControl := BuleReal.ofNat 6 / BuleReal.ofNat 10,  -- 60% regulatory control
    mindBodyConnection := BuleReal.ofNat 7 / BuleReal.ofNat 10, -- 70% mind-body connection
    interoceptiveLearning := BuleReal.ofNat 4 / BuleReal.ofNat 10 -- 40% interoceptive learning
  }
  
  exact {
    visceralSensations := initialVisceral,
    homeostaticMonitoring := initialHomeostatic,
    painMonitoring := initialPain,
    emotionalInteroception := initialEmotional,
    energyMonitoring := initialEnergy,
    interoceptiveAwareness := initialAwareness,
    parameters := params,
    overallInteroception := BuleReal.ofNat 6 / BuleReal.ofNat 10,  -- 60% overall interoception
    timestamp := BuleReal.zero
  }

end InteroceptiveSystem
end Gnosis
