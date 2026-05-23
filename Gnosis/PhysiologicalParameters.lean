import Gnosis.Real

namespace Gnosis
namespace PhysiologicalParameters

/-!
  # Configurable Physiological Parameters
  
  Central repository for all physiological constants and parameters
  that can be tuned and adjusted for different individuals or conditions.
-/

/-- Respiratory system parameters -/
structure RespiratoryParams where
  -- Lung volume ratios
  tidalVolumeRatio : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 10  -- 10% of vital capacity
  inspiratoryReserveRatio : BuleReal := BuleReal.ofNat 3 / BuleReal.ofNat 10  -- 30% of vital capacity
  expiratoryReserveRatio : BuleReal := BuleReal.ofNat 2 / BuleReal.ofNat 10  -- 20% of vital capacity
  residualVolumeRatio : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 5   -- 20% of total capacity
  
  -- Breathing rate limits
  minBreathingRate : BuleReal := BuleReal.ofNat 8   -- breaths per minute
  maxBreathingRate : BuleReal := BuleReal.ofNat 40  -- breaths per minute
  baselineBreathingRate : BuleReal := BuleReal.ofNat 12  -- breaths per minute
  
  -- Blood gas normal ranges
  normalO2 : BuleReal := BuleReal.ofNat 98        -- arterial O2 saturation (%)
  minO2 : BuleReal := BuleReal.ofNat 95           -- minimum O2 saturation (%)
  maxO2 : BuleReal := BuleReal.ofNat 100          -- maximum O2 saturation (%)
  
  normalCO2 : BuleReal := BuleReal.ofNat 40       -- arterial CO2 (mmHg)
  minCO2 : BuleReal := BuleReal.ofNat 35          -- minimum CO2 (mmHg)
  maxCO2 : BuleReal := BuleReal.ofNat 45          -- maximum CO2 (mmHg)
  
  normalPH : BuleReal := BuleReal.ofNat 740 / BuleReal.ofNat 100  -- 7.40
  minPH : BuleReal := BuleReal.ofNat 735 / BuleReal.ofNat 100     -- 7.35
  maxPH : BuleReal := BuleReal.ofNat 745 / BuleReal.ofNat 100     -- 7.45
  
  -- Muscle activation ratios
  intercostalInspirationRatio : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% of diaphragm
  intercostalExpirationRatio : BuleReal := BuleReal.ofNat 3 / BuleReal.ofNat 10  -- 30% of inspiration
  abdominalExpirationRatio : BuleReal := BuleReal.ofNat 5 / BuleReal.ofNat 10   -- 50% of inspiration
  accessoryThreshold : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10        -- 80% flow demand
  
  -- Energy cost factors
  inspirationEnergyFactor : BuleReal := BuleReal.ofNat 5  -- quadratic cost multiplier
  expirationEnergyFactor : BuleReal := BuleReal.ofNat 3  -- lower cost for exhalation
  
  -- Speech parameters
  syllablesPerBreath : BuleReal := BuleReal.ofNat 15    -- typical syllables per breath
  breathSupportRatio : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% of tidal volume
  saturationRatio : BuleReal := BuleReal.ofNat 98 / BuleReal.ofNat 100      -- 98% of O2
  
  -- Gas change sensitivities
  oxygenChangeSensitivity : BuleReal := BuleReal.ofNat 2  -- O2 change multiplier
  co2ChangeSensitivity : BuleReal := BuleReal.ofNat 3    -- CO2 change multiplier
  phChangeSensitivity : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 100  -- pH change per CO2 unit
  
  -- Ventilation drive parameters
  co2DriveSensitivity : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 10  -- per mmHg
  o2DriveSensitivity : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 20   -- per % O2
  ventilationDriveMultiplier : BuleReal := BuleReal.ofNat 8  -- breaths/min per drive unit
  
  -- Rhythm parameters
  rateStabilitySensitivity : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 50  -- stability loss per breath above baseline
  tidalVolumeRateSensitivity : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 20  -- tidal ratio change per breath above baseline
  
  -- I:E ratio thresholds
  exerciseIERatioThreshold : BuleReal := BuleReal.ofNat 5 / BuleReal.ofNat 10  -- 50% activity level for 1:1 ratio
  restIERatio : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 2  -- 1:2 at rest
  exerciseIERatio : BuleReal := BuleReal.one  -- 1:1 during exercise
  
  -- Flow normalization
  flowNormalizationFactor : BuleReal := BuleReal.ofNat 500  -- normalize flow to 0-1 range
  
  deriving Repr

/-- Cardiovascular system parameters -/
structure CardiovascularParams where
  -- Heart rate limits
  minHeartRate : BuleReal := BuleReal.ofNat 50   -- beats per minute
  maxHeartRate : BuleReal := BuleReal.ofNat 180  -- beats per minute
  baselineHeartRate : BuleReal := BuleReal.ofNat 70  -- beats per minute
  
  -- Stroke volume parameters
  strokeVolumePerKg : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 100  -- 70 mL/kg
  endDiastolicVolumeRatio : BuleReal := BuleReal.ofNat 12 / BuleReal.ofNat 10  -- 120% of stroke volume
  endSystolicVolumeRatio : BuleReal := BuleReal.ofNat 6 / BuleReal.ofNat 10   -- 60% of stroke volume
  
  -- Blood pressure parameters
  normalSystolic : BuleReal := BuleReal.ofNat 120  -- mmHg
  normalDiastolic : BuleReal := BuleReal.ofNat 80   -- mmHg
  
  -- Blood flow distribution (resting)
  cerebralFlowRatio : BuleReal := BuleReal.ofNat 2 / BuleReal.ofNat 10  -- 20% of cardiac output
  muscularFlowRatio : BuleReal := BuleReal.ofNat 2 / BuleReal.ofNat 10  -- 20% of cardiac output
  cutaneousFlowRatio : BuleReal := BuleReal.ofNat 5 / BuleReal.ofNat 100 -- 5% of cardiac output
  
  -- Exercise redistribution
  muscularFlowIncreaseRatio : BuleReal := BuleReal.ofNat 6 / BuleReal.ofNat 10  -- 60% increase
  cutaneousFlowDecreaseRatio : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10 -- 80% decrease
  minCutaneousFlowRatio : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 100   -- 1% minimum
  
  -- Temperature effects
  temperatureSensitivity : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 10  -- per degree above 37°C
  normalTemperature : BuleReal := BuleReal.ofNat 37  -- Celsius
  
  -- Vascular resistance
  baselineResistance : BuleReal := BuleReal.ofNat 80  -- mmHg/L/min
  resistanceSensitivity : BuleReal := BuleReal.ofNat 1000  -- scaling factor
  
  -- Heart rate variability
  baselineRRInterval : BuleReal := BuleReal.ofNat 857  -- ms (70 bpm)
  respiratoryModulationAmplitude : BuleReal := BuleReal.ofNat 5 / BuleReal.ofNat 100  -- 5% RR variation
  stressModulationAmplitude : BuleReal := BuleReal.ofNat 2 / BuleReal.ofNat 10   -- 20% stress effect
  
  -- Cardiorespiratory coupling
  idealHeartBreathRatio : BuleReal := BuleReal.ofNat 4  -- 4:1 heart:breath ratio
  rsaAmplitudeRatio : BuleReal := BuleReal.ofNat 5 / BuleReal.ofNat 100  -- 5% of HRV
  
  -- Circadian effects
  dayHeartRateAdjustment : BuleReal := BuleReal.ofNat 5   -- +5 bpm during day
  nightHeartRateAdjustment : BuleReal := BuleReal.zero -- -5 bpm during night (use zero for now)
  dayHRVFactor : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% of baseline
  nightHRVFactor : BuleReal := BuleReal.ofNat 6 / BuleReal.ofNat 10  -- 60% of baseline
  
  -- Metabolic demand effects
  demandHeartRateMultiplier : BuleReal := BuleReal.ofNat 30  -- max 30 bpm increase
  demandStrokeVolumeMultiplier : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 100  -- 1% per bpm above baseline
  
  deriving Repr

/-- Body composition parameters -/
structure BodyCompositionParams where
  -- Standard adult values
  adultMass : BuleReal := BuleReal.ofNat 700   -- 70 kg
  adultHeight : BuleReal := BuleReal.ofNat 1700 -- 170 cm
  adultHeightOffset : BuleReal := BuleReal.ofNat 150 -- 150 cm offset for vital capacity calculation
  
  -- Lung volume calculation factors
  heightFactor : BuleReal := BuleReal.ofNat 20  -- mL per cm above offset
  massFactor : BuleReal := BuleReal.ofNat 7    -- mL per kg
  
  -- Segment masses (as ratios of total mass)
  headMassRatio : BuleReal := BuleReal.ofNat 47 / BuleReal.ofNat 1000   -- 4.7%
  torsoMassRatio : BuleReal := BuleReal.ofNat 350 / BuleReal.ofNat 1000 -- 35%
  upperArmMassRatio : BuleReal := BuleReal.ofNat 20 / BuleReal.ofNat 1000 -- 2% each
  forearmMassRatio : BuleReal := BuleReal.ofNat 12 / BuleReal.ofNat 1000 -- 1.2% each
  handMassRatio : BuleReal := BuleReal.ofNat 4 / BuleReal.ofNat 1000   -- 0.4% each
  thighMassRatio : BuleReal := BuleReal.ofNat 80 / BuleReal.ofNat 1000  -- 8% each
  shinMassRatio : BuleReal := BuleReal.ofNat 30 / BuleReal.ofNat 1000  -- 3% each
  footMassRatio : BuleReal := BuleReal.ofNat 10 / BuleReal.ofNat 1000  -- 1% each
  
  -- Segment positions (cm from ground)
  headPosition : BuleReal := BuleReal.ofNat 170
  torsoPosition : BuleReal := BuleReal.ofNat 120
  upperArmPosition : BuleReal := BuleReal.ofNat 140
  forearmPosition : BuleReal := BuleReal.ofNat 120
  handPosition : BuleReal := BuleReal.ofNat 100
  thighPosition : BuleReal := BuleReal.ofNat 70
  shinPosition : BuleReal := BuleReal.ofNat 40
  footPosition : BuleReal := BuleReal.ofNat 5
  
  -- Segment lateral positions (cm from center)
  leftOffset : BuleReal := BuleReal.zero  -- Use zero instead of negative
  rightOffset : BuleReal := BuleReal.ofNat 10
  
  deriving Repr

/-- Motor control parameters -/
structure MotorControlParams where
  -- Force scaling factors
  respiratoryForceScale : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 100  -- convert to motor units
  speechForceScale : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 50
  motorForceScale : BuleReal := BuleReal.ofNat 2 / BuleReal.ofNat 10     -- 20% of motor force added to breathing
  
  -- Speed scaling factors
  flowRateSpeedScale : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 1000  -- convert flow to speed
  durationSpeedScale : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 1000  -- convert ms to speed
  cycleDurationScale : BuleReal := BuleReal.ofNat 60000  -- ms per minute
  
  -- Precision values
  respiratoryPrecision : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 0.7
  speechPrecision : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10      -- 0.8
  rhythmPrecision : BuleReal := BuleReal.ofNat 6 / BuleReal.ofNat 10      -- 0.6
  motorPrecision : BuleReal := BuleReal.ofNat 9 / BuleReal.ofNat 10      -- 0.9
  
  -- Activity level scaling
  activityForceMultiplier : BuleReal := BuleReal.ofNat 100  -- convert activity to force
  activitySpeedMultiplier : BuleReal := BuleReal.ofNat 100  -- convert activity to speed
  
  -- Posture effects
  coreBreathingImpact : BuleReal := BuleReal.ofNat 2 / BuleReal.ofNat 10  -- 20% impact on breathing
  postureForceBonus : BuleReal := BuleReal.ofNat 10  -- additional force for posture
  
  deriving Repr

/-- Complete physiological parameter set -/
structure PhysiologicalConstants where
  respiratory : RespiratoryParams
  cardiovascular : CardiovascularParams
  bodyComposition : BodyCompositionParams
  motorControl : MotorControlParams
  metabolism : MetabolismParams
  endocrine : EndocrineParams
  immune : ImmuneParams
  memory : MemoryParams
  somatosensory : SomatosensoryParams
  gustatory : GustatoryParams
  olfactory : OlfactoryParams
  autonomic : AutonomicParams
  language : LanguageParams
  executive : ExecutiveParams
  interoceptive : InteroceptiveParams
  socialCognition : SocialCognitionParams
  selfModel : SelfModelParams
  creativity : CreativityParams
  developmental : DevelopmentalParams
  
  -- Derived convenience values
  totalBodyMass : BuleReal := BuleReal.ofNat 70000  -- 70 kg
  totalBodyHeight : BuleReal := BuleReal.ofNat 170  -- 170 cm
  
  deriving Repr

/-- Metabolism system parameters -/
structure MetabolismParams where
  -- ATP production parameters
  atpProductionRate : BuleReal := BuleReal.ofNat 32  -- ATP molecules per glucose
  atpDecayRate : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 100  -- 1% decay per minute
  basalMetabolicRate : BuleReal := BuleReal.ofNat 70  -- kcal/day/kg
  
  -- Energy budget parameters
  energyEfficiency : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% efficiency
  fatStorageRate : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 100  -- 1% excess energy to fat
  glucoseUtilizationRate : BuleReal := BuleReal.ofNat 2 / BuleReal.ofNat 10  -- 20% per minute
  
  -- Thermoregulation parameters
  coreTemperatureSetpoint : BuleReal := BuleReal.ofNat 37  -- Celsius
  sweatingThreshold : BuleReal := BuleReal.ofNat 38  -- Celsius
  shiveringThreshold : BuleReal := BuleReal.ofNat 36  -- Celsius
  thermalConductivity : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 10  -- Heat loss rate
  
  -- Fatigue parameters
  fatigueAccumulationRate : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 100  -- 1% per activity unit
  recoveryRate : BuleReal := BuleReal.ofNat 5 / BuleReal.ofNat 100  -- 5% per minute rest
  sleepDebtAccumulation : BuleReal := BuleReal.ofNat 2 / BuleReal.ofNat 10  -- 20% per hour missed
  
  deriving Repr

/-- Endocrine system parameters -/
structure EndocrineParams where
  -- Hormone baseline levels
  baselineCortisol : BuleReal := BuleReal.ofNat 10  -- μg/dL
  baselineAdrenaline : BuleReal := BuleReal.ofNat 30  -- pg/mL
  baselineInsulin : BuleReal := BuleReal.ofNat 10  -- μU/mL
  baselineThyroid : BuleReal := BuleReal.ofNat 2  -- mIU/L
  
  -- Stress response parameters
  cortisolStressMultiplier : BuleReal := BuleReal.ofNat 3  -- 3x increase during stress
  adrenalineStressMultiplier : BuleReal := BuleReal.ofNat 10  -- 10x increase during stress
  stressRecoveryTime : BuleReal := BuleReal.ofNat 60  -- minutes to recover
  
  -- Metabolic hormone parameters
  insulinGlucoseSensitivity : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 10  -- per mg/dL glucose
  leptinFatRatio : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 100  -- per kg fat
  ghrelinHungerMultiplier : BuleReal := BuleReal.ofNat 2  -- 2x increase when hungry
  
  -- Circadian parameters
  melatoninPeak : BuleReal := BuleReal.ofNat 80  -- pg/mL at night
  melatoninBaseline : BuleReal := BuleReal.ofNat 10  -- pg/mL during day
  circadianAmplitude : BuleReal := BuleReal.ofNat 70  -- 70% variation
  
  -- Hormone clearance rates
  cortisolHalfLife : BuleReal := BuleReal.ofNat 70  -- minutes
  adrenalineHalfLife : BuleReal := BuleReal.ofNat 2  -- minutes
  insulinHalfLife : BuleReal := BuleReal.ofNat 5  -- minutes
  
  deriving Repr

/-- Immune system parameters -/
structure ImmuneParams where
  -- Immune cell populations
  baselineNeutrophils : BuleReal := BuleReal.ofNat 60  -- % of white blood cells
  baselineLymphocytes : BuleReal := BuleReal.ofNat 30  -- % of white blood cells
  baselineNKCells : BuleReal := BuleReal.ofNat 10  -- % of lymphocytes
  
  -- Response parameters
  pathogenDetectionThreshold : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 1000  -- 0.1% concentration
  immuneResponseLatency : BuleReal := BuleReal.ofNat 24  -- hours
  peakResponseTime : BuleReal := BuleReal.ofNat 48  -- hours
  
  -- Inflammation parameters
  inflammationIntensity : BuleReal := BuleReal.ofNat 5 / BuleReal.ofNat 10  -- 50% of maximum
  inflammationDuration : BuleReal := BuleReal.ofNat 72  -- hours
  antiInflammatoryFeedback : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% feedback efficiency
  
  -- Antibody parameters
  antibodyProductionRate : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 100  -- 1% per hour
  antibodyHalfLife : BuleReal := BuleReal.ofNat 21  -- days
  memoryCellFormation : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 10  -- 10% of activated cells
  
  -- Healing parameters
  tissueRepairRate : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 100  -- 1% per hour
  scarFormationThreshold : BuleReal := BuleReal.ofNat 5 / BuleReal.ofNat 10  -- 50% damage threshold
  healingEfficiency : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% efficiency
  
  deriving Repr

/-- Memory system parameters -/
structure MemoryParams where
  -- Working memory parameters
  workingMemoryCapacity : Nat := 7  -- Miller's magical number
  workingMemoryDecay : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 10  -- 10% per second
  rehearsalEfficiency : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% efficiency
  
  -- Short-term memory parameters
  shortTermCapacity : Nat := 15  -- items
  shortTermDuration : BuleReal := BuleReal.ofNat 30  -- seconds
  consolidationRate : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 100  -- 1% per repetition
  
  -- Long-term memory parameters
  longTermCapacity : Nat := 1000000  -- items (practically unlimited)
  retrievalStrength : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% retrieval strength
  forgettingRate : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 1000  -- 0.1% per day
  
  -- Learning parameters
  learningRate : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 10  -- 10% per experience
  spacingEffect : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% benefit from spacing
  attentionThreshold : BuleReal := BuleReal.ofNat 3 / BuleReal.ofNat 10  -- 30% attention needed
  
  -- Memory type parameters
  episodicStrength : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% episodic memory strength
  semanticStrength : BuleReal := BuleReal.ofNat 9 / BuleReal.ofNat 10  -- 90% semantic memory strength
  proceduralStrength : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% procedural memory strength
  
  deriving Repr

/-- Somatosensory system parameters -/
structure SomatosensoryParams where
  -- Mechanoreceptor parameters
  mechanoreceptorDensity : BuleReal := BuleReal.ofNat 100  -- receptors per cm²
  touchThreshold : BuleReal := BuleReal.ofNat 5  -- mN
  adaptationRate : BuleReal := BuleReal.ofNat 2 / BuleReal.ofNat 10  -- 20% per second
  spatialResolution : BuleReal := BuleReal.ofNat 2  -- mm two-point discrimination
  
  -- Thermoreceptor parameters
  temperatureRange : BuleReal × BuleReal := (BuleReal.ofNat 22, BuleReal.ofNat 38)  -- Comfort range in Celsius
  temperatureSensitivity : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 10  -- per degree
  adaptationTime : BuleReal := BuleReal.ofNat 30  -- seconds
  
  -- Nociceptor parameters
  painThreshold : BuleReal := BuleReal.ofNat 50  -- mN
  hyperalgesiaThreshold : BuleReal := BuleReal.ofNat 30  -- mN (lowered with sensitization)
  referredPainProbability : BuleReal := BuleReal.ofNat 3 / BuleReal.ofNat 10  -- 30% chance
  
  -- Texture parameters
  roughnessSensitivity : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% accuracy
  hardnessSensitivity : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% accuracy
  frictionSensitivity : BuleReal := BuleReal.ofNat 6 / BuleReal.ofNat 10  -- 60% accuracy
  
  -- Vibration parameters
  vibrationRange : BuleReal × BuleReal := (BuleReal.ofNat 10, BuleReal.ofNat 1000)  -- Hz range
  vibrationThreshold : BuleReal := BuleReal.ofNat 1  -- μm
  temporalResolution : BuleReal := BuleReal.ofNat 10  -- ms
  
  deriving Repr

/-- Gustatory system parameters -/
structure GustatoryParams where
  -- Taste receptor parameters
  tasteReceptorDensity : BuleReal := BuleReal.ofNat 200  -- receptors per taste bud
  tasteBudCount : Nat := 8000  -- total taste buds
  detectionThreshold : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 100  -- 1% concentration
  
  -- Basic taste parameters
  sweetSensitivity : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% sensitivity
  sourSensitivity : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% sensitivity
  saltySensitivity : BuleReal := BuleReal.ofNat 6 / BuleReal.ofNat 10  -- 60% sensitivity
  bitterSensitivity : BuleReal := BuleReal.ofNat 9 / BuleReal.ofNat 10  -- 90% sensitivity
  umamiSensitivity : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% sensitivity
  
  -- Flavor integration parameters
  aromaContribution : BuleReal := BuleReal.ofNat 6 / BuleReal.ofNat 10  -- 60% from smell
  textureContribution : BuleReal := BuleReal.ofNat 2 / BuleReal.ofNat 10  -- 20% from texture
  temperatureEffect : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 10  -- 10% from temperature
  
  -- Food evaluation parameters
  palatabilityWeight : BuleReal := BuleReal.ofNat 4 / BuleReal.ofNat 10  -- 40% weight in decisions
  nutritionWeight : BuleReal := BuleReal.ofNat 3 / BuleReal.ofNat 10  -- 30% weight in decisions
  safetyWeight : BuleReal := BuleReal.ofNat 3 / BuleReal.ofNat 10  -- 30% weight in decisions
  
  -- Taste adaptation parameters
  adaptationRate : BuleReal := BuleReal.ofNat 2 / BuleReal.ofNat 10  -- 20% per minute
  recoveryTime : BuleReal := BuleReal.ofNat 5  -- minutes to recover
  
  deriving Repr

/-- Olfactory system parameters -/
structure OlfactoryParams where
  -- Olfactory receptor parameters
  receptorTypes : Nat := 400  -- different receptor types
  receptorsPerType : Nat := 10000  -- receptors per type
  detectionThreshold : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 1000  -- 0.1% concentration
  
  -- Odor processing parameters
  glomerularConvergence : Nat := 50  -- receptors per glomerulus
  spatialPatternAccuracy : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% accuracy
  temporalPatternAccuracy : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% accuracy
  
  -- Odor identification parameters
  identificationLatency : BuleReal := BuleReal.ofNat 10  -- seconds
  confidenceThreshold : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% confidence for identification
  familiarityThreshold : BuleReal := BuleReal.ofNat 5 / BuleReal.ofNat 10  -- 50% for familiarity
  
  -- Chemical communication parameters
  pheromoneSensitivity : BuleReal := BuleReal.ofNat 2 / BuleReal.ofNat 10  -- 20% sensitivity
  socialSignalDetection : BuleReal := BuleReal.ofNat 3 / BuleReal.ofNat 10  -- 30% detection rate
  dangerSignalSensitivity : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% sensitivity
  
  -- Odor memory parameters
  odorMemoryDuration : BuleReal := BuleReal.ofNat 365  -- days
  odorAssociationStrength : BuleReal := BuleReal.ofNat 6 / BuleReal.ofNat 10  -- 60% association strength
  
  deriving Repr

/-- Autonomic nervous system parameters -/
structure AutonomicParams where
  -- Sympathetic parameters
  baselineSympatheticTone : BuleReal := BuleReal.ofNat 3 / BuleReal.ofNat 10  -- 30% baseline
  maxSympatheticActivation : BuleReal := BuleReal.one  -- 100% maximum
  sympatheticLatency : BuleReal := BuleReal.ofNat 3  -- seconds
  
  -- Parasympathetic parameters
  baselineParasympatheticTone : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% baseline
  maxParasympatheticActivation : BuleReal := BuleReal.one  -- 100% maximum
  parasympatheticLatency : BuleReal := BuleReal.ofNat 30  -- seconds
  
  -- Homeostatic parameters
  homeostaticSetpointTolerance : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 10  -- 10% deviation tolerance
  allostaticLoadThreshold : BuleReal := BuleReal.ofNat 5 / BuleReal.ofNat 10  -- 50% allostatic load threshold
  recoveryRate : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 10  -- 10% per minute
  
  -- Stress response parameters
  acuteStressMultiplier : BuleReal := BuleReal.ofNat 5  -- 5x increase during acute stress
  chronicStressAccumulation : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 100  -- 1% per stress event
  exhaustionThreshold : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% stress for exhaustion
  
  -- Circadian parameters
  circadianAmplitude : BuleReal := BuleReal.ofNat 3 / BuleReal.ofNat 10  -- 30% circadian variation
  sleepWakeTransition : BuleReal := BuleReal.ofNat 30  -- minutes for transition
  
  deriving Repr

/-- Language system parameters -/
structure LanguageParams where
  -- Phonological parameters
  phonemeInventorySize : Nat := 44  -- English phonemes
  phonologicalMemoryCapacity : Nat := 7  -- 7±2 chunks
  articulationPlanningTime : BuleReal := BuleReal.ofNat 200  -- ms per syllable
  
  -- Lexical parameters
  vocabularySize : Nat := 20000  -- words
  lexicalAccessTime : BuleReal := BuleReal.ofNat 300  -- ms
  wordRecognitionAccuracy : BuleReal := BuleReal.ofNat 9 / BuleReal.ofNat 10  -- 90% accuracy
  
  -- Syntactic parameters
  parseTreeDepth : Nat := 5  -- maximum depth
  grammaticalAgreementAccuracy : BuleReal := BuleReal.ofNat 9 / BuleReal.ofNat 10  -- 90% accuracy
  sentenceComplexityThreshold : Nat := 20  -- words for complex sentences
  
  -- Semantic parameters
  semanticNetworkDensity : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 10  -- 10% connections
  comprehensionAccuracy : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% accuracy
  inferenceAccuracy : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% accuracy
  
  -- Pragmatic parameters
  conversationalMaximAdherence : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% adherence
  turnTakingAccuracy : BuleReal := BuleReal.ofNat 9 / BuleReal.ofNat 10  -- 90% accuracy
  politenessStrategyAccuracy : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% accuracy
  
  -- Speech production parameters
  speechRate : BuleReal := BuleReal.ofNat 140  -- words per minute
  fluencyRate : BuleReal := BuleReal.ofNat 9 / BuleReal.ofNat 10  -- 90% fluency
  prosodyControl : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% prosody control
  
  deriving Repr

/-- Executive function parameters -/
structure ExecutiveParams where
  -- Working memory control parameters
  workingMemoryCapacity : Nat := 7  -- items
  updatingEfficiency : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% efficiency
  interferenceControl : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% control
  
  -- Inhibitory control parameters
  responseInhibitionAccuracy : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% accuracy
  impulseControlStrength : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% strength
  emotionalRegulationEfficiency : BuleReal := BuleReal.ofNat 6 / BuleReal.ofNat 10  -- 60% efficiency
  
  -- Planning parameters
  goalHierarchyDepth : Nat := 3  -- levels
  subgoalDecompositionAccuracy : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% accuracy
  temporalSequencingAccuracy : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% accuracy
  
  -- Decision making parameters
  optionGenerationCapacity : Nat := 5  -- options
  riskAssessmentAccuracy : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% accuracy
  decisionConfidenceThreshold : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% confidence
  
  -- Cognitive flexibility parameters
  taskSwitchingCost : BuleReal := BuleReal.ofNat 2 / BuleReal.ofNat 10  -- 20% performance cost
  mentalSetShiftingAccuracy : BuleReal := BuleReal.ofNat 6 / BuleReal.ofNat 10  -- 60% accuracy
  alternativeStrategyGeneration : BuleReal := BuleReal.ofNat 4 / BuleReal.ofNat 10  -- 40% alternative strategies
  
  deriving Repr

/-- Interoceptive system parameters -/
structure InteroceptiveParams where
  -- Visceral sensation parameters
  heartbeatDetectionThreshold : BuleReal := BuleReal.ofNat 3 / BuleReal.ofNat 10  -- 30% detection threshold
  respirationDetectionThreshold : BuleReal := BuleReal.ofNat 4 / BuleReal.ofNat 10  -- 40% detection threshold
  digestionDetectionThreshold : BuleReal := BuleReal.ofNat 2 / BuleReal.ofNat 10  -- 20% detection threshold
  
  -- Homeostatic monitoring parameters
  temperatureDeviationThreshold : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 10  -- 10% deviation
  bloodPressureDeviationThreshold : BuleReal := BuleReal.ofNat 2 / BuleReal.ofNat 10  -- 20% deviation
  glucoseDeviationThreshold : BuleReal := BuleReal.ofNat 15 / BuleReal.ofNat 100  -- 15% deviation
  
  -- Pain monitoring parameters
  painSensitivity : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% sensitivity
  painTolerance : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% tolerance
  chronicPainThreshold : BuleReal := BuleReal.ofNat 6 / BuleReal.ofNat 10  -- 60% for chronic pain
  
  -- Emotional interoception parameters
  emotionBodyConnection : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% body-emotion connection
  anxietySignalStrength : BuleReal := BuleReal.ofNat 6 / BuleReal.ofNat 10  -- 60% anxiety signal strength
  stressSignalStrength : BuleReal := BuleReal.ofNat 5 / BuleReal.ofNat 10  -- 50% stress signal strength
  
  -- Energy monitoring parameters
  fatigueDetectionThreshold : BuleReal := BuleReal.ofNat 5 / BuleReal.ofNat 10  -- 50% fatigue threshold
  energyAvailabilityAccuracy : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% accuracy
  recoveryNeedThreshold : BuleReal := BuleReal.ofNat 6 / BuleReal.ofNat 10  -- 60% recovery need threshold
  
  -- Interoceptive awareness parameters
  bodyScanAccuracy : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% body scan accuracy
  signalClarity : BuleReal := BuleReal.ofNat 6 / BuleReal.ofNat 10  -- 60% signal clarity
  mindBodyConnection : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% mind-body connection
  
  deriving Repr

/-- Social cognition parameters -/
structure SocialCognitionParams where
  -- Theory of mind parameters
  beliefAttributionAccuracy : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% accuracy
  desireAttributionAccuracy : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% accuracy
  falseBeliefUnderstandingAccuracy : BuleReal := BuleReal.ofNat 6 / BuleReal.ofNat 10  -- 60% accuracy
  
  -- Social perception parameters
  facialExpressionRecognitionAccuracy : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% accuracy
  bodyLanguageInterpretationAccuracy : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% accuracy
  personalityJudgmentAccuracy : BuleReal := BuleReal.ofNat 6 / BuleReal.ofNat 10  -- 60% accuracy
  
  -- Empathy parameters
  cognitiveEmpathyAccuracy : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% accuracy
  emotionalEmpathyStrength : BuleReal := BuleReal.ofNat 6 / BuleReal.ofNat 10  -- 60% strength
  compassionateEmpathyStrength : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% strength
  
  -- Social reasoning parameters
  moralReasoningAccuracy : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% accuracy
  fairnessJudgmentAccuracy : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% accuracy
  trustAssessmentAccuracy : BuleReal := BuleReal.ofNat 6 / BuleReal.ofNat 10  -- 60% accuracy
  
  -- Social relationship parameters
  socialBondingStrength : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% bonding strength
  groupCohesionLevel : BuleReal := BuleReal.ofNat 6 / BuleReal.ofNat 10  -- 60% cohesion
  socialSupportEffectiveness : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% effectiveness
  
  -- Social interaction parameters
  conversationalSkillAccuracy : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% accuracy
  turnTakingAccuracy : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% accuracy
  conflictManagementEffectiveness : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% effectiveness
  
  deriving Repr

/-- Self model parameters -/
structure SelfModelParams where
  -- Self-awareness parameters
  bodilyAwarenessLevel : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% awareness
  mentalStateAwarenessLevel : BuleReal := BuleReal.ofNat 6 / BuleReal.ofNat 10  -- 60% awareness
  emotionalAwarenessLevel : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% awareness
  
  -- Identity parameters
  identityStability : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% stability
  identityComplexity : BuleReal := BuleReal.ofNat 6 / BuleReal.ofNat 10  -- 60% complexity
  narrativeCoherence : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% coherence
  
  -- Metacognition parameters
  metacognitiveKnowledge : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% knowledge
  metacognitiveMonitoring : BuleReal := BuleReal.ofNat 6 / BuleReal.ofNat 10  -- 60% monitoring
  metacognitiveControl : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% control
  
  -- Autobiographical memory parameters
  episodicMemoryAccuracy : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% accuracy
  selfContinuity : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% continuity
  temporalExtension : BuleReal := BuleReal.ofNat 6 / BuleReal.ofNat 10  -- 60% temporal extension
  
  -- Self-evaluation parameters
  selfWorthLevel : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% self-worth
  competenceEvaluationAccuracy : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% accuracy
  growthMindsetLevel : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% growth mindset
  
  -- Self-regulation parameters
  goalDirectedBehavior : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% goal-directed
  impulseControlStrength : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% impulse control
  selfMonitoringAccuracy : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% self-monitoring
  
  deriving Repr

/-- Creativity system parameters -/
structure CreativityParams where
  -- Divergent thinking parameters
  ideaFluencyRate : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% fluency
  ideaFlexibilityLevel : BuleReal := BuleReal.ofNat 6 / BuleReal.ofNat 10  -- 60% flexibility
  originalityLevel : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% originality
  
  -- Convergent thinking parameters
  problemAnalysisAccuracy : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% accuracy
  solutionEvaluationAccuracy : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% accuracy
  logicalReasoningAccuracy : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% accuracy
  
  -- Artistic expression parameters
  visualCreativityLevel : BuleReal := BuleReal.ofNat 6 / BuleReal.ofNat 10  -- 60% visual creativity
  musicalCreativityLevel : BuleReal := BuleReal.ofNat 5 / BuleReal.ofNat 10  -- 50% musical creativity
  literaryCreativityLevel : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% literary creativity
  
  -- Innovation parameters
  problemIdentificationAccuracy : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% accuracy
  solutionNoveltyLevel : BuleReal := BuleReal.ofNat 6 / BuleReal.ofNat 10  -- 60% novelty
  implementationFeasibility : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% feasibility
  
  -- Creative insight parameters
  insightFrequency : BuleReal := BuleReal.ofNat 5 / BuleReal.ofNat 10  -- 50% frequency
  serendipityDetection : BuleReal := BuleReal.ofNat 6 / BuleReal.ofNat 10  -- 60% detection
  metaphoricalThinkingAccuracy : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% accuracy
  
  -- Creative collaboration parameters
  ideaSharingWillingness : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% willingness
  collaborativeSynergy : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% synergy
  constructiveCriticismAccuracy : BuleReal := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- 70% accuracy
  
  deriving Repr

/-- Developmental systems parameters -/
structure DevelopmentalParams where
  -- Developmental stage parameters
  stageTransitionAge : BuleReal := BuleReal.ofNat 5  -- years between major stages
  developmentalVariability : BuleReal := BuleReal.ofNat 2 / BuleReal.ofNat 10  -- 20% individual variation
  stageCompletionThreshold : BuleReal := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% for stage completion
  
  -- Physical development parameters
  growthRatePeak : BuleReal := BuleReal.ofNat 15  -- cm/year peak growth
  pubertyOnsetAge : BuleReal := BuleReal.ofNat 12  -- years average
  skeletalMaturityAge : BuleReal := BuleReal.ofNat 25  -- years
  
  -- Cognitive development parameters
  workingMemoryDevelopment : BuleReal := BuleReal.ofNat 25  -- years to peak
  processingSpeedPeak : BuleReal := BuleReal.ofNat 20  -- years peak
  abstractReasoningOnset : BuleReal := BuleReal.ofNat 12  -- years onset
  
  -- Emotional development parameters
  emotionalRegulationMaturity : BuleReal := BuleReal.ofNat 25  -- years to maturity
  empathyDevelopment : BuleReal := BuleReal.ofNat 20  -- years to develop
  socialMaturityAge : BuleReal := BuleReal.ofNat 30  -- years to maturity
  
  -- Neuroplasticity parameters
  synapticDensityPeak : BuleReal := BuleReal.ofNat 3  -- years peak
  myelinationCompletion : BuleReal := BuleReal.ofNat 30  -- years completion
  criticalPeriodEnd : BuleReal := BuleReal.ofNat 10  -- years end
  
  -- Aging parameters
  biologicalAgeAcceleration : BuleReal := BuleReal.ofNat 1 / BuleReal.ofNat 100  -- 1% per lifestyle factor
  cellularAgingOnset : BuleReal := BuleReal.ofNat 30  -- years onset
  cognitiveDeclineOnset : BuleReal := BuleReal.ofNat 50  -- years onset
  
  deriving Repr

/-! # Default Parameter Sets -/

/-- Create default respiratory parameters -/
def defaultRespiratoryParams : RespiratoryParams := by
  exact {}

/-- Create default cardiovascular parameters -/
def defaultCardiovascularParams : CardiovascularParams := by
  exact {
    baselineHeartRate := BuleReal.ofNat 70,
    maxHeartRate := BuleReal.ofNat 190,
    minHeartRate := BuleReal.ofNat 50,
    strokeVolumePerKg := BuleReal.ofNat 7,
    normalSystolic := BuleReal.ofNat 120,
    normalDiastolic := BuleReal.ofNat 80,
    cerebralFlowRatio := BuleReal.ofNat 2 / BuleReal.ofNat 10,
    muscularFlowRatio := BuleReal.ofNat 2 / BuleReal.ofNat 10,
    cutaneousFlowRatio := BuleReal.ofNat 5 / BuleReal.ofNat 100,
    muscularFlowIncreaseRatio := BuleReal.ofNat 6 / BuleReal.ofNat 10,
    cutaneousFlowDecreaseRatio := BuleReal.ofNat 8 / BuleReal.ofNat 10,
    minCutaneousFlowRatio := BuleReal.ofNat 1 / BuleReal.ofNat 100,
    temperatureSensitivity := BuleReal.ofNat 1 / BuleReal.ofNat 10,
    normalTemperature := BuleReal.ofNat 37,
    baselineResistance := BuleReal.ofNat 80,
    resistanceSensitivity := BuleReal.ofNat 1000,
    baselineRRInterval := BuleReal.ofNat 857,
    respiratoryModulationAmplitude := BuleReal.ofNat 5 / BuleReal.ofNat 100,
    stressModulationAmplitude := BuleReal.ofNat 2 / BuleReal.ofNat 10,
    idealHeartBreathRatio := BuleReal.ofNat 4,
    rsaAmplitudeRatio := BuleReal.ofNat 5 / BuleReal.ofNat 100,
    dayHeartRateAdjustment := BuleReal.ofNat 5,
    nightHeartRateAdjustment := BuleReal.zero,
    dayHRVFactor := BuleReal.ofNat 8 / BuleReal.ofNat 10,
    nightHRVFactor := BuleReal.ofNat 6 / BuleReal.ofNat 10,
    demandHeartRateMultiplier := BuleReal.ofNat 30,
    demandStrokeVolumeMultiplier := BuleReal.ofNat 1 / BuleReal.ofNat 100
  }

/-- Create default body composition parameters -/
def defaultBodyCompositionParams : BodyCompositionParams := by
  exact {
    heightFactor := BuleReal.ofNat 20,
    massFactor := BuleReal.ofNat 7,
    headMassRatio := BuleReal.ofNat 47 / BuleReal.ofNat 1000,
    torsoMassRatio := BuleReal.ofNat 350 / BuleReal.ofNat 1000,
    upperArmMassRatio := BuleReal.ofNat 20 / BuleReal.ofNat 1000,
    forearmMassRatio := BuleReal.ofNat 12 / BuleReal.ofNat 1000,
    handMassRatio := BuleReal.ofNat 4 / BuleReal.ofNat 1000,
    thighMassRatio := BuleReal.ofNat 80 / BuleReal.ofNat 1000,
    shinMassRatio := BuleReal.ofNat 30 / BuleReal.ofNat 1000,
    footMassRatio := BuleReal.ofNat 10 / BuleReal.ofNat 1000,
    headPosition := BuleReal.ofNat 170,
    torsoPosition := BuleReal.ofNat 120,
    upperArmPosition := BuleReal.ofNat 140,
    forearmPosition := BuleReal.ofNat 120,
    handPosition := BuleReal.ofNat 100,
    thighPosition := BuleReal.ofNat 70,
    shinPosition := BuleReal.ofNat 40,
    footPosition := BuleReal.ofNat 5,
    leftOffset := BuleReal.zero,
    rightOffset := BuleReal.ofNat 10
  }

/-- Create default motor control parameters -/
def defaultMotorControlParams : MotorControlParams := by
  exact {}

/-- Create default metabolism parameters -/
def defaultMetabolismParams : MetabolismParams := by
  exact {}

/-- Create default endocrine parameters -/
def defaultEndocrineParams : EndocrineParams := by
  exact {}

/-- Create default immune parameters -/
def defaultImmuneParams : ImmuneParams := by
  exact {}

/-- Create default memory parameters -/
def defaultMemoryParams : MemoryParams := by
  exact {}

/-- Create default somatosensory parameters -/
def defaultSomatosensoryParams : SomatosensoryParams := by
  exact {}

/-- Create default gustatory parameters -/
def defaultGustatoryParams : GustatoryParams := by
  exact {}

/-- Create default olfactory parameters -/
def defaultOlfactoryParams : OlfactoryParams := by
  exact {}

/-- Create default autonomic parameters -/
def defaultAutonomicParams : AutonomicParams := by
  exact {}

/-- Create default language parameters -/
def defaultLanguageParams : LanguageParams := by
  exact {}

/-- Create default executive parameters -/
def defaultExecutiveParams : ExecutiveParams := by
  exact {}

/-- Create default interoceptive parameters -/
def defaultInteroceptiveParams : InteroceptiveParams := by
  exact {}

/-- Create default social cognition parameters -/
def defaultSocialCognitionParams : SocialCognitionParams := by
  exact {}

/-- Create default self model parameters -/
def defaultSelfModelParams : SelfModelParams := by
  exact {}

/-- Create default creativity parameters -/
def defaultCreativityParams : CreativityParams := by
  exact {}

/-- Create default developmental parameters -/
def defaultDevelopmentalParams : DevelopmentalParams := by
  exact {}

/-- Create complete default physiological constants -/
def defaultPhysiologicalConstants : PhysiologicalConstants := by
  exact {
    respiratory := defaultRespiratoryParams,
    cardiovascular := defaultCardiovascularParams,
    bodyComposition := defaultBodyCompositionParams,
    motorControl := defaultMotorControlParams,
    metabolism := defaultMetabolismParams,
    endocrine := defaultEndocrineParams,
    immune := defaultImmuneParams,
    memory := defaultMemoryParams,
    somatosensory := defaultSomatosensoryParams,
    gustatory := defaultGustatoryParams,
    olfactory := defaultOlfactoryParams,
    autonomic := defaultAutonomicParams,
    language := defaultLanguageParams,
    executive := defaultExecutiveParams,
    interoceptive := defaultInteroceptiveParams,
    socialCognition := defaultSocialCognitionParams,
    selfModel := defaultSelfModelParams,
    creativity := defaultCreativityParams,
    developmental := defaultDevelopmentalParams
  }

/-! # Parameter Validation -/

/-- Validate respiratory parameters are within reasonable bounds -/
def validateRespiratoryParams (params : RespiratoryParams) : Bool :=
  let validRates := params.minBreathingRate ≤ params.baselineBreathingRate && 
                   params.baselineBreathingRate ≤ params.maxBreathingRate
  let validGases := params.minO2 ≤ params.normalO2 && params.normalO2 ≤ params.maxO2 &&
                   params.minCO2 ≤ params.normalCO2 && params.normalCO2 ≤ params.maxCO2 &&
                   params.minPH ≤ params.normalPH && params.normalPH ≤ params.maxPH
  let validRatios := params.tidalVolumeRatio > BuleReal.zero && 
                    params.tidalVolumeRatio ≤ BuleReal.one
  validRates && validGases && validRatios

/-- Validate cardiovascular parameters are within reasonable bounds -/
def validateCardiovascularParams (params : CardiovascularParams) : Bool :=
  let validRates := params.minHeartRate ≤ params.baselineHeartRate && 
                   params.baselineHeartRate ≤ params.maxHeartRate
  let validVolumes := params.strokeVolumePerKg > BuleReal.zero
  let validPressures := params.normalSystolic > params.normalDiastolic
  validRates && validVolumes && validPressures

/-- Validate complete parameter set -/
def validatePhysiologicalConstants (constants : PhysiologicalConstants) : Bool :=
  let respiratoryValid := validateRespiratoryParams constants.respiratory
  let cardiovascularValid := validateCardiovascularParams constants.cardiovascular
  let bodyValid := constants.totalBodyMass > BuleReal.zero && constants.totalBodyHeight > BuleReal.zero
  respiratoryValid && cardiovascularValid && bodyValid

/-! # Parameter Adjustment Functions -/

/-- Adjust respiratory parameters for different conditions -/
def adjustRespiratoryForCondition 
    (baseParams : RespiratoryParams)
    (condition : String) : RespiratoryParams :=
  match condition with
  | "asthma" =>
    { baseParams with 
      maxBreathingRate := baseParams.maxBreathingRate * BuleReal.ofNat 12 / BuleReal.ofNat 10,  -- 20% higher max rate
      normalO2 := if baseParams.normalO2 >= BuleReal.ofNat 2 then baseParams.normalO2 - BuleReal.ofNat 2 else BuleReal.zero,  -- 2% lower O2
      baselineBreathingRate := baseParams.baselineBreathingRate * BuleReal.ofNat 11 / BuleReal.ofNat 10  -- 10% higher baseline
    }
  | "copd" =>
    { baseParams with
      tidalVolumeRatio := baseParams.tidalVolumeRatio * BuleReal.ofNat 8 / BuleReal.ofNat 10,  -- 20% lower tidal volume
      maxBreathingRate := baseParams.maxBreathingRate * BuleReal.ofNat 12 / BuleReal.ofNat 10,  -- 20% higher max rate
      normalO2 := if baseParams.normalO2 >= BuleReal.ofNat 5 then baseParams.normalO2 - BuleReal.ofNat 5 else BuleReal.zero,  -- 5% lower O2
      normalCO2 := baseParams.normalCO2 + BuleReal.ofNat 5  -- 5% higher CO2
    }
  | "athlete" =>
    { baseParams with
      baselineBreathingRate := baseParams.baselineBreathingRate * BuleReal.ofNat 8 / BuleReal.ofNat 10,  -- 20% lower baseline
      maxBreathingRate := baseParams.maxBreathingRate * BuleReal.ofNat 12 / BuleReal.ofNat 10,  -- 20% higher max rate
      normalO2 := baseParams.normalO2 + BuleReal.ofNat 1  -- 1% higher O2
    }
  | _ => baseParams

/-- Adjust cardiovascular parameters for different conditions -/
def adjustCardiovascularForCondition 
    (baseParams : CardiovascularParams)
    (condition : String) : CardiovascularParams :=
  match condition with
  | "athlete" =>
    { baseParams with
      baselineHeartRate := baseParams.baselineHeartRate * BuleReal.ofNat 6 / BuleReal.ofNat 10,  -- 40% lower baseline
      strokeVolumePerKg := baseParams.strokeVolumePerKg * BuleReal.ofNat 12 / BuleReal.ofNat 10,  -- 20% higher stroke volume
      baselineRRInterval := BuleReal.ofNat 60000 / (baseParams.baselineHeartRate * BuleReal.ofNat 6 / BuleReal.ofNat 10)  -- recalculate RR interval
    }
  | "hypertension" =>
    { baseParams with
      normalSystolic := baseParams.normalSystolic * BuleReal.ofNat 13 / BuleReal.ofNat 10,  -- 30% higher systolic
      normalDiastolic := baseParams.normalDiastolic * BuleReal.ofNat 12 / BuleReal.ofNat 10,  -- 20% higher diastolic
      baselineResistance := baseParams.baselineResistance * BuleReal.ofNat 12 / BuleReal.ofNat 10  -- 20% higher resistance
    }
  | "heart_failure" =>
    { baseParams with
      strokeVolumePerKg := baseParams.strokeVolumePerKg * BuleReal.ofNat 7 / BuleReal.ofNat 10,  -- 30% lower stroke volume
      baselineHeartRate := baseParams.baselineHeartRate * BuleReal.ofNat 12 / BuleReal.ofNat 10,  -- 20% higher baseline
      normalSystolic := baseParams.normalSystolic * BuleReal.ofNat 9 / BuleReal.ofNat 10   -- 10% lower systolic
    }
  | _ => baseParams

end PhysiologicalParameters
end Gnosis
