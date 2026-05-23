import Gnosis.ComprehensiveAnatomy
import Gnosis.ThothMotorControl
import Gnosis.Real
import Gnosis.PhysiologicalParameters
import Gnosis.GnosisTimeClock
import Gnosis.Body.MetabolismSystem
import Gnosis.Body.EndocrineSystem
import Mathlib.Data.Real.Basic

namespace Gnosis
namespace GustatorySystem

/-!
  # Gustatory System - Taste and Flavor Perception
  
  Mathematical formalization of taste detection, flavor perception, gustatory
  processing, and food evaluation for the autonomous human system.
-/

/-- Basic taste modalities -/
structure BasicTastes where
  sweet : BuleReal        -- 0.0 to 1.0, sweet intensity
  sour : BuleReal         -- 0.0 to 1.0, sour intensity
  salty : BuleReal        -- 0.0 to 1.0, salty intensity
  bitter : BuleReal       -- 0.0 to 1.0, bitter intensity
  umami : BuleReal        -- 0.0 to 1.0, umami intensity
  fat : BuleReal          -- 0.0 to 1.0, fat taste intensity
  metallic : BuleReal     -- 0.0 to 1.0, metallic taste
  water : BuleReal        -- 0.0 to 1.0, water taste
  deriving Repr

/-- Taste receptor cell responses -/
structure TasteReceptors where
  t1r1_t1r2 : BuleReal    -- Sweet receptors
  t2r : BuleReal          -- Sour receptors
  enac : BuleReal         -- Salty receptors
  t2r4 : BuleReal         -- Bitter receptors
  t1r1_t1r3 : BuleReal    -- Umami receptors
  cd36 : BuleReal         -- Fat receptors
  pkd2l1 : BuleReal       -- Water receptors
  threshold : BuleReal     -- Detection threshold
  adaptationRate : BuleReal -- Taste adaptation speed
  sensitivity : BuleReal   -- Overall taste sensitivity
  deriving Repr

/-- Gustatory processing regions -/
structure GustatoryProcessing where
  tasteBuds : Array (String × BuleReal)  -- (tongue region, activation level)
  papillaeTypes : Array (String × Nat)   -- (papillae type, count)
  neuralActivation : BuleReal            -- Gustatory nerve activation
  corticalResponse : BuleReal           -- Taste cortex activation
  integrationTime : BuleReal             -- Time to integrate tastes
  spatialMapping : BuleReal              -- Tongue spatial mapping
  deriving Repr

/-- Flavor perception and integration -/
structure FlavorPerception where
  tasteProfile : BasicTastes           -- Basic taste components
  aromaContribution : BuleReal         -- How much smell contributes to flavor
  textureContribution : BuleReal       -- Texture influence on flavor
  temperatureEffect : BuleReal         -- Temperature influence on taste
  spiciness : BuleReal                 -- Capsaicin/pungency
  astringency : BuleReal               -- Tannin/drying sensation
  aftertaste : BuleReal                -- Persistent taste
  complexity : BuleReal                -- Overall flavor complexity
  deriving Repr

/-- Food evaluation and preferences -/
structure FoodEvaluation where
  palatability : BuleReal      -- 0.0 to 1.0, how pleasant the taste is
  nutritionalValue : BuleReal   -- 0.0 to 1.0, perceived nutritional value
  safetyAssessment : BuleReal   -- 0.0 to 1.0, food safety evaluation
  caloricEstimate : BuleReal    -- Estimated calories
  macronutrientProfile : (BuleReal × BuleReal × BuleReal)  -- (carbs, protein, fat)
  hydrationValue : BuleReal      -- 0.0 to 1.0, hydration contribution
  satietyPrediction : BuleReal   -- 0.0 to 1.0, how filling it will be
  preferenceScore : BuleReal     -- 0.0 to 1.0, personal preference
  deriving Repr

/-- Gustatory evidence for Thoth framework -/
structure GustatoryEvidence where
  basicTastes : BasicTastes
  tasteReceptors : TasteReceptors
  gustatoryProcessing : GustatoryProcessing
  flavorPerception : FlavorPerception
  foodEvaluation : FoodEvaluation
  parameters : PhysiologicalParameters.BodyCompositionParams
  overallFunction : BuleReal  -- 0.0 to 1.0, gustatory system health
  timestamp : BuleReal
  claimsAuthority : Bool := false
  deriving Repr

/-! # Taste Receptor Functions -/

/-- Process taste molecules through taste receptors -/
def processTasteMolecules 
    (previousReceptors : TasteReceptors)
    (tasteStimulus : BasicTastes)
    (salivaFlow : BuleReal) : TasteReceptors := by
  -- Sweet receptors (T1R1/T1R2) activated by sugars
  let sweetActivation := tasteStimulus.sweet * (BuleReal.one + salivaFlow * BuleReal.ofNat 2 / BuleReal.ofNat 10)
  let newT1r1_t1r2 := previousReceptors.t1r1_t1r2 * BuleReal.ofNat 9 / BuleReal.ofNat 10 + sweetActivation * BuleReal.ofNat 1 / BuleReal.ofNat 10
  
  -- Sour receptors (T2R) activated by acids
  let sourActivation := tasteStimulus.sour * (BuleReal.one + salivaFlow / BuleReal.ofNat 5)
  let newT2r := previousReceptors.t2r * BuleReal.ofNat 9 / BuleReal.ofNat 10 + sourActivation * BuleReal.ofNat 1 / BuleReal.ofNat 10
  
  -- Salty receptors (ENaC) activated by sodium ions
  let saltyActivation := tasteStimulus.salty * (BuleReal.one + salivaFlow / BuleReal.ofNat 10)
  let newENaC := previousReceptors.enac * BuleReal.ofNat 9 / BuleReal.ofNat 10 + saltyActivation * BuleReal.ofNat 1 / BuleReal.ofNat 10
  
  -- Bitter receptors (T2R4) activated by bitter compounds
  let bitterActivation := tasteStimulus.bitter * (BuleReal.one + salivaFlow * BuleReal.ofNat 3 / BuleReal.ofNat 10)
  let newT2r4 := previousReceptors.t2r4 * BuleReal.ofNat 9 / BuleReal.ofNat 10 + bitterActivation * BuleReal.ofNat 1 / BuleReal.ofNat 10
  
  -- Umami receptors (T1R1/T1R3) activated by glutamate
  let umamiActivation := tasteStimulus.umami * (BuleReal.one + salivaFlow / BuleReal.ofNat 5)
  let newT1r1_t1r3 := previousReceptors.t1r1_t1r3 * BuleReal.ofNat 9 / BuleReal.ofNat 10 + umamiActivation * BuleReal.ofNat 1 / BuleReal.ofNat 10
  
  -- Fat receptors (CD36) activated by fatty acids
  let fatActivation := tasteStimulus.fat * (BuleReal.one + salivaFlow / BuleReal.ofNat 8)
  let newCD36 := previousReceptors.cd36 * BuleReal.ofNat 9 / BuleReal.ofNat 10 + fatActivation * BuleReal.ofNat 1 / BuleReal.ofNat 10
  
  -- Water receptors (PKD2L1) activated by pure water
  let waterActivation := tasteStimulus.water * (BuleReal.one - salivaFlow / BuleReal.ofNat 10)
  let newPKD2l1 := previousReceptors.pkd2l1 * BuleReal.ofNat 9 / BuleReal.ofNat 10 + waterActivation * BuleReal.ofNat 1 / BuleReal.ofNat 10
  
  -- Update sensitivity based on recent activation
  let totalActivation := newT1r1_t1r2 + newT2r + newENaC + newT2r4 + newT1r1_t1r3 + newCD36 + newPKD2l1
  let newSensitivity := Float.min (previousReceptors.sensitivity + totalActivation * BuleReal.ofNat 1 / BuleReal.ofNat 100) BuleReal.one
  
  -- Adaptation rate increases with continuous stimulation
  let newAdaptationRate := Float.min (previousReceptors.adaptationRate + totalActivation * BuleReal.ofNat 2 / BuleReal.ofNat 100) BuleReal.ofNat 9 / BuleReal.ofNat 10
  
  exact {
    t1r1_t1r2 := newT1r1_t1r2,
    t2r := newT2r,
    enac := newENaC,
    t2r4 := newT2r4,
    t1r1_t1r3 := newT1r1_t1r3,
    cd36 := newCD36,
    pkd2l1 := newPKD2l1,
    threshold := previousReceptors.threshold,
    adaptationRate := newAdaptationRate,
    sensitivity := newSensitivity
  }

/-! # Gustatory Processing Functions -/

/-- Process taste information through gustatory pathways -/
def processGustatoryInformation 
    (previousProcessing : GustatoryProcessing)
    (receptorInput : TasteReceptors)
    (tongueRegion : String) : GustatoryProcessing := by
  -- Calculate overall receptor activation
  let totalActivation := receptorInput.t1r1_t1r2 + receptorInput.t2r + receptorInput.enac + 
                       receptorInput.t2r4 + receptorInput.t1r1_t1r3 + receptorInput.cd36 + receptorInput.pkd2l1
  
  -- Update taste bud activation for specific tongue region
  let regionActivation := match tongueRegion with
  | "tip" => (receptorInput.t1r1_t1r2 + receptorInput.enac) / BuleReal.ofNat 2  -- Sweet and salty
  | "sides" => (receptorInput.t1r1_t1r3 + receptorInput.t2r) / BuleReal.ofNat 2  -- Umami and sour
  | "back" => (receptorInput.t2r4 + receptorInput.t2r) / BuleReal.ofNat 2  -- Bitter and sour
  | "middle" => totalActivation / BuleReal.ofNat 7  -- All tastes
  | _ => totalActivation / BuleReal.ofNat 7
  
  let newTasteBuds := previousProcessing.tasteBuds.map (λ (region, activation) =>
    if region = tongueRegion then
      (region, activation * BuleReal.ofNat 9 / BuleReal.ofNat 10 + regionActivation * BuleReal.ofNat 1 / BuleReal.ofNat 10)
    else
      (region, activation * BuleReal.ofNat 95 / BuleReal.ofNat 100)  -- Decay other regions
  )
  
  -- Neural activation follows receptor activation
  let newNeuralActivation := totalActivation * receptorInput.sensitivity
  
  -- Cortical response with integration delay
  let integrationDelay := previousProcessing.integrationTime
  let newCorticalResponse := previousProcessing.corticalResponse * BuleReal.ofNat 8 / BuleReal.ofNat 10 + 
                           newNeuralActivation * BuleReal.ofNat 2 / BuleReal.ofNat 10
  
  -- Update integration time based on complexity
  let newIntegrationTime := if totalActivation > BuleReal.ofNat 5 / BuleReal.ofNat 10 then
                           BuleReal.ofNat 2  -- 2 seconds for complex tastes
                         else
                           BuleReal.ofNat 1  -- 1 second for simple tastes
  
  -- Spatial mapping accuracy
  let newSpatialMapping := Float.min (previousProcessing.spatialMapping + regionActivation * BuleReal.ofNat 1 / BuleReal.ofNat 10) BuleReal.one
  
  exact {
    tasteBuds := newTasteBuds,
    papillaeTypes := previousProcessing.papillaeTypes,
    neuralActivation := newNeuralActivation,
    corticalResponse := newCorticalResponse,
    integrationTime := newIntegrationTime,
    spatialMapping := newSpatialMapping
  }

/-! # Flavor Perception Functions -/

/-- Integrate taste with other sensory modalities for flavor -/
def integrateFlavorPerception 
    (previousFlavor : FlavorPerception)
    (tasteInput : BasicTastes)
    (olfactoryInput : BuleReal)
    (textureInput : BuleReal)
    (temperature : BuleReal) : FlavorPerception := by
  -- Update basic taste profile
  let newTasteProfile := tasteInput
  
  -- Aroma contribution (smell is major component of flavor)
  let newAromaContribution := previousFlavor.aromaContribution * BuleReal.ofNat 9 / BuleReal.ofNat 10 + 
                            olfactoryInput * BuleReal.ofNat 1 / BuleReal.ofNat 10
  
  -- Texture contribution to flavor
  let newTextureContribution := previousFlavor.textureContribution * BuleReal.ofNat 9 / BuleReal.ofNat 10 + 
                             textureInput * BuleReal.ofNat 1 / BuleReal.ofNat 10
  
  -- Temperature effects on taste perception
  let temperatureEffect := match temperature with
  | _ if temperature < BuleReal.ofNat 10 => BuleReal.ofNat 7 / BuleReal.ofNat 10  -- Cold reduces taste
  | _ if temperature > BuleReal.ofNat 40 => BuleReal.ofNat 8 / BuleReal.ofNat 10  -- Hot enhances taste
  | _ => BuleReal.one  -- Normal temperature
  let newTemperatureEffect := temperatureEffect
  
  -- Spiciness (capsaicin response) - not a basic taste but contributes to flavor
  let newSpiciness := previousFlavor.spiciness * BuleReal.ofNat 9 / BuleReal.ofNat 10  -- Would be updated by capsaicin input
  
  -- Astringency (tannin response)
  let newAstringency := if tasteInput.bitter > BuleReal.ofNat 5 / BuleReal.ofNat 10 then
                       BuleReal.ofNat 6 / BuleReal.ofNat 10
                     else
                       previousFlavor.astringency * BuleReal.ofNat 9 / BuleReal.ofNat 10
  
  -- Aftertaste persistence
  let totalTasteIntensity := tasteInput.sweet + tasteInput.sour + tasteInput.salty + 
                           tasteInput.bitter + tasteInput.umami + tasteInput.fat
  let newAftertaste := totalTasteIntensity * BuleReal.ofNat 3 / BuleReal.ofNat 10
  
  -- Flavor complexity based on number of active tastes and modalities
  let activeTastes := [tasteInput.sweet, tasteInput.sour, tasteInput.salty, 
                      tasteInput.bitter, tasteInput.umami, tasteInput.fat].filter (λ t => t > BuleReal.ofNat 1 / BuleReal.ofNat 10)
  let tasteComplexity := activeTastes.length.toFloat / BuleReal.ofNat 6
  let modalityComplexity := (newAromaContribution + newTextureContribution + newSpiciness) / BuleReal.ofNat 3
  let newComplexity := (tasteComplexity + modalityComplexity) / BuleReal.ofNat 2
  
  exact {
    tasteProfile := newTasteProfile,
    aromaContribution := newAromaContribution,
    textureContribution := newTextureContribution,
    temperatureEffect := newTemperatureEffect,
    spiciness := newSpiciness,
    astringency := newAstringency,
    aftertaste := newAftertaste,
    complexity := newComplexity
  }

/-! # Food Evaluation Functions -/

/-- Evaluate food based on taste and nutritional information -/
def evaluateFood 
    (previousEvaluation : FoodEvaluation)
    (flavorInput : FlavorPerception)
    (nutritionalInfo : (BuleReal × BuleReal × BuleReal × BuleReal))  -- (calories, carbs, protein, fat)
    (safetySignals : BuleReal) : FoodEvaluation := by
  let (calories, carbs, protein, fat) := nutritionalInfo
  
  -- Palatability based on taste preferences
  let sweetPreference := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- Preference for sweet
  let bitterAversion := BuleReal.ofNat 3 / BuleReal.ofNat 10   -- Aversion to bitter
  let saltyPreference := BuleReal.ofNat 6 / BuleReal.ofNat 10  -- Moderate salt preference
  
  let tasteScore := (flavorInput.tasteProfile.sweet * sweetPreference +
                   flavorInput.tasteProfile.sour * BuleReal.ofNat 5 / BuleReal.ofNat 10 +
                   flavorInput.tasteProfile.salty * saltyPreference +
                   flavorInput.tasteProfile.bitter * bitterAversion +
                   flavorInput.tasteProfile.umami * BuleReal.ofNat 8 / BuleReal.ofNat 10 +
                   flavorInput.tasteProfile.fat * BuleReal.ofNat 6 / BuleReal.ofNat 10) / BuleReal.ofNat 5
  
  let flavorScore := (tasteScore + flavorInput.complexity) / BuleReal.ofNat 2
  let newPalatability := Float.clamp flavorScore BuleReal.zero BuleReal.one
  
  -- Nutritional value perception
  let carbValue := if carbs > BuleReal.ofNat 5 / BuleReal.ofNat 10 then BuleReal.ofNat 6 / BuleReal.ofNat 10 else BuleReal.ofNat 3 / BuleReal.ofNat 10
  let proteinValue := if protein > BuleReal.ofNat 2 / BuleReal.ofNat 10 then BuleReal.ofNat 8 / BuleReal.ofNat 10 else BuleReal.ofNat 4 / BuleReal.ofNat 10
  let fatValue := if fat > BuleReal.ofNat 1 / BuleReal.ofNat 10 then BuleReal.ofNat 5 / BuleReal.ofNat 10 else BuleReal.ofNat 2 / BuleReal.ofNat 10
  let newNutritionalValue := (carbValue + proteinValue + fatValue) / BuleReal.ofNat 3
  
  -- Safety assessment
  let bitternessWarning := if flavorInput.tasteProfile.bitter > BuleReal.ofNat 8 / BuleReal.ofNat 10 then BuleReal.ofNat 3 / BuleReal.ofNat 10 else BuleReal.zero
  let metallicWarning := if flavorInput.tasteProfile.metallic > BuleReal.ofNat 5 / BuleReal.ofNat 10 then BuleReal.ofNat 4 / BuleReal.ofNat 10 else BuleReal.zero
  let newSafetyAssessment := Float.max (BuleReal.one - safetySignals - bitternessWarning - metallicWarning) BuleReal.zero
  
  -- Caloric estimation
  let newCaloricEstimate := calories
  
  -- Macronutrient profile
  let newMacronutrientProfile := (carbs, protein, fat)
  
  -- Hydration value (water taste and moisture)
  let newHydrationValue := flavorInput.tasteProfile.water * BuleReal.ofNat 8 / BuleReal.ofNat 10
  
  -- Satiety prediction based on calories and macronutrients
  let satietyFactor := (calories / BuleReal.ofNat 500 + protein * BuleReal.ofNat 2 + fat * BuleReal.ofNat 3) / BuleReal.ofNat 6
  let newSatietyPrediction := Float.clamp satietyFactor BuleReal.zero BuleReal.one
  
  -- Overall preference combines palatability, nutrition, and safety
  let preferenceFactors := #[
    newPalatability,
    newNutritionalValue,
    newSafetyAssessment,
    newSatietyPrediction * BuleReal.ofNat 5 / BuleReal.ofNat 10  -- Moderate weight to satiety
  ]
  let newPreferenceScore := preferenceFactors.foldl (λ sum factor => sum + factor) BuleReal.zero / BuleReal.ofNat 4
  
  exact {
    palatability := newPalatability,
    nutritionalValue := newNutritionalValue,
    safetyAssessment := newSafetyAssessment,
    caloricEstimate := newCaloricEstimate,
    macronutrientProfile := newMacronutrientProfile,
    hydrationValue := newHydrationValue,
    satietyPrediction := newSatietyPrediction,
    preferenceScore := newPreferenceScore
  }

/-! # System Integration -/

/-- Update complete gustatory system -/
def updateGustatorySystem 
    (previousEvidence : GustatoryEvidence)
    (tasteStimulus : BasicTastes)
    (olfactoryInput : BuleReal)
    (textureInput : BuleReal)
    (temperature : BuleReal)
    (nutritionalInfo : (BuleReal × BuleReal × BuleReal × BuleReal))
    (timeStep : BuleReal) : GustatoryEvidence := by
  -- Update taste receptors
  let salivaFlow := BuleReal.ofNat 7 / BuleReal.ofNat 10  -- Normal saliva flow
  let newTasteReceptors := processTasteMolecules previousEvidence.tasteReceptors tasteStimulus salivaFlow
  
  -- Update gustatory processing
  let newGustatoryProcessing := processGustatoryInformation 
    previousEvidence.gustatoryProcessing 
    newTasteReceptors 
    "middle"  -- Assume stimulation in middle of tongue
  
  -- Update flavor perception
  let newFlavorPerception := integrateFlavorPerception 
    previousEvidence.flavorPerception 
    tasteStimulus 
    olfactoryInput 
    textureInput 
    temperature
  
  -- Update food evaluation
  let safetySignals := BuleReal.ofNat 1 / BuleReal.ofNat 10  -- Low safety concern
  let newFoodEvaluation := evaluateFood 
    previousEvidence.foodEvaluation 
    newFlavorPerception 
    nutritionalInfo 
    safetySignals
  
  -- Calculate overall gustatory function
  let functionFactors := #[
    newTasteReceptors.sensitivity,
    newGustatoryProcessing.neuralActivation,
    newGustatoryProcessing.corticalResponse,
    newFlavorPerception.complexity,
    newFoodEvaluation.palatability
  ]
  let overallFunction := functionFactors.foldl (λ sum factor => sum + factor) BuleReal.zero / BuleReal.ofNat 5
  
  exact {
    basicTastes := tasteStimulus,
    tasteReceptors := newTasteReceptors,
    gustatoryProcessing := newGustatoryProcessing,
    flavorPerception := newFlavorPerception,
    foodEvaluation := newFoodEvaluation,
    parameters := previousEvidence.parameters,
    overallFunction := overallFunction,
    timestamp := previousEvidence.timestamp + timeStep
  }

/-! # Default System Initialization -/

/-- Initialize gustatory system with default parameters -/
def initGustatorySystem (params : PhysiologicalParameters.BodyCompositionParams) : GustatoryEvidence := by
  let initialTastes := {
    sweet := BuleReal.zero,
    sour := BuleReal.zero,
    salty := BuleReal.zero,
    bitter := BuleReal.zero,
    umami := BuleReal.zero,
    fat := BuleReal.zero,
    metallic := BuleReal.zero,
    water := BuleReal.zero
  }
  
  let initialReceptors := {
    t1r1_t1r2 := BuleReal.zero,
    t2r := BuleReal.zero,
    enac := BuleReal.zero,
    t2r4 := BuleReal.zero,
    t1r1_t1r3 := BuleReal.zero,
    cd36 := BuleReal.zero,
    pkd2l1 := BuleReal.zero,
    threshold := BuleReal.ofNat 1 / BuleReal.ofNat 100,  -- 1% threshold
    adaptationRate := BuleReal.ofNat 2 / BuleReal.ofNat 10,  -- 20% adaptation rate
    sensitivity := BuleReal.ofNat 8 / BuleReal.ofNat 10   -- 80% sensitivity
  }
  
  let initialProcessing := {
    tasteBuds := #[
      ("tip", BuleReal.zero),
      ("sides", BuleReal.zero),
      ("back", BuleReal.zero),
      ("middle", BuleReal.zero)
    ],
    papillaeTypes := #[
      ("fungiform", 200),    -- 200 fungiform papillae
      ("circumvallate", 12), -- 12 circumvallate papillae
      ("foliate", 20)       -- 20 foliate papillae
    ],
    neuralActivation := BuleReal.zero,
    corticalResponse := BuleReal.zero,
    integrationTime := BuleReal.ofNat 1,  -- 1 second integration
    spatialMapping := BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% spatial accuracy
  }
  
  let initialFlavor := {
    tasteProfile := initialTastes,
    aromaContribution := BuleReal.ofNat 6 / BuleReal.ofNat 10,  -- 60% aroma contribution
    textureContribution := BuleReal.ofNat 2 / BuleReal.ofNat 10,  -- 20% texture contribution
    temperatureEffect := BuleReal.one,
    spiciness := BuleReal.zero,
    astringency := BuleReal.zero,
    aftertaste := BuleReal.zero,
    complexity := BuleReal.zero
  }
  
  let initialEvaluation := {
    palatability := BuleReal.ofNat 7 / BuleReal.ofNat 10,  -- 70% baseline palatability
    nutritionalValue := BuleReal.ofNat 6 / BuleReal.ofNat 10,  -- 60% nutritional value
    safetyAssessment := BuleReal.ofNat 9 / BuleReal.ofNat 10,  -- 90% safety
    caloricEstimate := BuleReal.zero,
    macronutrientProfile := (BuleReal.zero, BuleReal.zero, BuleReal.zero),
    hydrationValue := BuleReal.ofNat 5 / BuleReal.ofNat 10,  -- 50% hydration
    satietyPrediction := BuleReal.ofNat 5 / BuleReal.ofNat 10,  -- 50% satiety
    preferenceScore := BuleReal.ofNat 6 / BuleReal.ofNat 10   -- 60% preference
  }
  
  exact {
    basicTastes := initialTastes,
    tasteReceptors := initialReceptors,
    gustatoryProcessing := initialProcessing,
    flavorPerception := initialFlavor,
    foodEvaluation := initialEvaluation,
    parameters := params,
    overallFunction := BuleReal.ofNat 8 / BuleReal.ofNat 10,
    timestamp := BuleReal.zero
  }

end GustatorySystem
end Gnosis
