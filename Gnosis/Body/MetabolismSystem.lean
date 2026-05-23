import Gnosis.ComprehensiveAnatomy
import Gnosis.ThothMotorControl
import Gnosis.Real
import Gnosis.PhysiologicalParameters
import Gnosis.GnosisTimeClock
import Mathlib.Data.Real.Basic

namespace Gnosis
namespace MetabolismSystem

/-!
  # Metabolism and Energy System
  
  Mathematical formalization of cellular energy production, ATP dynamics,
  metabolic pathways, and energy budgeting for the autonomous human.
-/

/-- Energy currency and metabolic state -/
structure EnergyState where
  atpLevel : BuleReal  -- ATP concentration (0.0 to 1.0 normalized)
  adpLevel : BuleReal  -- ADP concentration
  ampLevel : BuleReal  -- AMP concentration
  phosphocreatine : BuleReal  -- PCr energy buffer
  totalEnergy : BuleReal  -- Total cellular energy (kcal)
  metabolicRate : BuleReal  -- Current metabolic rate (kcal/day)
  energyDeficit : BuleReal  -- Energy deficit/surplus
  deriving Repr

/-- Nutrient and fuel sources -/
structure NutrientPool where
  glucose : BuleReal  -- Blood glucose (mg/dL)
  fattyAcids : BuleReal  -- Free fatty acids
  aminoAcids : BuleReal  -- Free amino acids
  glycogen : BuleReal  -- Glycogen stores (liver + muscle)
  fatStores : BuleReal  -- Adipose tissue energy (kcal)
  proteinStores : BuleReal  -- Muscle protein (kg)
  hydration : BuleReal  -- Body water percentage
  deriving Repr

/-- Cellular respiration processes -/
structure CellularRespiration where
  glycolysisRate : BuleReal  -- Glucose → Pyruvate rate
  krebsCycleRate : BuleReal  -- TCA cycle rate
  oxidativePhosphorylation : BuleReal  -- ATP synthesis rate
  oxygenConsumption : BuleReal  -- VO2 (mL/kg/min)
  co2Production : BuleReal  -- VCO2 (mL/kg/min)
  respiratoryQuotient : BuleReal  -- VCO2/VO2 ratio
  mitochondrialEfficiency : BuleReal  -- ATP/O2 ratio
  deriving Repr

/-- Thermoregulation and heat management -/
structure ThermalState where
  coreTemperature : BuleReal  -- Core body temperature (°C)
  skinTemperature : BuleReal  -- Average skin temperature
  heatProduction : BuleReal  -- Metabolic heat production (W)
  heatLoss : BuleReal  -- Heat loss to environment (W)
  sweatingRate : BuleReal  -- Sweat production (mL/hour)
  shiveringThermogenesis : BuleReal  -- Shivering heat production
  vasomotorTone : BuleReal  -- Blood vessel constriction (0-1)
  deriving Repr

/-- Fatigue and recovery dynamics -/
structure FatigueState where
  muscularFatigue : BuleReal  -- Muscle fatigue (0-1)
  centralFatigue : BuleReal  -- Central nervous system fatigue
  mentalFatigue : BuleReal  -- Cognitive fatigue
  recoveryRate : BuleReal  -- Recovery rate multiplier
  sleepDebt : BuleReal  -- Accumulated sleep debt (hours)
  circadianPhase : BuleReal  -- Circadian rhythm phase
  deriving Repr

/-- Metabolic evidence for Thoth framework -/
structure MetabolicEvidence where
  energyState : EnergyState
  nutrientPool : NutrientPool
  cellularRespiration : CellularRespiration
  thermalState : ThermalState
  fatigueState : FatigueState
  parameters : PhysiologicalParameters.BodyCompositionParams
  overallEfficiency : BuleReal  -- 0.0 to 1.0
  timestamp : BuleReal
  claimsAuthority : Bool := false
  deriving Repr

/-! # Energy Production Functions -/

/-- Calculate ATP production from cellular respiration -/
def calculateATPProduction 
    (oxygenAvailability : BuleReal)
    (substrateAvailability : BuleReal) 
    (mitochondrialHealth : BuleReal) : BuleReal := by
  -- Maximum ATP production rate with full oxygen and substrates
  let maxATPRate := BuleReal.ofNat 32  -- 32 ATP per glucose molecule
  
  -- Limiting factors: oxygen, substrates, mitochondrial efficiency
  let oxygenFactor := Float.min oxygenAvailability BuleReal.one
  let substrateFactor := Float.min substrateAvailability BuleReal.one
  let mitochondrialFactor := mitochondrialHealth
  
  exact maxATPRate * oxygenFactor * substrateFactor * mitochondrialFactor

/-- Update cellular respiration based on metabolic demand -/
def updateCellularRespiration 
    (previousState : CellularRespiration)
    (metabolicDemand : BuleReal)
    (oxygenLevel : BuleReal)
    (glucoseLevel : BuleReal) : CellularRespiration := by
  -- Increase respiration rate with demand, limited by oxygen and glucose
  let demandFactor := Float.clamp metabolicDemand BuleReal.ofNat 5 BuleReal.ofNat 20
  let oxygenLimit := oxygenLevel / BuleReal.ofNat 100  -- Normalize oxygen availability
  let glucoseLimit := glucoseLevel / BuleReal.ofNat 100  -- Normalize glucose availability
  
  let newGlycolysis := demandFactor * oxygenLimit * glucoseLimit
  let newKrebsCycle := newGlycolysis * BuleReal.ofNat 8 / BuleReal.ofNat 10  -- 80% of glycolysis
  let newOxPhos := newKrebsCycle * BuleReal.ofNat 9 / BuleReal.ofNat 10  -- 90% of TCA
  
  let newVO2 := newOxPhos * BuleReal.ofNat 5  -- 5 mL O2 per ATP
  let newVCO2 := newVO2 * BuleReal.ofNat 8 / BuleReal.ofNat 10  -- RQ = 0.8 for mixed fuel
  let newRQ := if newVO2 > BuleReal.zero then newVCO2 / newVO2 else BuleReal.ofNat 85 / BuleReal.ofNat 100
  
  exact {
    glycolysisRate := newGlycolysis,
    krebsCycleRate := newKrebsCycle,
    oxidativePhosphorylation := newOxPhos,
    oxygenConsumption := newVO2,
    co2Production := newVCO2,
    respiratoryQuotient := newRQ,
    mitochondrialEfficiency := previousState.mitochondrialEfficiency
  }

/-! # Energy Budget and Balance -/

/-- Calculate total daily energy expenditure -/
def calculateTotalEnergyExpenditure 
    (bodyMass : BuleReal)
    (activityLevel : BuleReal)
    (thermalEffect : BuleReal) : BuleReal := by
  -- Basal metabolic rate (Harris-Benedict equation simplified)
  let bmr := bodyMass * BuleReal.ofNat 10 + BuleReal.ofNat 1500  -- 10 kcal/kg + 1500 base
  
  -- Activity multiplier: 1.2 (sedentary) to 2.5 (very active)
  let activityMultiplier := BuleReal.ofNat 12 / BuleReal.ofNat 10 + activityLevel * BuleReal.ofNat 13 / BuleReal.ofNat 10
  
  -- Thermic effect of food (~10% of total)
  let thermicEffect := bmr * activityMultiplier * thermalEffect
  
  exact bmr * activityMultiplier + thermicEffect

/-- Update energy state based on production and consumption -/
def updateEnergyState 
    (previousState : EnergyState)
    (atpProduction : BuleReal)
    (energyConsumption : BuleReal)
    (timeStep : BuleReal) : EnergyState := by
  -- ATP dynamics with phosphocreatine buffer
  let atpChange := (atpProduction - energyConsumption) * timeStep
  let newATP := Float.clamp (previousState.atpLevel + atpChange) BuleReal.zero BuleReal.one
  
  -- Phosphocreatine buffers ATP changes
  let pcrtChange := -atpChange * BuleReal.ofNat 3 / BuleReal.ofNat 10  -- 30% of ATP change buffered by PCr
  let newPCr := Float.clamp (previousState.phosphocreatine + pcrtChange) BuleReal.zero BuleReal.one
  
  -- ADP/AMP balance
  let newADP := BuleReal.one - newATP - previousState.ampLevel
  let newAMP := BuleReal.ofNat 5 / BuleReal.ofNat 100 * (BuleReal.one - newATP)  -- AMP increases with ATP depletion
  
  let totalEnergyChange := (atpProduction - energyConsumption) * timeStep * BuleReal.ofNat 777  -- 7.7 kcal per ATP
  let newTotalEnergy := previousState.totalEnergy + totalEnergyChange
  let newEnergyDeficit := energyConsumption - atpProduction
  
  -- Metabolic rate adapts to energy state
  let metabolicAdjustment := if newEnergyDeficit > BuleReal.zero then 
                            BuleReal.ofNat 95 / BuleReal.ofNat 100  -- 5% reduction in deficit
                          else 
                            BuleReal.one
  let newMetabolicRate := previousState.metabolicRate * metabolicAdjustment
  
  exact {
    atpLevel := newATP,
    adpLevel := newADP,
    ampLevel := newAMP,
    phosphocreatine := newPCr,
    totalEnergy := newTotalEnergy,
    metabolicRate := newMetabolicRate,
    energyDeficit := newEnergyDeficit
  }

/-! # Nutrient Processing Functions -/

/-- Update nutrient pools based on intake and utilization -/
def updateNutrientPool 
    (previousPool : NutrientPool)
    (glucoseIntake : BuleReal)
    (fatIntake : BuleReal)
    (proteinIntake : BuleReal)
    (glucoseUtilization : BuleReal)
    (fatUtilization : BuleReal)
    (proteinUtilization : BuleReal) : NutrientPool := by
  -- Glucose dynamics (mg/dL)
  let glucoseChange := (glucoseIntake - glucoseUtilization) * BuleReal.ofNat 100
  let newGlucose := Float.clamp (previousPool.glucose + glucoseChange) BuleReal.ofNat 70 BuleReal.ofNat 140
  
  -- Glycogen storage (limited capacity)
  let glycogenChange := if newGlucose > BuleReal.ofNat 100 then 
                      (newGlucose - BuleReal.ofNat 100) * BuleReal.ofNat 5 / BuleReal.ofNat 100
                    else 
                      BuleReal.zero
  let newGlycogen := Float.clamp (previousPool.glycogen + glycogenChange) BuleReal.zero BuleReal.ofNat 500
  
  -- Fat stores (kcal, 1g fat = 9 kcal)
  let fatChange := (fatIntake - fatUtilization) * BuleReal.ofNat 9
  let newFatStores := previousPool.fatStores + fatChange
  
  -- Protein stores (kg, limited conversion)
  let proteinChange := (proteinIntake - proteinUtilization) / BuleReal.ofNat 1000
  let newProtein := Float.clamp (previousPool.proteinStores + proteinChange) 
                        (bodyMass * BuleReal.ofNat 3 / BuleReal.ofNat 100) 
                        (bodyMass * BuleReal.ofNat 5 / BuleReal.ofNat 100)
  
  -- Fatty acids in blood
  let newFattyAcids := if newGlucose < BuleReal.ofNat 80 then 
                       previousPool.fatStores * BuleReal.ofNat 1 / BuleReal.ofNat 100
                     else 
                       previousPool.fatStores * BuleReal.ofNat 2 / BuleReal.ofNat 100
  
  -- Amino acids in blood
  let newAminoAcids := proteinIntake / BuleReal.ofNat 100
  
  -- Hydration (percentage of body weight)
  let waterChange := BuleReal.zero  -- Simplified, would need fluid intake/loss
  let newHydration := Float.clamp (previousPool.hydration + waterChange) 
                        BuleReal.ofNat 45 BuleReal.ofNat 75
  
  exact {
    glucose := newGlucose,
    fattyAcids := newFattyAcids,
    aminoAcids := newAminoAcids,
    glycogen := newGlycogen,
    fatStores := newFatStores,
    proteinStores := newProtein,
    hydration := newHydration
  }

/-! # Thermoregulation Functions -/

/-- Calculate heat production from metabolism -/
def calculateHeatProduction 
    (metabolicRate : BuleReal)
    (muscleActivity : BuleReal)
    (shivering : BuleReal) : BuleReal := by
  -- Basal heat production (1 kcal = 4.184 kJ = 1.162 W)
  let basalHeat := metabolicRate * BuleReal.ofNat 1162 / BuleReal.ofNat 1000
  
  -- Muscle activity heat (20% efficiency, 80% heat)
  let activityHeat := muscleActivity * BuleReal.ofNat 4
  
  -- Shivering thermogenesis
  let shiveringHeat := shivering * BuleReal.ofNat 5
  
  exact basalHeat + activityHeat + shiveringHeat

/-- Update thermal state based on heat balance -/
def updateThermalState 
    (previousState : ThermalState)
    (heatProduction : BuleReal)
    (ambientTemperature : BuleReal)
    (activityLevel : BuleReal) : ThermalState := by
  -- Heat loss depends on temperature gradient
  let temperatureGradient := previousState.coreTemperature - ambientTemperature
  let heatLossCoefficient := BuleReal.ofNat 10  -- W/°C simplified
  let newHeatLoss := temperatureGradient * heatLossCoefficient
  
  -- Core temperature changes with heat balance
  let heatBalance := heatProduction - newHeatLoss
  let bodyHeatCapacity := BuleReal.ofNat 3500  -- kJ/°C for 70kg human
  let temperatureChange := heatBalance * timeStep / bodyHeatCapacity
  let newCoreTemp := Float.clamp (previousState.coreTemperature + temperatureChange) 
                        BuleReal.ofNat 365 BuleReal.ofNat 405  -- 36.5°C to 40.5°C
  
  -- Skin temperature follows core with lag
  let skinLagFactor := BuleReal.ofNat 8 / BuleReal.ofNat 10
  let newSkinTemp := previousState.skinTemperature * skinLagFactor + 
                    newCoreTemp * (BuleReal.one - skinLagFactor)
  
  -- Sweating response to heat
  let sweatingThreshold := BuleReal.ofNat 37
  let newSweating := if newCoreTemp > sweatingThreshold then 
                    (newCoreTemp - sweatingThreshold) * BuleReal.ofNat 500
                  else 
                    BuleReal.zero
  
  -- Shivering response to cold
  let shiveringThreshold := BuleReal.ofNat 365
  let newShivering := if newCoreTemp < shiveringThreshold then 
                      (shiveringThreshold - newCoreTemp) * BuleReal.ofNat 200
                    else 
                      BuleReal.zero
  
  -- Vasomotor tone (vasoconstriction in cold, vasodilation in heat)
  let newVasomotor := Float.clamp ((BuleReal.ofNat 37 - newCoreTemp) / BuleReal.ofNat 5) 
                        BuleReal.zero BuleReal.one
  
  exact {
    coreTemperature := newCoreTemp,
    skinTemperature := newSkinTemp,
    heatProduction := heatProduction,
    heatLoss := newHeatLoss,
    sweatingRate := newSweating,
    shiveringThermogenesis := newShivering,
    vasomotorTone := newVasomotor
  }

/-! # Fatigue and Recovery Functions -/

/-- Update fatigue state based on activity and recovery -/
def updateFatigueState 
    (previousState : FatigueState)
    (physicalActivity : BuleReal)
    (mentalActivity : BuleReal)
    (sleepQuality : BuleReal)
    (timeStep : BuleReal) : FatigueState := by
  -- Fatigue accumulation
  let muscularFatigueRate := physicalActivity * BuleReal.ofNat 2
  let centralFatigueRate := (physicalActivity + mentalActivity) * BuleReal.ofNat 1
  let mentalFatigueRate := mentalActivity * BuleReal.ofNat 3
  
  -- Recovery during rest/sleep
  let recoveryMultiplier := previousState.recoveryRate * sleepQuality
  let muscularRecovery := previousState.muscularFatigue * recoveryMultiplier * timeStep * BuleReal.ofNat 5
  let centralRecovery := previousState.centralFatigue * recoveryMultiplier * timeStep * BuleReal.ofNat 3
  let mentalRecovery := previousState.mentalFatigue * recoveryMultiplier * timeStep * BuleReal.ofNat 4
  
  -- Update fatigue levels
  let newMuscular := Float.clamp (previousState.muscularFatigue + muscularFatigueRate - muscularRecovery) 
                        BuleReal.zero BuleReal.one
  let newCentral := Float.clamp (previousState.centralFatigue + centralFatigueRate - centralRecovery) 
                      BuleReal.zero BuleReal.one
  let newMental := Float.clamp (previousState.mentalFatigue + mentalFatigueRate - mentalRecovery) 
                    BuleReal.zero BuleReal.one
  
  -- Sleep debt accumulation
  let sleepNeed := BuleReal.ofNat 8  -- 8 hours needed
  let actualSleep := sleepQuality * BuleReal.ofNat 8
  let sleepDebtChange := sleepNeed - actualSleep
  let newSleepDebt := Float.max (previousState.sleepDebt + sleepDebtChange) BuleReal.zero
  
  -- Circadian phase update
  let newCircadianPhase := (previousState.circadianPhase + timeStep / BuleReal.ofNat 24) % BuleReal.one
  
  -- Recovery rate adapts to fatigue and sleep
  let newRecoveryRate := if newSleepDebt < BuleReal.ofNat 2 then 
                        BuleReal.ofNat 9 / BuleReal.ofNat 10  -- 90% recovery when well-rested
                      else 
                        BuleReal.ofNat 6 / BuleReal.ofNat 10  -- 60% recovery when sleep-deprived
  
  exact {
    muscularFatigue := newMuscular,
    centralFatigue := newCentral,
    mentalFatigue := newMental,
    recoveryRate := newRecoveryRate,
    sleepDebt := newSleepDebt,
    circadianPhase := newCircadianPhase
  }

/-! # System Integration -/

/-- Update complete metabolic system -/
def updateMetabolicSystem 
    (previousEvidence : MetabolicEvidence)
    (activityLevel : BuleReal)
    (nutrientIntake : BuleReal × BuleReal × BuleReal)  -- (carbs, fats, protein)
    (ambientTemperature : BuleReal)
    (timeStep : BuleReal) : MetabolicEvidence := by
  let bodyMass := previousEvidence.parameters.totalBodyMass
  
  -- Calculate energy demand
  let tdee := calculateTotalEnergyExpenditure bodyMass activityLevel BuleReal.ofNat 1
  let energyDemand := tdee / BuleReal.ofNat 24  -- Convert to hourly rate
  
  -- Update cellular respiration
  let newRespiration := updateCellularRespiration 
    previousEvidence.cellularRespiration 
    energyDemand 
    BuleReal.ofNat 98  -- Assuming 98% oxygen saturation
    previousEvidence.nutrientPool.glucose
  
  -- Calculate ATP production
  let atpProduction := calculateATPProduction 
    BuleReal.ofNat 98  -- Oxygen availability
    previousEvidence.nutrientPool.glucose / BuleReal.ofNat 100
    BuleReal.ofNat 9 / BuleReal.ofNat 10  -- Mitochondrial health
  
  -- Update energy state
  let newEnergyState := updateEnergyState 
    previousEvidence.energyState 
    atpProduction 
    energyDemand 
    timeStep
  
  -- Update nutrient pools
  let (carbIntake, fatIntake, proteinIntake) := nutrientIntake
  let newNutrientPool := updateNutrientPool 
    previousEvidence.nutrientPool
    carbIntake
    fatIntake
    proteinIntake
    energyDemand * BuleReal.ofNat 4 / BuleReal.ofNat 10  -- 40% from glucose
    energyDemand * BuleReal.ofNat 3 / BuleReal.ofNat 10  -- 30% from fat
    energyDemand * BuleReal.ofNat 3 / BuleReal.ofNat 10  -- 30% from protein
  
  -- Update thermal state
  let heatProd := calculateHeatProduction newEnergyState.metabolicRate activityLevel BuleReal.zero
  let newThermalState := updateThermalState 
    previousEvidence.thermalState 
    heatProd 
    ambientTemperature 
    activityLevel
  
  -- Update fatigue state
  let newFatigueState := updateFatigueState 
    previousEvidence.fatigueState 
    activityLevel 
    BuleReal.ofNat 5  -- Mental activity level
    BuleReal.ofNat 8 / BuleReal.ofNat 10  -- Sleep quality
    timeStep
  
  -- Calculate overall efficiency
  let efficiency := atpProduction / energyDemand
  
  exact {
    energyState := newEnergyState,
    nutrientPool := newNutrientPool,
    cellularRespiration := newRespiration,
    thermalState := newThermalState,
    fatigueState := newFatigueState,
    parameters := previousEvidence.parameters,
    overallEfficiency := efficiency,
    timestamp := previousEvidence.timestamp + timeStep
  }

/-! # Default System Initialization -/

/-- Initialize metabolic system with default parameters -/
def initMetabolicSystem (params : PhysiologicalParameters.BodyCompositionParams) : MetabolicEvidence := by
  let initialEnergy := {
    atpLevel := BuleReal.ofNat 9 / BuleReal.ofNat 10,  -- 90% ATP
    adpLevel := BuleReal.ofNat 8 / BuleReal.ofNat 10,  -- 8% ADP
    ampLevel := BuleReal.ofNat 2 / BuleReal.ofNat 10,  -- 2% AMP
    phosphocreatine := BuleReal.ofNat 7 / BuleReal.ofNat 10,  -- 70% PCr
    totalEnergy := params.totalBodyMass * BuleReal.ofNat 30,  -- 30 kcal/kg
    metabolicRate := params.totalBodyMass * BuleReal.ofNat 10 + BuleReal.ofNat 1500,  -- BMR
    energyDeficit := BuleReal.zero
  }
  
  let initialNutrients := {
    glucose := BuleReal.ofNat 90,  -- 90 mg/dL
    fattyAcids := BuleReal.ofNat 5,  -- 5 mg/dL
    aminoAcids := BuleReal.ofNat 2,  -- 2 mg/dL
    glycogen := BuleReal.ofNat 400,  -- 400g total
    fatStores := params.totalBodyMass * BuleReal.ofNat 15,  -- 15% body fat
    proteinStores := params.totalBodyMass * BuleReal.ofNat 4 / BuleReal.ofNat 100,  -- 4% muscle mass
    hydration := BuleReal.ofNat 60  -- 60% body water
  }
  
  let initialRespiration := {
    glycolysisRate := BuleReal.ofNat 5,
    krebsCycleRate := BuleReal.ofNat 4,
    oxidativePhosphorylation := BuleReal.ofNat 36,
    oxygenConsumption := BuleReal.ofNat 3,  -- 3 mL/kg/min at rest
    co2Production := BuleReal.ofNat 24,  -- 2.4 mL/kg/min
    respiratoryQuotient := BuleReal.ofNat 8 / BuleReal.ofNat 10,  -- 0.8
    mitochondrialEfficiency := BuleReal.ofNat 9 / BuleReal.ofNat 10
  }
  
  let initialThermal := {
    coreTemperature := BuleReal.ofNat 37,  -- 37°C
    skinTemperature := BuleReal.ofNat 335,  -- 33.5°C
    heatProduction := BuleReal.ofNat 80,  -- 80W at rest
    heatLoss := BuleReal.ofNat 80,
    sweatingRate := BuleReal.zero,
    shiveringThermogenesis := BuleReal.zero,
    vasomotorTone := BuleReal.ofNat 5 / BuleReal.ofNat 10
  }
  
  let initialFatigue := {
    muscularFatigue := BuleReal.zero,
    centralFatigue := BuleReal.zero,
    mentalFatigue := BuleReal.zero,
    recoveryRate := BuleReal.ofNat 9 / BuleReal.ofNat 10,
    sleepDebt := BuleReal.zero,
    circadianPhase := BuleReal.zero
  }
  
  exact {
    energyState := initialEnergy,
    nutrientPool := initialNutrients,
    cellularRespiration := initialRespiration,
    thermalState := initialThermal,
    fatigueState := initialFatigue,
    parameters := params,
    overallEfficiency := BuleReal.ofNat 8 / BuleReal.ofNat 10,
    timestamp := BuleReal.zero
  }

end MetabolismSystem
end Gnosis
