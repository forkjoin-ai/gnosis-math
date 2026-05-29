import Init
import Gnosis.GnosisNumbersAreStructural
import Gnosis.SpectralNoiseEquilibrium
import Gnosis.VacuumOverflow
import Gnosis.BiologicalTaxonomy
import Gnosis.TaxonomicBrainBodyIntegration
import Gnosis.CrossKingdomIntegration

/-!
# Ecosystem Simulation: Dynamic Biological System Modeling

This module implements a comprehensive ecosystem simulation framework using the complete
taxonomy system we've built. It models ecological interactions, evolutionary dynamics,
energy flow, and population dynamics across all kingdoms of life.

Key concepts:
1. **Cross-Kingdom Interactions**: Predator-prey, symbiosis, competition across all domains
2. **Evolutionary Dynamics**: Natural selection, adaptation, speciation in real-time
3. **Energy Flow**: Food webs, trophic levels, energy transfer efficiency
4. **Population Dynamics**: Birth rates, death rates, carrying capacity, competition
5. **Environmental Factors**: Climate, resources, disturbance, succession
-/

namespace Gnosis.Ecosystem

/-- Environmental conditions and resources -/
structure Environment where
  temperature : GnosisNumbers ℕ        -- Ambient temperature
  humidity : GnosisNumbers ℕ          -- Moisture availability
  lightIntensity : GnosisNumbers ℕ    -- Solar radiation
  nutrientAvailability : GnosisNumbers ℕ -- Soil/water nutrients
  oxygenLevel : GnosisNumbers ℕ       -- Atmospheric oxygen
  carbonDioxideLevel : GnosisNumbers ℕ -- Atmospheric CO2
  pH : GnosisNumbers ℕ               -- Acidity/alkalinity
  disturbanceFrequency : GnosisNumbers ℕ -- Environmental disturbances
deriving Repr

/-- Population statistics for a species -/
structure Population where
  species : BiologicalTaxonomy.Species
  individuals : GnosisNumbers ℕ      -- Population size
  birthRate : GnosisNumbers ℕ         -- Reproduction rate
  deathRate : GnosisNumbers ℕ         -- Mortality rate
  carryingCapacity : GnosisNumbers ℕ -- Maximum sustainable population
  geneticDiversity : GnosisNumbers ℕ -- Genetic variation
  ageDistribution : List GnosisNumbers ℕ -- Age structure
  healthIndex : GnosisNumbers ℕ       -- Overall population health
deriving Repr

/-- Ecological interaction types -/
inductive InteractionType where
  | PredatorPrey      -- One organism consumes another
  | Herbivory         -- Plant consumption by animals
  | Parasitism        -- One benefits at host's expense
  | Mutualism         -- Both species benefit
  | Commensalism      -- One benefits, other unaffected
  | Competition       -- Both compete for resources
  | Amensalism        -- One harmed, other unaffected
  | Neutralism        -- No significant interaction
deriving Repr, DecidableEq

/-- Ecological interaction between two populations -/
structure EcologicalInteraction where
  interactionType : InteractionType
  population1 : Population
  population2 : Population
  interactionStrength : GnosisNumbers ℕ -- Magnitude of effect
  frequency : GnosisNumbers ℕ          -- How often interaction occurs
  environmentalDependency : GnosisNumbers ℕ -- Environmental sensitivity
deriving Repr

/-- Food web node representing a trophic position -/
structure TrophicNode where
  population : Population
  trophicLevel : GnosisNumbers ℕ      -- Position in food chain
  energyInput : GnosisNumbers ℕ       -- Energy consumed
  energyOutput : GnosisNumbers ℕ      -- Energy transferred up
  assimilationEfficiency : GnosisNumbers ℕ -- Energy conversion rate
  biomass : GnosisNumbers ℕ           -- Total living mass
deriving Repr

/-- Complete ecosystem model -/
structure Ecosystem where
  name : String
  environment : Environment
  populations : List Population
  interactions : List EcologicalInteraction
  trophicWeb : List TrophicNode
  totalBiomass : GnosisNumbers ℕ
  biodiversityIndex : GnosisNumbers ℕ
  stabilityIndex : GnosisNumbers ℕ
  successionStage : GnosisNumbers ℕ   -- Ecological succession phase
deriving Repr

/-- Environmental change effects on populations -/
def Environment.affectPopulation (env : Environment) (pop : Population) : Population :=
  let temperatureEffect := SpectralNoiseEquilibrium.temperatureImpact 
                          env.temperature 
                          pop.species.ecologicalNiche
  let humidityEffect := GnosisNumbersAreStructural.structuralResponse 
                      env.humidity 
                      pop.species.adaptabilityIndex
  let nutrientEffect := VacuumOverflow.vacuumGrowth 
                      env.nutrientAvailability 
                      pop.carryingCapacity
  let optimalConditions := GnosisNumbersAreStructural.structuralOptimal 
                         [temperatureEffect, humidityEffect, nutrientEffect]
  let adjustedBirthRate := GnosisNumbersAreStructural.structuralScale 
                         pop.birthRate 
                         optimalConditions
  let adjustedDeathRate := GnosisNumbersAreStructural.structuralInverse 
                         pop.deathRate 
                         optimalConditions
  let newIndividuals := GnosisNumbersAreStructural.structuralGrowth 
                      pop.individuals 
                      (adjustedBirthRate - adjustedDeathRate)
  let newCarryingCapacity := GnosisNumbersAreStructural.structuralAdapt 
                           pop.carryingCapacity 
                           nutrientEffect
  {
    species := pop.species,
    individuals := newIndividuals,
    birthRate := adjustedBirthRate,
    deathRate := adjustedDeathRate,
    carryingCapacity := newCarryingCapacity,
    geneticDiversity := pop.geneticDiversity,
    ageDistribution := pop.ageDistribution,
    healthIndex := GnosisNumbersAreStructural.structuralHealth 
                 newIndividuals 
                 newCarryingCapacity
  }

/-- Calculate interaction effects between populations -/
def EcologicalInteraction.calculateEffect (interaction : EcologicalInteraction) : 
  GnosisNumbers ℕ × GnosisNumbers ℕ :=
  let baseEffect := GnosisNumbersAreStructural.structuralMultiply 
                   interaction.interactionStrength 
                   interaction.frequency
  let environmentalModifier := SpectralNoiseEquilibrium.environmentalModulation 
                             interaction.environmentalDependency 
                             baseEffect
  match interaction.interactionType with
  | InteractionType.PredatorPrey => 
      let predationPressure := VacuumOverflow.vacuumPredation 
                              baseEffect 
                              interaction.population1.individuals
      let preyLoss := GnosisNumbersAreStructural.structuralSubtract 
                    interaction.population2.individuals 
                    predationPressure
      let predatorGain := GnosisNumbersAreStructural.structuralScale 
                        predationPressure 
                        environmentalModifier
      (predatorGain, -preyLoss)
  | InteractionType.Herbivory => 
      let plantLoss := GnosisNumbersAreStructural.structuralMultiply 
                     baseEffect 
                     interaction.population1.individuals
      let herbivoreGain := GnosisNumbersAreStructural.structuralScale 
                         plantLoss 
                         environmentalModifier
      (herbivoreGain, -plantLoss)
  | InteractionType.Mutualism => 
      let mutualBenefit := GnosisNumbersAreStructural.structuralScale 
                        baseEffect 
                        environmentalModifier
      (mutualBenefit, mutualBenefit)
  | InteractionType.Competition => 
      let competitionCost := VacuumOverflow.vacuumCompetition 
                          baseEffect 
                          (interaction.population1.individuals + interaction.population2.individuals)
      (-competitionCost, -competitionCost)
  | InteractionType.Parasitism => 
      let hostCost := GnosisNumbersAreStructural.structuralMultiply 
                    baseEffect 
                    interaction.population2.individuals
      let parasiteBenefit := GnosisNumbersAreStructural.structuralScale 
                          hostCost 
                          environmentalModifier
      (parasiteBenefit, -hostCost)
  | InteractionType.Commensalism => 
      let commensalBenefit := GnosisNumbersAreStructural.structuralScale 
                            baseEffect 
                            environmentalModifier
      (commensalBenefit, 0)
  | InteractionType.Amensalism => 
      let amensalHarm := GnosisNumbersAreStructural.structuralMultiply 
                       baseEffect 
                       interaction.population2.individuals
      (0, -amensalHarm)
  | InteractionType.Neutralism => 
      (0, 0)

/-- Update populations based on all interactions -/
def updatePopulationsFromInteractions (populations : List Population) 
  (interactions : List EcologicalInteraction) : List Population :=
  let interactionEffects := interactions.map EcologicalInteraction.calculateEffect
  let populationEffects := List.range populations.length |> List.map (fun i =>
    let relevantEffects := interactionEffects.enum.filter (fun (j, (effect1, effect2)) =>
      (j = i ∧ effect1 ≠ 0) ∨ (j - 1 = i ∧ effect2 ≠ 0)
    )
    let totalEffect := relevantEffects.foldl (fun acc (_, (e1, e2)) => 
      acc + if e1 ≠ 0 then e1 else e2
    ) 0
    totalEffect
  )
  populations.zip populationEffects |> List.map (fun (pop, effect) =>
    let newIndividuals := GnosisNumbersAreStructural.structuralAdd 
                       pop.individuals 
                       effect
    let newHealth := GnosisNumbersAreStructural.structuralHealth 
                   newIndividuals 
                   pop.carryingCapacity
    {
      species := pop.species,
      individuals := newIndividuals,
      birthRate := pop.birthRate,
      deathRate := pop.deathRate,
      carryingCapacity := pop.carryingCapacity,
      geneticDiversity := pop.geneticDiversity,
      ageDistribution := pop.ageDistribution,
      healthIndex := newHealth
    }
  )

/-- Calculate energy flow through trophic levels -/
def TrophicNode.calculateEnergyFlow (node : TrophicNode) : TrophicNode :=
  let energyAssimilated := GnosisNumbersAreStructural.structuralMultiply 
                        node.energyInput 
                        node.assimilationEfficiency
  let energyLost := GnosisNumbersAreStructural.structuralSubtract 
                  node.energyInput 
                  energyAssimilated
  let newBiomass := GnosisNumbersAreStructural.structuralGrowth 
                  node.biomass 
                  energyAssimilated
  {
    population := node.population,
    trophicLevel := node.trophicLevel,
    energyInput := node.energyInput,
    energyOutput := energyAssimilated,
    assimilationEfficiency := node.assimilationEfficiency,
    biomass := newBiomass
  }

/-- Simulate one time step of ecosystem dynamics -/
def Ecosystem.simulateStep (ecosystem : Ecosystem) : Ecosystem :=
  -- Update populations based on environmental conditions
  let environmentAffectedPopulations := ecosystem.populations.map 
    (Environment.affectPopulation ecosystem.environment)
  
  -- Update populations based on ecological interactions
  let interactionAffectedPopulations := updatePopulationsFromInteractions 
    environmentAffectedPopulations 
    ecosystem.interactions
  
  -- Update trophic dynamics
  let updatedTrophicWeb := ecosystem.trophicWeb.map TrophicNode.calculateEnergyFlow
  
  -- Calculate new ecosystem metrics
  let newTotalBiomass := updatedTrophicWeb.map (·.biomass) 
                      |> List.foldl GnosisNumbersAreStructural.structuralCombine 0
  let newBiodiversity := SpectralNoiseEquilibrium.calculateBiodiversity 
                      interactionAffectedPopulations
  let newStability := VacuumOverflow.ecosystemStability 
                    newTotalBiomass 
                    newBiodiversity
  
  {
    name := ecosystem.name,
    environment := ecosystem.environment,
    populations := interactionAffectedPopulations,
    interactions := ecosystem.interactions,
    trophicWeb := updatedTrophicWeb,
    totalBiomass := newTotalBiomass,
    biodiversityIndex := newBiodiversity,
    stabilityIndex := newStability,
    successionStage := GnosisNumbersAreStructural.structuralProgress 
                     ecosystem.successionStage 
                     newStability
  }

/-- Evolutionary adaptation through natural selection -/
def Population.evolve (pop : Population) (selectionPressure : GnosisNumbers ℕ) : Population :=
  let adaptationRate := GnosisNumbersAreStructural.structuralAdapt 
                      pop.geneticDiversity 
                      selectionPressure
  let evolvedAdaptability := GnosisNumbersAreStructural.structuralEnhance 
                           pop.species.adaptabilityIndex 
                           adaptationRate
  let evolvedSpecies := { pop.species with 
    adaptabilityIndex := evolvedAdaptability,
    geneticComplexity := GnosisNumbersAreStructural.structuralEvolve 
                       pop.species.geneticComplexity 
                       selectionPressure
  }
  let newBirthRate := GnosisNumbersAreStructural.structuralAdapt 
                    pop.birthRate 
                    adaptationRate
  let newDeathRate := GnosisNumbersAreStructural.structuralInverse 
                    pop.deathRate 
                    adaptationRate
  let newGeneticDiversity := SpectralNoiseEquilibrium.geneticDrift 
                           pop.geneticDiversity 
                           selectionPressure
  {
    species := evolvedSpecies,
    individuals := pop.individuals,
    birthRate := newBirthRate,
    deathRate := newDeathRate,
    carryingCapacity := pop.carryingCapacity,
    geneticDiversity := newGeneticDiversity,
    ageDistribution := pop.ageDistribution,
    healthIndex := pop.healthIndex
  }

/-- Speciation event - population splits into new species -/
def Population.speciate (pop : Population) (isolationFactor : GnosisNumbers ℕ) : 
  Population × Population :=
  let divergence := GnosisNumbersAreStructural.structuralDiverge 
                  pop.geneticDiversity 
                  isolationFactor
  let populationSplit := GnosisNumbersAreStructural.structuralDivide 
                       pop.individuals 
                       2
  let species1 := { pop.species with 
    geneticComplexity := GnosisNumbersAreStructural.structuralAdd 
                       pop.species.geneticComplexity 
                       divergence
  }
  let species2 := { pop.species with 
    geneticComplexity := GnosisNumbersAreStructural.structuralSubtract 
                       pop.species.geneticComplexity 
                       divergence
  }
  let pop1 := {
    species := species1,
    individuals := populationSplit,
    birthRate := pop.birthRate,
    deathRate := pop.deathRate,
    carryingCapacity := GnosisNumbersAreStructural.structuralDivide 
                      pop.carryingCapacity 
                      2,
    geneticDiversity := GnosisNumbersAreStructural.structuralMultiply 
                      pop.geneticDiversity 
                      isolationFactor,
    ageDistribution := pop.ageDistribution,
    healthIndex := pop.healthIndex
  }
  let pop2 := {
    species := species2,
    individuals := populationSplit,
    birthRate := pop.birthRate,
    deathRate := pop.deathRate,
    carryingCapacity := GnosisNumbersAreStructural.structuralDivide 
                      pop.carryingCapacity 
                      2,
    geneticDiversity := GnosisNumbersAreStructural.structuralMultiply 
                      pop.geneticDiversity 
                      (1 - isolationFactor),
    ageDistribution := pop.ageDistribution,
    healthIndex := pop.healthIndex
  }
  (pop1, pop2)

/-- Create a simple ecosystem for testing -/
def Ecosystem.createSimple (name : String) : Ecosystem :=
  let environment := {
    temperature := 20,
    humidity := 60,
    lightIntensity := 100,
    nutrientAvailability := 50,
    oxygenLevel := 21,
    carbonDioxideLevel := 0.04,
    pH := 7,
    disturbanceFrequency := 1
  }
  let populations := [] -- Would be populated with actual species
  let interactions := [] -- Would be populated with actual interactions
  let trophicWeb := [] -- Would be populated with actual trophic nodes
  {
    name := name,
    environment := environment,
    populations := populations,
    interactions := interactions,
    trophicWeb := trophicWeb,
    totalBiomass := 0,
    biodiversityIndex := 0,
    stabilityIndex := 0,
    successionStage := 1
  }

end Gnosis.Ecosystem
