import Init
import Gnosis.GnosisNumbersAreStructural
import Gnosis.SpectralNoiseEquilibrium
import Gnosis.VacuumOverflow
import Gnosis.BiologicalTaxonomy
import Gnosis.DetailedTaxonomy
import Gnosis.EcosystemSimulation
import Gnosis.TaxonomicBrainBodyIntegration

/-!
# Integrated Ecosystem: Unified Taxonomy and Simulation Framework

This module integrates the detailed taxonomy system with the ecosystem simulation,
creating a comprehensive framework where complete taxonomic classification directly
influences ecological dynamics, evolutionary processes, and organism behavior.

Key integrations:
1. **Taxonomic-Ecological Link**: Full classification affects ecological interactions
2. **Evolutionary Hierarchy**: Evolution operates at all taxonomic levels
3. **Behavioral Taxonomy**: Taxonomic classification determines behavior patterns
4. **Cross-Kingdom Dynamics**: Detailed interactions across all taxonomic levels
-/

namespace Gnosis.IntegratedEcosystem

/-- Enhanced organism with complete taxonomic classification -/
structure TaxonomicOrganism where
  species : BiologicalTaxonomy.Species
  taxonomicPath : DetailedTaxonomy.TaxonomicPath
  brainConfiguration : TaxonomicIntegration.TaxonomicBrainConfiguration
  bodyConfiguration : TaxonomicIntegration.TaxonomicBodyConfiguration
  population : Ecosystem.Population
  ecologicalRole : GnosisNumbers ℕ
  evolutionaryPotential : GnosisNumbers ℕ
deriving Repr

/-- Enhanced ecological interaction with taxonomic context -/
structure TaxonomicInteraction where
  interactionType : Ecosystem.InteractionType
  organism1 : TaxonomicOrganism
  organism2 : TaxonomicOrganism
  taxonomicRelationship : GnosisNumbers ℕ -- How closely related
  ecologicalStrength : GnosisNumbers ℕ
  evolutionaryImpact : GnosisNumbers ℕ
  environmentalSensitivity : GnosisNumbers ℕ
deriving Repr

/-- Enhanced ecosystem with full taxonomic integration -/
structure IntegratedEcosystem where
  name : String
  environment : Ecosystem.Environment
  organisms : List TaxonomicOrganism
  interactions : List TaxonomicInteraction
  taxonomicDiversity : GnosisNumbers ℕ
  evolutionaryPressure : GnosisNumbers ℕ
  ecosystemComplexity : GnosisNumbers ℕ
  stabilityIndex : GnosisNumbers ℕ
  successionStage : GnosisNumbers ℕ
deriving Repr

/-- Calculate taxonomic relationship strength between organisms -/
def calculateTaxonomicRelationship (org1 : TaxonomicOrganism) (org2 : TaxonomicOrganism) : 
  GnosisNumbers ℕ :=
  let kingdomMatch := if org1.species.kingdom = org2.species.kingdom then 4 else 0
  let phylumSimilarity := GnosisNumbersAreStructural.structuralSimilarity 
                        org1.species.phylumProperties.bodyPlanComplexity 
                        org2.species.phylumProperties.bodyPlanComplexity
  let classSimilarity := GnosisNumbersAreStructural.structuralSimilarity 
                       (org1.taxonomicPath.properties.1.morphologicalComplexity)
                       (org2.taxonomicPath.properties.1.morphologicalComplexity)
  let orderSimilarity := GnosisNumbersAreStructural.structuralSimilarity 
                       (org1.taxonomicPath.properties.2.1.familyDiversity)
                       (org2.taxonomicPath.properties.2.1.familyDiversity)
  let familySimilarity := GnosisNumbersAreStructural.structuralSimilarity 
                        (org1.taxonomicPath.properties.2.2.morphologicalVariation)
                        (org2.taxonomicPath.properties.2.2.morphologicalVariation)
  let genusSimilarity := GnosisNumbersAreStructural.structuralSimilarity 
                       (org1.taxonomicPath.properties.2.3.morphologicalCohesion)
                       (org2.taxonomicPath.properties.2.3.morphologicalCohesion)
  GnosisNumbersAreStructural.structuralAggregate 
    [kingdomMatch, phylumSimilarity, classSimilarity, orderSimilarity, familySimilarity, genusSimilarity]

/-- Calculate ecological role based on taxonomic classification -/
def calculateEcologicalRole (organism : TaxonomicOrganism) : GnosisNumbers ℕ :=
  let kingdomRole := match organism.species.kingdom with
    | BiologicalTaxonomy.Kingdom.Animalia => 4 -- Consumers
    | BiologicalTaxonomy.Kingdom.Plantae => 1 -- Producers
    | BiologicalTaxonomy.Kingdom.Fungi => 2 -- Decomposers
    | BiologicalTaxonomy.Kingdom.Protista => 3 -- Various roles
    | BiologicalTaxonomy.Kingdom.Archaea => 0 -- Extreme environments
    | BiologicalTaxonomy.Kingdom.Bacteria => 2 -- Decomposers, nitrogen fixers
  let phylumContribution := organism.species.phylumProperties.bodyPlanComplexity
  let classContribution := organism.taxonomicPath.properties.1.ecologicalSpecialization
  let orderContribution := organism.taxonomicPath.properties.2.1.ecologicalRange
  let familyContribution := organism.taxonomicPath.properties.2.2.ecologicalSpecialization
  let genusContribution := organism.taxonomicPath.properties.2.3.ecologicalNiche
  GnosisNumbersAreStructural.structuralCombine 
    [kingdomRole, phylumContribution, classContribution, orderContribution, familyContribution, genusContribution]

/-- Calculate evolutionary potential based on taxonomic position -/
def calculateEvolutionaryPotential (organism : TaxonomicOrganism) : GnosisNumbers ℕ :=
  let geneticBase := organism.species.geneticComplexity
  let diversityFactor := organism.population.geneticDiversity
  let adaptabilityFactor := organism.species.adaptabilityIndex
  let taxonomicNovelty := organism.species.phylumProperties.evolutionaryNovelty
  let classNovelty := organism.taxonomicPath.properties.1.evolutionaryNovelty
  let orderRadiation := organism.taxonomicPath.properties.2.2.adaptiveRadiation
  let familyCoherence := organism.taxonomicPath.properties.2.2.evolutionaryCoherence
  let genusRecentness := organism.taxonomicPath.properties.2.3.evolutionaryRecentness
  let evolutionaryScore := GnosisNumbersAreStructural.structuralAggregate 
                         [geneticBase, diversityFactor, adaptabilityFactor, taxonomicNovelty, 
                          classNovelty, orderRadiation, familyCoherence, genusRecentness]
  SpectralNoiseEquilibrium.evolutionaryPotential evolutionaryScore diversityFactor

/-- Create taxonomic interaction with full context -/
def createTaxonomicInteraction (org1 : TaxonomicOrganism) (org2 : TaxonomicOrganism) 
  (interactionType : Ecosystem.InteractionType) : TaxonomicInteraction :=
  let taxonomicRel := calculateTaxonomicRelationship org1 org2
  let ecologicalStrength := match interactionType with
    | Ecosystem.InteractionType.PredatorPrey => 
        VacuumOverflow.vacuumPredation org1.population.individuals org2.population.individuals
    | Ecosystem.InteractionType.Mutualism => 
        GnosisNumbersAreStructural.structuralSynergy org1.ecologicalRole org2.ecologicalRole
    | Ecosystem.InteractionType.Competition => 
        VacuumOverflow.vacuumCompetition org1.population.individuals org2.population.individuals
    | Ecosystem.InteractionType.Parasitism => 
        GnosisNumbersAreStructural.structuralParasitism org1.ecologicalRole org2.ecologicalRole
    | _ => GnosisNumbersAreStructural.structuralNeutral org1.ecologicalRole org2.ecologicalRole
  let evolutionaryImpact := GnosisNumbersAreStructural.structuralEvolutionaryImpact 
                         taxonomicRel 
                         ecologicalStrength
  let environmentalSensitivity := SpectralNoiseEquilibrium.environmentalSensitivity 
                               taxonomicRel 
                                 (org1.species.ecologicalNiche + org2.species.ecologicalNiche)
  {
    interactionType := interactionType,
    organism1 := org1,
    organism2 := org2,
    taxonomicRelationship := taxonomicRel,
    ecologicalStrength := ecologicalStrength,
    evolutionaryImpact := evolutionaryImpact,
    environmentalSensitivity := environmentalSensitivity
  }

/-- Update organism based on taxonomic interactions -/
def updateOrganismFromInteractions (organism : TaxonomicOrganism) 
  (interactions : List TaxonomicInteraction) : TaxonomicOrganism :=
  let relevantInteractions := interactions.filter (fun inter =>
    inter.organism1 = organism ∨ inter.organism2 = organism
  )
  let totalEffect := relevantInteractions.foldl (fun acc inter =>
    let effect := if inter.organism1 = organism 
                  then inter.ecologicalStrength 
                  else -inter.ecologicalStrength
    acc + effect
  ) 0
  let newIndividuals := GnosisNumbersAreStructural.structuralAdd 
                     organism.population.individuals 
                     totalEffect
  let newPopulation := {
    species := organism.population.species,
    individuals := newIndividuals,
    birthRate := organism.population.birthRate,
    deathRate := organism.population.deathRate,
    carryingCapacity := organism.population.carryingCapacity,
    geneticDiversity := organism.population.geneticDiversity,
    ageDistribution := organism.population.ageDistribution,
    healthIndex := GnosisNumbersAreStructural.structuralHealth 
                 newIndividuals 
                 organism.population.carryingCapacity
  }
  let evolutionaryChange := GnosisNumbersAreStructural.structuralEvolution 
                          organism.evolutionaryPotential 
                          (relevantInteractions.map (·.evolutionaryImpact) |> List.foldl GnosisNumbersAreStructural.structuralCombine 0)
  {
    species := organism.species,
    taxonomicPath := organism.taxonomicPath,
    brainConfiguration := organism.brainConfiguration,
    bodyConfiguration := organism.bodyConfiguration,
    population := newPopulation,
    ecologicalRole := organism.ecologicalRole,
    evolutionaryPotential := evolutionaryChange
  }

/-- Simulate evolutionary processes at all taxonomic levels -/
def simulateEvolutionaryStep (ecosystem : IntegratedEcosystem) : IntegratedEcosystem :=
  let evolvedOrganisms := ecosystem.organisms.map (fun organism =>
    let selectionPressure := ecosystem.evolutionaryPressure
    let adaptationRate := GnosisNumbersAreStructural.structuralAdapt 
                        organism.evolutionaryPotential 
                        selectionPressure
    let evolvedSpecies := BiologicalTaxonomy.Species.evolve organism.species selectionPressure
    let evolvedPopulation := Ecosystem.Population.evolve organism.population selectionPressure
    let evolvedEcologicalRole := calculateEcologicalRole {
      species := evolvedSpecies,
      taxonomicPath := organism.taxonomicPath,
      brainConfiguration := organism.brainConfiguration,
      bodyConfiguration := organism.bodyConfiguration,
      population := evolvedPopulation,
      ecologicalRole := organism.ecologicalRole,
      evolutionaryPotential := organism.evolutionaryPotential
    }
    let evolvedPotential := calculateEvolutionaryPotential {
      species := evolvedSpecies,
      taxonomicPath := organism.taxonomicPath,
      brainConfiguration := organism.brainConfiguration,
      bodyConfiguration := organism.bodyConfiguration,
      population := evolvedPopulation,
      ecologicalRole := evolvedEcologicalRole,
      evolutionaryPotential := organism.evolutionaryPotential
    }
    {
      species := evolvedSpecies,
      taxonomicPath := organism.taxonomicPath,
      brainConfiguration := organism.brainConfiguration,
      bodyConfiguration := organism.bodyConfiguration,
      population := evolvedPopulation,
      ecologicalRole := evolvedEcologicalRole,
      evolutionaryPotential := evolvedPotential
    }
  )
  {
    name := ecosystem.name,
    environment := ecosystem.environment,
    organisms := evolvedOrganisms,
    interactions := ecosystem.interactions,
    taxonomicDiversity := ecosystem.taxonomicDiversity,
    evolutionaryPressure := GnosisNumbersAreStructural.structuralFluctuate 
                         ecosystem.evolutionaryPressure 
                         0.1,
    ecosystemComplexity := ecosystem.ecosystemComplexity,
    stabilityIndex := ecosystem.stabilityIndex,
    successionStage := GnosisNumbersAreStructural.structuralProgress 
                     ecosystem.successionStage 
                     ecosystem.stabilityIndex
  }

/-- Calculate ecosystem complexity based on taxonomic diversity -/
def calculateEcosystemComplexity (organisms : List TaxonomicOrganism) : GnosisNumbers ℕ :=
  let kingdomDiversity := organisms.map (·.species.kingdom) |> List.eraseDup.length |> GnosisNumbers.ofNat
  let phylumDiversity := organisms.map (·.species.phylumProperties.bodyPlanComplexity) |> List.eraseDup.length |> GnosisNumbers.ofNat
  let classDiversity := organisms.map (fun org => org.taxonomicPath.properties.1.morphologicalComplexity) |> List.eraseDup.length |> GnosisNumbers.ofNat
  let orderDiversity := organisms.map (fun org => org.taxonomicPath.properties.2.1.familyDiversity) |> List.eraseDup.length |> GnosisNumbers.ofNat
  let familyDiversity := organisms.map (fun org => org.taxonomicPath.properties.2.2.morphologicalVariation) |> List.eraseDup.length |> GnosisNumbers.ofNat
  let genusDiversity := organisms.map (fun org => org.taxonomicPath.properties.2.3.morphologicalCohesion) |> List.eraseDup.length |> GnosisNumbers.ofNat
  let totalDiversity := GnosisNumbersAreStructural.structuralAggregate 
                      [kingdomDiversity, phylumDiversity, classDiversity, orderDiversity, familyDiversity, genusDiversity]
  let interactionComplexity := organisms.length * (organisms.length - 1) / 2 |> GnosisNumbers.ofNat
  GnosisNumbersAreStructural.structuralCombine [totalDiversity, interactionComplexity]

/-- Simulate one complete time step of integrated ecosystem -/
def simulateIntegratedStep (ecosystem : IntegratedEcosystem) : IntegratedEcosystem :=
  -- Update organisms based on environmental conditions
  let environmentAffectedOrganisms := ecosystem.organisms.map (fun organism =>
    let affectedPopulation := Ecosystem.Environment.affectPopulation 
                             ecosystem.environment 
                             organism.population
    {
      species := organism.species,
      taxonomicPath := organism.taxonomicPath,
      brainConfiguration := organism.brainConfiguration,
      bodyConfiguration := organism.bodyConfiguration,
      population := affectedPopulation,
      ecologicalRole := organism.ecologicalRole,
      evolutionaryPotential := organism.evolutionaryPotential
    }
  )
  
  -- Update organisms based on interactions
  let interactionAffectedOrganisms := environmentAffectedOrganisms.map 
    (updateOrganismFromInteractions · ecosystem.interactions)
  
  -- Simulate evolutionary processes
  let evolvedOrganisms := simulateEvolutionaryStep {
    name := ecosystem.name,
    environment := ecosystem.environment,
    organisms := interactionAffectedOrganisms,
    interactions := ecosystem.interactions,
    taxonomicDiversity := ecosystem.taxonomicDiversity,
    evolutionaryPressure := ecosystem.evolutionaryPressure,
    ecosystemComplexity := ecosystem.ecosystemComplexity,
    stabilityIndex := ecosystem.stabilityIndex,
    successionStage := ecosystem.successionStage
  }
  
  -- Recalculate ecosystem metrics
  let newTaxonomicDiversity := calculateEcosystemComplexity evolvedOrganisms.organisms
  let newStability := VacuumOverflow.ecosystemStability 
                    (evolvedOrganisms.organisms.map (·.population.individuals) |> List.foldl GnosisNumbersAreStructural.structuralCombine 0)
                    newTaxonomicDiversity
  
  {
    name := ecosystem.name,
    environment := ecosystem.environment,
    organisms := evolvedOrganisms.organisms,
    interactions := ecosystem.interactions,
    taxonomicDiversity := newTaxonomicDiversity,
    evolutionaryPressure := evolvedOrganisms.evolutionaryPressure,
    ecosystemComplexity := newTaxonomicDiversity,
    stabilityIndex := newStability,
    successionStage := evolvedOrganisms.successionStage
  }

/-- Create integrated ecosystem from basic species list -/
def createIntegratedEcosystem (name : String) 
  (species : List BiologicalTaxonomy.Species) : IntegratedEcosystem :=
  let organisms := species.map (fun sp =>
    let taxonomicPath := DetailedTaxonomy.buildTaxonomicPath sp
    let brainConfig := TaxonomicIntegration.TaxonomicBrainConfiguration.fromSpecies sp
    let bodyConfig := TaxonomicIntegration.TaxonomicBodyConfiguration.fromSpecies sp
    let population := {
      species := sp,
      individuals := 100, -- Default population
      birthRate := 1.0,
      deathRate := 0.5,
      carryingCapacity := 1000,
      geneticDiversity := 0.8,
      ageDistribution := [20, 30, 25, 15, 10], -- Age distribution
      healthIndex := 0.9
    }
    let ecologicalRole := calculateEcologicalRole {
      species := sp,
      taxonomicPath := taxonomicPath,
      brainConfiguration := brainConfig,
      bodyConfiguration := bodyConfig,
      population := population,
      ecologicalRole := 0,
      evolutionaryPotential := 0
    }
    let evolutionaryPotential := calculateEvolutionaryPotential {
      species := sp,
      taxonomicPath := taxonomicPath,
      brainConfiguration := brainConfig,
      bodyConfiguration := bodyConfig,
      population := population,
      ecologicalRole := ecologicalRole,
      evolutionaryPotential := 0
    }
    {
      species := sp,
      taxonomicPath := taxonomicPath,
      brainConfiguration := brainConfig,
      bodyConfiguration := bodyConfig,
      population := population,
      ecologicalRole := ecologicalRole,
      evolutionaryPotential := evolutionaryPotential
    }
  )
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
  let taxonomicDiversity := calculateEcosystemComplexity organisms
  {
    name := name,
    environment := environment,
    organisms := organisms,
    interactions := [], -- Would be populated based on ecological relationships
    taxonomicDiversity := taxonomicDiversity,
    evolutionaryPressure := 1.0,
    ecosystemComplexity := taxonomicDiversity,
    stabilityIndex := 0.8,
    successionStage := 1
  }

end Gnosis.IntegratedEcosystem
