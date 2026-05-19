import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyTeachingIntegrityOntologyWitness

/-!
# Science and Health, Chapter XIII -- Integrity, Ontology, and Right Motive

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:18780-19145`.

Bounded section: 455:27-464:27. This teaching unit closes the chapter by
requiring integrity of method, rejecting concessions to matter, locating
Mind-healing in ontology, distinguishing sickness confession from sin
confession, defining mental anatomy and spiritual obstetrics, and ending with
right motive rather than personality.
-/

inductive TeachingIntegrityMoment where
  | fountainCannotBearSweetAndBitter
  | chicaneryImpossibleUnderTruth
  | onePrincipleOneMethod
  | dishonestyBetraysChristCure
  | noMatterBasisForMetaphysics
  | textbookIndispensable
  | truthUncontaminatedByHypotheses
  | cannotCureAndCauseDisease
  | excellenceRequiresDirectLabor
  | noOppositeRule
  | mentalCharlatanismTwoPrinciples
  | divinityAlwaysReady
  | scientistLawUntoHimself
  | livingTeachingHealingProof
  | advancementRequiresSacrifice
  | erringMortalMindDangerous
  | goodTreeGoodFruit
  | ontologyUnderliesPractice
  | moralPharmacySpiritualMedicine
  | sicknessSolidConviction
  | smatterersMischief
  | earlyTeachingClarified
  | inductionFromProvedPart
  | spiritualSenseIlluminesScience
  | sicknessAdmissionDiffersFromSin
  | diseaseMentallyUnseen
  | systematicGrowthRequired
  | dividedLoyaltyReapsError
  | anatomyMentalSelfKnowledge
  | thoughtQualityQuantityOrigin
  | spiritualObstetricsNewIdea
  | quickDecisionAgainstError
  | spiritualLawNotDrugs
  | authorSeclusionLabor
  | temporarySurgeryWhenPainOverwhelms
  | principleNotPersonality
  | falsityCannotOverthrowEthics
deriving DecidableEq, Repr

def teachingIntegrityTrace : List TeachingIntegrityMoment :=
  [ TeachingIntegrityMoment.fountainCannotBearSweetAndBitter
  , TeachingIntegrityMoment.chicaneryImpossibleUnderTruth
  , TeachingIntegrityMoment.onePrincipleOneMethod
  , TeachingIntegrityMoment.dishonestyBetraysChristCure
  , TeachingIntegrityMoment.noMatterBasisForMetaphysics
  , TeachingIntegrityMoment.textbookIndispensable
  , TeachingIntegrityMoment.truthUncontaminatedByHypotheses
  , TeachingIntegrityMoment.cannotCureAndCauseDisease
  , TeachingIntegrityMoment.excellenceRequiresDirectLabor
  , TeachingIntegrityMoment.noOppositeRule
  , TeachingIntegrityMoment.mentalCharlatanismTwoPrinciples
  , TeachingIntegrityMoment.divinityAlwaysReady
  , TeachingIntegrityMoment.scientistLawUntoHimself
  , TeachingIntegrityMoment.livingTeachingHealingProof
  , TeachingIntegrityMoment.advancementRequiresSacrifice
  , TeachingIntegrityMoment.erringMortalMindDangerous
  , TeachingIntegrityMoment.goodTreeGoodFruit
  , TeachingIntegrityMoment.ontologyUnderliesPractice
  , TeachingIntegrityMoment.moralPharmacySpiritualMedicine
  , TeachingIntegrityMoment.sicknessSolidConviction
  , TeachingIntegrityMoment.smatterersMischief
  , TeachingIntegrityMoment.earlyTeachingClarified
  , TeachingIntegrityMoment.inductionFromProvedPart
  , TeachingIntegrityMoment.spiritualSenseIlluminesScience
  , TeachingIntegrityMoment.sicknessAdmissionDiffersFromSin
  , TeachingIntegrityMoment.diseaseMentallyUnseen
  , TeachingIntegrityMoment.systematicGrowthRequired
  , TeachingIntegrityMoment.dividedLoyaltyReapsError
  , TeachingIntegrityMoment.anatomyMentalSelfKnowledge
  , TeachingIntegrityMoment.thoughtQualityQuantityOrigin
  , TeachingIntegrityMoment.spiritualObstetricsNewIdea
  , TeachingIntegrityMoment.quickDecisionAgainstError
  , TeachingIntegrityMoment.spiritualLawNotDrugs
  , TeachingIntegrityMoment.authorSeclusionLabor
  , TeachingIntegrityMoment.temporarySurgeryWhenPainOverwhelms
  , TeachingIntegrityMoment.principleNotPersonality
  , TeachingIntegrityMoment.falsityCannotOverthrowEthics
  ]

structure TeachingIntegrityOntology where
  oneMethodRequired : Bool
  textbookCentral : Bool
  matterBasisRejected : Bool
  ontologyUnderPractice : Bool
  diseaseMentallyUnseen : Bool
  anatomyIsThoughtDissection : Bool
  spiritualObstetricsNewBirth : Bool
  rightMotiveOverPersonality : Bool
deriving DecidableEq, Repr

def teachingIntegrityOntology : TeachingIntegrityOntology where
  oneMethodRequired := true
  textbookCentral := true
  matterBasisRejected := true
  ontologyUnderPractice := true
  diseaseMentallyUnseen := true
  anatomyIsThoughtDissection := true
  spiritualObstetricsNewBirth := true
  rightMotiveOverPersonality := true

theorem eddy_teaching_integrity_ontology_witness :
    teachingIntegrityTrace.length = 37
    ∧ teachingIntegrityTrace.head? =
      some TeachingIntegrityMoment.fountainCannotBearSweetAndBitter
    ∧ teachingIntegrityTrace.getLast? =
      some TeachingIntegrityMoment.falsityCannotOverthrowEthics
    ∧ teachingIntegrityOntology.oneMethodRequired = true
    ∧ teachingIntegrityOntology.textbookCentral = true
    ∧ teachingIntegrityOntology.matterBasisRejected = true
    ∧ teachingIntegrityOntology.ontologyUnderPractice = true
    ∧ teachingIntegrityOntology.diseaseMentallyUnseen = true
    ∧ teachingIntegrityOntology.anatomyIsThoughtDissection = true
    ∧ teachingIntegrityOntology.spiritualObstetricsNewBirth = true
    ∧ teachingIntegrityOntology.rightMotiveOverPersonality = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyTeachingIntegrityOntologyWitness
end Gnosis.Witnesses.Eddy
