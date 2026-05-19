import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyPracticeRelapseGovernmentWitness

/-!
# Science and Health, Chapter XII -- Relapse and True Government

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:17380-17700`.

Bounded section: 415:1-420:9. This practice unit treats inflammation, sedatives,
the so-called physical ego, encouragement, disease made unreal, moral hindrance,
relapse, fear, and true government as one therapeutic ledger: thought produces
the apparent evidence, Truth removes the mental image, and Spirit rather than
matter governs man.
-/

inductive RelapseGovernmentMoment where
  | inflammationFearState
  | diseaseNoTruthFoundation
  | thoughtMovesSystem
  | opiatesQuietThoughtTemporarily
  | truthCalmsAndInstructs
  | etherizationShowsPainMental
  | sedativeLeavesBeliefCause
  | physicalEgoMortalMind
  | patientToldOnlyUsefulTruth
  | thoughtTurnedHigher
  | courageStrengthProportional
  | causationMindSpiritualLaw
  | witnessAgainstPleaSilenced
  | sicknessDreamAwakening
  | diseaseMadeUnrealToPatient
  | mindControlExplainedWhenBearable
  | materialPleasurePainBeliefDestroyed
  | honestPleaHeals
  | sicknessNoMoreRealThanSin
  | truthfulArgumentsConferHarmony
  | moralityIncludedInTreatment
  | diseaseFormsWakingDreams
  | lurkingErrorPerpetuatesDisease
  | relapseCauseMetMentally
  | diseaseNoIntelligenceToMove
  | observeMindNotBody
  | conquerOwnFearAndPatientFear
  | truthPreventsMetastasis
  | spiritGovernsMan
  | errorCannotProduceReluctance
deriving DecidableEq, Repr

def relapseGovernmentTrace : List RelapseGovernmentMoment :=
  [ RelapseGovernmentMoment.inflammationFearState
  , RelapseGovernmentMoment.diseaseNoTruthFoundation
  , RelapseGovernmentMoment.thoughtMovesSystem
  , RelapseGovernmentMoment.opiatesQuietThoughtTemporarily
  , RelapseGovernmentMoment.truthCalmsAndInstructs
  , RelapseGovernmentMoment.etherizationShowsPainMental
  , RelapseGovernmentMoment.sedativeLeavesBeliefCause
  , RelapseGovernmentMoment.physicalEgoMortalMind
  , RelapseGovernmentMoment.patientToldOnlyUsefulTruth
  , RelapseGovernmentMoment.thoughtTurnedHigher
  , RelapseGovernmentMoment.courageStrengthProportional
  , RelapseGovernmentMoment.causationMindSpiritualLaw
  , RelapseGovernmentMoment.witnessAgainstPleaSilenced
  , RelapseGovernmentMoment.sicknessDreamAwakening
  , RelapseGovernmentMoment.diseaseMadeUnrealToPatient
  , RelapseGovernmentMoment.mindControlExplainedWhenBearable
  , RelapseGovernmentMoment.materialPleasurePainBeliefDestroyed
  , RelapseGovernmentMoment.honestPleaHeals
  , RelapseGovernmentMoment.sicknessNoMoreRealThanSin
  , RelapseGovernmentMoment.truthfulArgumentsConferHarmony
  , RelapseGovernmentMoment.moralityIncludedInTreatment
  , RelapseGovernmentMoment.diseaseFormsWakingDreams
  , RelapseGovernmentMoment.lurkingErrorPerpetuatesDisease
  , RelapseGovernmentMoment.relapseCauseMetMentally
  , RelapseGovernmentMoment.diseaseNoIntelligenceToMove
  , RelapseGovernmentMoment.observeMindNotBody
  , RelapseGovernmentMoment.conquerOwnFearAndPatientFear
  , RelapseGovernmentMoment.truthPreventsMetastasis
  , RelapseGovernmentMoment.spiritGovernsMan
  , RelapseGovernmentMoment.errorCannotProduceReluctance
  ]

structure PracticeRelapseGovernment where
  inflammationFearBelief : Bool
  sedativeDoesNotRemoveCause : Bool
  patientThoughtTurnedHigher : Bool
  diseaseMustBeMadeUnreal : Bool
  moralBeliefIncluded : Bool
  relapseHasNoTruthPower : Bool
  diseaseCannotMoveItself : Bool
  spiritGovernsMan : Bool
deriving DecidableEq, Repr

def practiceRelapseGovernment : PracticeRelapseGovernment where
  inflammationFearBelief := true
  sedativeDoesNotRemoveCause := true
  patientThoughtTurnedHigher := true
  diseaseMustBeMadeUnreal := true
  moralBeliefIncluded := true
  relapseHasNoTruthPower := true
  diseaseCannotMoveItself := true
  spiritGovernsMan := true

theorem eddy_practice_relapse_government_witness :
    relapseGovernmentTrace.length = 30
    ∧ relapseGovernmentTrace.head? =
      some RelapseGovernmentMoment.inflammationFearState
    ∧ relapseGovernmentTrace.getLast? =
      some RelapseGovernmentMoment.errorCannotProduceReluctance
    ∧ practiceRelapseGovernment.inflammationFearBelief = true
    ∧ practiceRelapseGovernment.sedativeDoesNotRemoveCause = true
    ∧ practiceRelapseGovernment.patientThoughtTurnedHigher = true
    ∧ practiceRelapseGovernment.diseaseMustBeMadeUnreal = true
    ∧ practiceRelapseGovernment.moralBeliefIncluded = true
    ∧ practiceRelapseGovernment.relapseHasNoTruthPower = true
    ∧ practiceRelapseGovernment.diseaseCannotMoveItself = true
    ∧ practiceRelapseGovernment.spiritGovernsMan = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyPracticeRelapseGovernmentWitness
end Gnosis.Witnesses.Eddy
