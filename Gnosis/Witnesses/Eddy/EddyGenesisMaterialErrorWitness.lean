import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyGenesisMaterialErrorWitness

/-!
# Science and Health, Chapter XV -- Material Error Record

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:21620-22220`.

Bounded section: 521:18-531:12. This Genesis unit contrasts the completed
spiritual record with the second, material account: mist, Jehovah, dust-man,
Eden as body, forbidden knowledge, Adam's naming, hypnotic surgery, serpent,
and the dream-narrative that matter precedes Mind.
-/

inductive GenesisMaterialErrorMoment where
  | readerAsksMoreCreation
  | secondAccountMortalMaterial
  | mistIntroducesErrorStory
  | secondRecordOpposesFirst
  | firstRecordProvesSecondFalse
  | separateExistenceImpossible
  | pantheismExternalizedMatter
  | matterTakesSpiritPlace
  | spiritMatterCooperationHypothesis
  | falseClaimDeepensMist
  | errorComesFromBeneath
  | twoDocumentsDistinguished
  | elohimVersusJehovah
  | heathenGodsIdolatry
  | jehovahTribalDeity
  | dustManCreationReversed
  | matterNotSpiritReflection
  | dustNarrativeLie
  | mankindAdamicHumanCreation
  | manLanguageImageMind
  | wordMakesOnlyGood
  | corporealSensesContradictGood
  | treeContradictsFirstCreation
  | beliefLessThanUnderstanding
  | firstMentionEvilLegendary
  | treeLifeTruthIdea
  | treeKnowledgeErrorDoctrine
  | edenAsMortalBody
  | mindNotPutIntoMatter
  | godDoesNotTempt
  | materialPerceptionEvilKnowledge
  | adamNamingCounterfeit
  | dustSentienceDream
  | hypnoticSurgeryWoman
  | errorSimulatesTruth
  | mentalMidwiferyHint
  | dreamOfExistenceDestroyed
  | serpentOnlyAsEvil
  | evilContradictsItself
  | adamSynonymError
  | divineProvidenceFeedsMan
  | serpentPromisesOtherGod
  | spiritAndFleshWar
  | dreamNarrativeNoReality
  | matterPrecedesMindError
  | hopeOfSpiritualPerception
deriving DecidableEq, Repr

def genesisMaterialErrorTrace : List GenesisMaterialErrorMoment :=
  [ GenesisMaterialErrorMoment.readerAsksMoreCreation
  , GenesisMaterialErrorMoment.secondAccountMortalMaterial
  , GenesisMaterialErrorMoment.mistIntroducesErrorStory
  , GenesisMaterialErrorMoment.secondRecordOpposesFirst
  , GenesisMaterialErrorMoment.firstRecordProvesSecondFalse
  , GenesisMaterialErrorMoment.separateExistenceImpossible
  , GenesisMaterialErrorMoment.pantheismExternalizedMatter
  , GenesisMaterialErrorMoment.matterTakesSpiritPlace
  , GenesisMaterialErrorMoment.spiritMatterCooperationHypothesis
  , GenesisMaterialErrorMoment.falseClaimDeepensMist
  , GenesisMaterialErrorMoment.errorComesFromBeneath
  , GenesisMaterialErrorMoment.twoDocumentsDistinguished
  , GenesisMaterialErrorMoment.elohimVersusJehovah
  , GenesisMaterialErrorMoment.heathenGodsIdolatry
  , GenesisMaterialErrorMoment.jehovahTribalDeity
  , GenesisMaterialErrorMoment.dustManCreationReversed
  , GenesisMaterialErrorMoment.matterNotSpiritReflection
  , GenesisMaterialErrorMoment.dustNarrativeLie
  , GenesisMaterialErrorMoment.mankindAdamicHumanCreation
  , GenesisMaterialErrorMoment.manLanguageImageMind
  , GenesisMaterialErrorMoment.wordMakesOnlyGood
  , GenesisMaterialErrorMoment.corporealSensesContradictGood
  , GenesisMaterialErrorMoment.treeContradictsFirstCreation
  , GenesisMaterialErrorMoment.beliefLessThanUnderstanding
  , GenesisMaterialErrorMoment.firstMentionEvilLegendary
  , GenesisMaterialErrorMoment.treeLifeTruthIdea
  , GenesisMaterialErrorMoment.treeKnowledgeErrorDoctrine
  , GenesisMaterialErrorMoment.edenAsMortalBody
  , GenesisMaterialErrorMoment.mindNotPutIntoMatter
  , GenesisMaterialErrorMoment.godDoesNotTempt
  , GenesisMaterialErrorMoment.materialPerceptionEvilKnowledge
  , GenesisMaterialErrorMoment.adamNamingCounterfeit
  , GenesisMaterialErrorMoment.dustSentienceDream
  , GenesisMaterialErrorMoment.hypnoticSurgeryWoman
  , GenesisMaterialErrorMoment.errorSimulatesTruth
  , GenesisMaterialErrorMoment.mentalMidwiferyHint
  , GenesisMaterialErrorMoment.dreamOfExistenceDestroyed
  , GenesisMaterialErrorMoment.serpentOnlyAsEvil
  , GenesisMaterialErrorMoment.evilContradictsItself
  , GenesisMaterialErrorMoment.adamSynonymError
  , GenesisMaterialErrorMoment.divineProvidenceFeedsMan
  , GenesisMaterialErrorMoment.serpentPromisesOtherGod
  , GenesisMaterialErrorMoment.spiritAndFleshWar
  , GenesisMaterialErrorMoment.dreamNarrativeNoReality
  , GenesisMaterialErrorMoment.matterPrecedesMindError
  , GenesisMaterialErrorMoment.hopeOfSpiritualPerception
  ]

structure GenesisMaterialError where
  twoRecordsOpposed : Bool
  mistFalseClaim : Bool
  dustManLie : Bool
  edenMortalBody : Bool
  serpentErrorOnly : Bool
  adamErrorSynonym : Bool
  dreamNarrativeUnreal : Bool
deriving DecidableEq, Repr

def genesisMaterialError : GenesisMaterialError where
  twoRecordsOpposed := true
  mistFalseClaim := true
  dustManLie := true
  edenMortalBody := true
  serpentErrorOnly := true
  adamErrorSynonym := true
  dreamNarrativeUnreal := true

theorem eddy_genesis_material_error_witness :
    genesisMaterialErrorTrace.length = 46
    ∧ genesisMaterialErrorTrace.head? =
      some GenesisMaterialErrorMoment.readerAsksMoreCreation
    ∧ genesisMaterialErrorTrace.getLast? =
      some GenesisMaterialErrorMoment.hopeOfSpiritualPerception
    ∧ genesisMaterialError.twoRecordsOpposed = true
    ∧ genesisMaterialError.mistFalseClaim = true
    ∧ genesisMaterialError.dustManLie = true
    ∧ genesisMaterialError.edenMortalBody = true
    ∧ genesisMaterialError.serpentErrorOnly = true
    ∧ genesisMaterialError.adamErrorSynonym = true
    ∧ genesisMaterialError.dreamNarrativeUnreal = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyGenesisMaterialErrorWitness
end Gnosis.Witnesses.Eddy
