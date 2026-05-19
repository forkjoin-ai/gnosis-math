import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyRecapAllMindTenetsWitness

/-!
# Science and Health, Chapter XIV -- All-Mind Ultimatum and Tenets

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:20140-20470`.

Bounded section: 490:27-497:27. This recapitulation unit closes the Q&A chapter
by using sleep and mesmerism to expose material sense, stating the all-Mind
ultimatum, applying Mind-healing to sickness, grounding progress in obedience
and spiritual fruits, and ending with the six religious tenets.
-/

inductive RecapAllMindTenetsMoment where
  | sleepMaterialSenseIllusion
  | animalMagnetismUncoversBelief
  | sensationChangesWithBelief
  | spiritualIndividualityNeverWrong
  | spiritLinkEstablishesMan
  | materialManDream
  | personalityNotIndividuality
  | spiritualExistenceOnlyFact
  | beingHolinessHarmonyImmortality
  | matterVersusAllMindContest
  | allMindUltimatum
  | truthTriumphantOverSenseEvidence
  | healingQuestionRequiresTeaching
  | mindSuperiorToSenses
  | sicknessFearManifest
  | lazarusAwakeningTest
  | loveMeetsEveryNeed
  | graceNoMiracleToLove
  | reasonCorrectsCorporealSense
  | twoTheoriesOfMan
  | followersCastOutFear
  | sicknessClassedWithError
  | steadfastTrustSupportsBeing
  | studyLetterImbibeSpirit
  | noTransferFromMortalToMortal
  | firstDutyOneMindLoveNeighbor
  | lifeIsGodQuestion
  | fruitsProveUnderstanding
  | holyGhostChristEnableDemonstration
  | deathSwallowedInVictory
  | noDoctrinalCreed
  | bibleSufficientGuide
  | oneGodChristComforterMan
  | forgivenessAsSinDestruction
  | atonementUnfoldsUnity
  | resurrectionUpliftsFaith
  | watchPrayDoMercyJusticePurity
deriving DecidableEq, Repr

def recapAllMindTenetsTrace : List RecapAllMindTenetsMoment :=
  [ RecapAllMindTenetsMoment.sleepMaterialSenseIllusion
  , RecapAllMindTenetsMoment.animalMagnetismUncoversBelief
  , RecapAllMindTenetsMoment.sensationChangesWithBelief
  , RecapAllMindTenetsMoment.spiritualIndividualityNeverWrong
  , RecapAllMindTenetsMoment.spiritLinkEstablishesMan
  , RecapAllMindTenetsMoment.materialManDream
  , RecapAllMindTenetsMoment.personalityNotIndividuality
  , RecapAllMindTenetsMoment.spiritualExistenceOnlyFact
  , RecapAllMindTenetsMoment.beingHolinessHarmonyImmortality
  , RecapAllMindTenetsMoment.matterVersusAllMindContest
  , RecapAllMindTenetsMoment.allMindUltimatum
  , RecapAllMindTenetsMoment.truthTriumphantOverSenseEvidence
  , RecapAllMindTenetsMoment.healingQuestionRequiresTeaching
  , RecapAllMindTenetsMoment.mindSuperiorToSenses
  , RecapAllMindTenetsMoment.sicknessFearManifest
  , RecapAllMindTenetsMoment.lazarusAwakeningTest
  , RecapAllMindTenetsMoment.loveMeetsEveryNeed
  , RecapAllMindTenetsMoment.graceNoMiracleToLove
  , RecapAllMindTenetsMoment.reasonCorrectsCorporealSense
  , RecapAllMindTenetsMoment.twoTheoriesOfMan
  , RecapAllMindTenetsMoment.followersCastOutFear
  , RecapAllMindTenetsMoment.sicknessClassedWithError
  , RecapAllMindTenetsMoment.steadfastTrustSupportsBeing
  , RecapAllMindTenetsMoment.studyLetterImbibeSpirit
  , RecapAllMindTenetsMoment.noTransferFromMortalToMortal
  , RecapAllMindTenetsMoment.firstDutyOneMindLoveNeighbor
  , RecapAllMindTenetsMoment.lifeIsGodQuestion
  , RecapAllMindTenetsMoment.fruitsProveUnderstanding
  , RecapAllMindTenetsMoment.holyGhostChristEnableDemonstration
  , RecapAllMindTenetsMoment.deathSwallowedInVictory
  , RecapAllMindTenetsMoment.noDoctrinalCreed
  , RecapAllMindTenetsMoment.bibleSufficientGuide
  , RecapAllMindTenetsMoment.oneGodChristComforterMan
  , RecapAllMindTenetsMoment.forgivenessAsSinDestruction
  , RecapAllMindTenetsMoment.atonementUnfoldsUnity
  , RecapAllMindTenetsMoment.resurrectionUpliftsFaith
  , RecapAllMindTenetsMoment.watchPrayDoMercyJusticePurity
  ]

structure RecapAllMindTenets where
  materialSenseDream : Bool
  spiritualExistenceOnly : Bool
  allMindUltimatum : Bool
  sicknessFearManifest : Bool
  loveMeetsNeed : Bool
  progressRequiresObedience : Bool
  tenetsCloseChapter : Bool
deriving DecidableEq, Repr

def recapAllMindTenets : RecapAllMindTenets where
  materialSenseDream := true
  spiritualExistenceOnly := true
  allMindUltimatum := true
  sicknessFearManifest := true
  loveMeetsNeed := true
  progressRequiresObedience := true
  tenetsCloseChapter := true

theorem eddy_recap_all_mind_tenets_witness :
    recapAllMindTenetsTrace.length = 37
    ∧ recapAllMindTenetsTrace.head? =
      some RecapAllMindTenetsMoment.sleepMaterialSenseIllusion
    ∧ recapAllMindTenetsTrace.getLast? =
      some RecapAllMindTenetsMoment.watchPrayDoMercyJusticePurity
    ∧ recapAllMindTenets.materialSenseDream = true
    ∧ recapAllMindTenets.spiritualExistenceOnly = true
    ∧ recapAllMindTenets.allMindUltimatum = true
    ∧ recapAllMindTenets.sicknessFearManifest = true
    ∧ recapAllMindTenets.loveMeetsNeed = true
    ∧ recapAllMindTenets.progressRequiresObedience = true
    ∧ recapAllMindTenets.tenetsCloseChapter = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyRecapAllMindTenetsWitness
end Gnosis.Witnesses.Eddy
