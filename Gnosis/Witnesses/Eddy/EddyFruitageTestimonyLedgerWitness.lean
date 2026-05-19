import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyFruitageTestimonyLedgerWitness

/-!
# Science and Health, Chapter XVIII -- Fruitage Testimony Ledger

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:24207-26936`.

Bounded section: Chapter XVIII, "Fruitage", through end of source. This closing
chapter is a testimonial ledger: readers repeatedly report healing, reform, and
spiritual awakening through reading and studying `Science and Health`, often
after medicine, surgery, climate, or despair had failed.
-/

inductive FruitageMoment where
  | chapterIntroducesFruits
  | lettersAuthenticateHealingEfficacy
  | rheumatismHealedByReading
  | astigmatismHerniaConstipationHealed
  | lungsAndSprainedAnkleHealed
  | fibroidTumorHealedFewDays
  | insanityEpilepsyHealed
  | mentalSurgeryArmHealed
  | cataractQuicklyCured
  | heartDiseaseHealedBeforeTeacher
  | indigestionAsthmaHabitsHealed
  | cancerConsumptionChildbirthHealed
  | childRicketsAndMotherHealed
  | sciaticRheumatismHealed
  | brightDiseaseFearOfHellResolved
  | chronicBackCatarrhNeuralgiaHealed
  | neurastheniaAndDietaryBondageHealed
  | householdRemediesThrownAway
  | croupHealedByReadingAndHymn
  | deafnessCatarrhTonsilitisHealed
  | seekerFindsHealthAndPeace
  | consumptionHealedByBorrowedBook
  | profitableStudyRestoresLungs
  | infidelityAndPhysicalIllsHealed
  | diseasedEyesInstantlyHealed
  | textbookTransformsBodyByMindRenewal
  | stomachTroubleHealedByTruthSeeking
  | dyspepsiaConstipationQuicklyHealed
  | spinalSufferingInstantlyHealed
  | despairToHopeThroughLittleBook
  | exDruggistFreedByStudy
  | deafEarsAndChildDislocationHealed
  | insanitySuicideDespairOvercome
  | familyHarmonyRestoredByPerfectManView
  | liverComplaintAndSpotsHealed
  | liquorTobaccoDesireDisappeared
  | ministryStudentFindsBeingKey
  | brightDiseaseHealedByGiftBook
  | tumorAndScrofulaFearDestroyed
  | lightOutOfDarknessBibleRenewed
  | profanityTobaccoTemperHealed
  | consumptionAsthmaAndInfidelityHealed
  | finalLampPathTestimony
deriving DecidableEq, Repr

def fruitageTrace : List FruitageMoment :=
  [ FruitageMoment.chapterIntroducesFruits
  , FruitageMoment.lettersAuthenticateHealingEfficacy
  , FruitageMoment.rheumatismHealedByReading
  , FruitageMoment.astigmatismHerniaConstipationHealed
  , FruitageMoment.lungsAndSprainedAnkleHealed
  , FruitageMoment.fibroidTumorHealedFewDays
  , FruitageMoment.insanityEpilepsyHealed
  , FruitageMoment.mentalSurgeryArmHealed
  , FruitageMoment.cataractQuicklyCured
  , FruitageMoment.heartDiseaseHealedBeforeTeacher
  , FruitageMoment.indigestionAsthmaHabitsHealed
  , FruitageMoment.cancerConsumptionChildbirthHealed
  , FruitageMoment.childRicketsAndMotherHealed
  , FruitageMoment.sciaticRheumatismHealed
  , FruitageMoment.brightDiseaseFearOfHellResolved
  , FruitageMoment.chronicBackCatarrhNeuralgiaHealed
  , FruitageMoment.neurastheniaAndDietaryBondageHealed
  , FruitageMoment.householdRemediesThrownAway
  , FruitageMoment.croupHealedByReadingAndHymn
  , FruitageMoment.deafnessCatarrhTonsilitisHealed
  , FruitageMoment.seekerFindsHealthAndPeace
  , FruitageMoment.consumptionHealedByBorrowedBook
  , FruitageMoment.profitableStudyRestoresLungs
  , FruitageMoment.infidelityAndPhysicalIllsHealed
  , FruitageMoment.diseasedEyesInstantlyHealed
  , FruitageMoment.textbookTransformsBodyByMindRenewal
  , FruitageMoment.stomachTroubleHealedByTruthSeeking
  , FruitageMoment.dyspepsiaConstipationQuicklyHealed
  , FruitageMoment.spinalSufferingInstantlyHealed
  , FruitageMoment.despairToHopeThroughLittleBook
  , FruitageMoment.exDruggistFreedByStudy
  , FruitageMoment.deafEarsAndChildDislocationHealed
  , FruitageMoment.insanitySuicideDespairOvercome
  , FruitageMoment.familyHarmonyRestoredByPerfectManView
  , FruitageMoment.liverComplaintAndSpotsHealed
  , FruitageMoment.liquorTobaccoDesireDisappeared
  , FruitageMoment.ministryStudentFindsBeingKey
  , FruitageMoment.brightDiseaseHealedByGiftBook
  , FruitageMoment.tumorAndScrofulaFearDestroyed
  , FruitageMoment.lightOutOfDarknessBibleRenewed
  , FruitageMoment.profanityTobaccoTemperHealed
  , FruitageMoment.consumptionAsthmaAndInfidelityHealed
  , FruitageMoment.finalLampPathTestimony
  ]

structure FruitageTestimonyLedger where
  readingTextbookHeals : Bool
  physicalAndMoralReformTogether : Bool
  materialMeansOftenFailFirst : Bool
  fearAndDespairReverse : Bool
  bibleRenewedByScience : Bool
  bookClosesWithFruits : Bool
deriving DecidableEq, Repr

def fruitageTestimonyLedger : FruitageTestimonyLedger where
  readingTextbookHeals := true
  physicalAndMoralReformTogether := true
  materialMeansOftenFailFirst := true
  fearAndDespairReverse := true
  bibleRenewedByScience := true
  bookClosesWithFruits := true

theorem eddy_fruitage_testimony_ledger_witness :
    fruitageTrace.length = 43
    ∧ fruitageTrace.head? =
      some FruitageMoment.chapterIntroducesFruits
    ∧ fruitageTrace.getLast? =
      some FruitageMoment.finalLampPathTestimony
    ∧ fruitageTestimonyLedger.readingTextbookHeals = true
    ∧ fruitageTestimonyLedger.physicalAndMoralReformTogether = true
    ∧ fruitageTestimonyLedger.materialMeansOftenFailFirst = true
    ∧ fruitageTestimonyLedger.fearAndDespairReverse = true
    ∧ fruitageTestimonyLedger.bibleRenewedByScience = true
    ∧ fruitageTestimonyLedger.bookClosesWithFruits = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyFruitageTestimonyLedgerWitness
end Gnosis.Witnesses.Eddy
