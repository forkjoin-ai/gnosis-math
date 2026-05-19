import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyPracticeMentalCourtWitness

/-!
# Science and Health, Chapter XII -- The Mental Court Case

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:17780-18280`.

Bounded section: 430:15-442:30. This court allegory stages Personal Sense,
False Belief, Health-laws, Nerve, Mortality, Death, Judge Medicine, and Mortal
Minds as the prosecution's machinery, then reverses the verdict in the Court of
Spirit through Christian Science, Scripture, divine Justice, Spiritual Senses,
and Christ as the practical physician.
-/

inductive MentalCourtMoment where
  | allegoryLawMindVersusHygiene
  | personalSensePlaintiff
  | mortalManDefendant
  | falseBeliefAttorney
  | mortalMindsJury
  | judgeMedicineBench
  | healthLawsCriminalizesCare
  | coatedTongueFurWitness
  | sallowSkinSymptomWitness
  | nerveClaimsMatterMessages
  | mortalityStatuteDeathPenalty
  | deathConfirmsHealthLaw
  | medicineChargesPersonalSenseEvidence
  | guiltyOfLiverComplaint
  | benevolenceTreatedAsCrime
  | theologyPreparesSenseForDeath
  | christTruthDelaysExecution
  | courtOfSpiritGranted
  | christianScienceTenderCounsel
  | testimonyOneSidedConspiracy
  | manAmenableToSpiritOnly
  | bodyCommittedNoOffense
  | goodDeedsImmortal
  | healthLawsOutlawed
  | justiceCannotPunishRightAction
  | truthLifeLoveJurisdiction
  | divineLawProtectsService
  | fearSheriffPrecipitatesPenalty
  | errorCourtCondemnsDoingRight
  | nerveFalseWitnessExposed
  | truthRanksAboveErrorCourt
  | bibleStatuteRightsOfMan
  | personalSenseArrested
  | morbidSecretionFurFraud
  | deathMessageFromFalseBelief
  | witnessesJurorsJudgesOffenders
  | diseaseNeverFoundByDetectives
  | goodDeedsWarpedIntoCrimes
  | spiritAppealSentencesOnlySin
  | personalSenseTestimonyRepudiated
  | chiefJusticeNullifiesNonSinPunishment
  | materialLawCannotWitness
  | fearCannotArrest
  | diseaseCannotImprison
  | spiritDecidesForMan
  | noPhysicalLawTransgressed
  | spiritualSensesNotGuilty
  | divineLoveCastsOutFear
  | christChangesBeliefToUnderstanding
  | malpracticeCannotHarm
deriving DecidableEq, Repr

def mentalCourtTrace : List MentalCourtMoment :=
  [ MentalCourtMoment.allegoryLawMindVersusHygiene
  , MentalCourtMoment.personalSensePlaintiff
  , MentalCourtMoment.mortalManDefendant
  , MentalCourtMoment.falseBeliefAttorney
  , MentalCourtMoment.mortalMindsJury
  , MentalCourtMoment.judgeMedicineBench
  , MentalCourtMoment.healthLawsCriminalizesCare
  , MentalCourtMoment.coatedTongueFurWitness
  , MentalCourtMoment.sallowSkinSymptomWitness
  , MentalCourtMoment.nerveClaimsMatterMessages
  , MentalCourtMoment.mortalityStatuteDeathPenalty
  , MentalCourtMoment.deathConfirmsHealthLaw
  , MentalCourtMoment.medicineChargesPersonalSenseEvidence
  , MentalCourtMoment.guiltyOfLiverComplaint
  , MentalCourtMoment.benevolenceTreatedAsCrime
  , MentalCourtMoment.theologyPreparesSenseForDeath
  , MentalCourtMoment.christTruthDelaysExecution
  , MentalCourtMoment.courtOfSpiritGranted
  , MentalCourtMoment.christianScienceTenderCounsel
  , MentalCourtMoment.testimonyOneSidedConspiracy
  , MentalCourtMoment.manAmenableToSpiritOnly
  , MentalCourtMoment.bodyCommittedNoOffense
  , MentalCourtMoment.goodDeedsImmortal
  , MentalCourtMoment.healthLawsOutlawed
  , MentalCourtMoment.justiceCannotPunishRightAction
  , MentalCourtMoment.truthLifeLoveJurisdiction
  , MentalCourtMoment.divineLawProtectsService
  , MentalCourtMoment.fearSheriffPrecipitatesPenalty
  , MentalCourtMoment.errorCourtCondemnsDoingRight
  , MentalCourtMoment.nerveFalseWitnessExposed
  , MentalCourtMoment.truthRanksAboveErrorCourt
  , MentalCourtMoment.bibleStatuteRightsOfMan
  , MentalCourtMoment.personalSenseArrested
  , MentalCourtMoment.morbidSecretionFurFraud
  , MentalCourtMoment.deathMessageFromFalseBelief
  , MentalCourtMoment.witnessesJurorsJudgesOffenders
  , MentalCourtMoment.diseaseNeverFoundByDetectives
  , MentalCourtMoment.goodDeedsWarpedIntoCrimes
  , MentalCourtMoment.spiritAppealSentencesOnlySin
  , MentalCourtMoment.personalSenseTestimonyRepudiated
  , MentalCourtMoment.chiefJusticeNullifiesNonSinPunishment
  , MentalCourtMoment.materialLawCannotWitness
  , MentalCourtMoment.fearCannotArrest
  , MentalCourtMoment.diseaseCannotImprison
  , MentalCourtMoment.spiritDecidesForMan
  , MentalCourtMoment.noPhysicalLawTransgressed
  , MentalCourtMoment.spiritualSensesNotGuilty
  , MentalCourtMoment.divineLoveCastsOutFear
  , MentalCourtMoment.christChangesBeliefToUnderstanding
  , MentalCourtMoment.malpracticeCannotHarm
  ]

structure PracticeMentalCourt where
  prosecutionIsPersonalSense : Bool
  healthLawCriminalizesGood : Bool
  fearPrecipitatesPenalty : Bool
  spiritCourtReversesErrorCourt : Bool
  bibleStatuteOverridesMaterialLaw : Bool
  materialLawCannotWitness : Bool
  diseaseCannotImprison : Bool
  verdictNotGuilty : Bool
  christChangesBeliefToUnderstanding : Bool
deriving DecidableEq, Repr

def practiceMentalCourt : PracticeMentalCourt where
  prosecutionIsPersonalSense := true
  healthLawCriminalizesGood := true
  fearPrecipitatesPenalty := true
  spiritCourtReversesErrorCourt := true
  bibleStatuteOverridesMaterialLaw := true
  materialLawCannotWitness := true
  diseaseCannotImprison := true
  verdictNotGuilty := true
  christChangesBeliefToUnderstanding := true

theorem eddy_practice_mental_court_witness :
    mentalCourtTrace.length = 50
    ∧ mentalCourtTrace.head? =
      some MentalCourtMoment.allegoryLawMindVersusHygiene
    ∧ mentalCourtTrace.getLast? =
      some MentalCourtMoment.malpracticeCannotHarm
    ∧ practiceMentalCourt.prosecutionIsPersonalSense = true
    ∧ practiceMentalCourt.healthLawCriminalizesGood = true
    ∧ practiceMentalCourt.fearPrecipitatesPenalty = true
    ∧ practiceMentalCourt.spiritCourtReversesErrorCourt = true
    ∧ practiceMentalCourt.bibleStatuteOverridesMaterialLaw = true
    ∧ practiceMentalCourt.materialLawCannotWitness = true
    ∧ practiceMentalCourt.diseaseCannotImprison = true
    ∧ practiceMentalCourt.verdictNotGuilty = true
    ∧ practiceMentalCourt.christChangesBeliefToUnderstanding = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyPracticeMentalCourtWitness
end Gnosis.Witnesses.Eddy
