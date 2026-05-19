import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyRecapGodErrorChristWitness

/-!
# Science and Health, Chapter XIV -- God, Error, and Christ

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:19145-19680`.

Bounded section: 465:1-475:3. This recapitulation unit gathers the opening Q&A
definitions: God as Mind, Spirit, Soul, Principle, Life, Truth, Love; one Mind
as the demand of Soul; the scientific statement of being; substance, Life, and
intelligence; error and sin as unrealities; and Christ as ideal Truth destroying
the works of error.
-/

inductive RecapGodErrorChristMoment where
  | chapterFromClassBook
  | godSevenSynonyms
  | synonymsOneAbsoluteGod
  | onePrincipleOmni
  | spiritsSoulsImproperPlural
  | christianityDemonstratesScience
  | noOtherIntelligenceLifeSubstance
  | neighborLoveFromOneMind
  | soulNotInBody
  | principleNotInIdea
  | mindKnownByItsIdea
  | soulCannotSin
  | scientificStatementBeing
  | substanceEternalNotDiscordant
  | lifeWithoutBeginningEnd
  | intelligenceOmniQuality
  | oneMindExterminatesError
  | evilNoPlaceInInfinity
  | oneFatherBrotherhood
  | evilUnrealIfGoodReal
  | standardGodAndMan
  | relationIndestructible
  | materialSenseNoFactEvidence
  | spiritualSenseSustainsCoexistence
  | creedReducedToScience
  | godLawDestroysInharmony
  | errorSuppositionMatter
  | erroneousTruthAbsurd
  | sinSeemsRealUntilStripped
  | christIdealTruth
  | jesusPresentsChrist
  | principleNotPersonalityNeeded
  | demonstrationAboveWords
  | miraclesAsMarvelsMisread
  | evilsNotDivineOffspring
  | truthDestroysFalsity
  | noMatterToInfiniteSpirit
deriving DecidableEq, Repr

def recapGodErrorChristTrace : List RecapGodErrorChristMoment :=
  [ RecapGodErrorChristMoment.chapterFromClassBook
  , RecapGodErrorChristMoment.godSevenSynonyms
  , RecapGodErrorChristMoment.synonymsOneAbsoluteGod
  , RecapGodErrorChristMoment.onePrincipleOmni
  , RecapGodErrorChristMoment.spiritsSoulsImproperPlural
  , RecapGodErrorChristMoment.christianityDemonstratesScience
  , RecapGodErrorChristMoment.noOtherIntelligenceLifeSubstance
  , RecapGodErrorChristMoment.neighborLoveFromOneMind
  , RecapGodErrorChristMoment.soulNotInBody
  , RecapGodErrorChristMoment.principleNotInIdea
  , RecapGodErrorChristMoment.mindKnownByItsIdea
  , RecapGodErrorChristMoment.soulCannotSin
  , RecapGodErrorChristMoment.scientificStatementBeing
  , RecapGodErrorChristMoment.substanceEternalNotDiscordant
  , RecapGodErrorChristMoment.lifeWithoutBeginningEnd
  , RecapGodErrorChristMoment.intelligenceOmniQuality
  , RecapGodErrorChristMoment.oneMindExterminatesError
  , RecapGodErrorChristMoment.evilNoPlaceInInfinity
  , RecapGodErrorChristMoment.oneFatherBrotherhood
  , RecapGodErrorChristMoment.evilUnrealIfGoodReal
  , RecapGodErrorChristMoment.standardGodAndMan
  , RecapGodErrorChristMoment.relationIndestructible
  , RecapGodErrorChristMoment.materialSenseNoFactEvidence
  , RecapGodErrorChristMoment.spiritualSenseSustainsCoexistence
  , RecapGodErrorChristMoment.creedReducedToScience
  , RecapGodErrorChristMoment.godLawDestroysInharmony
  , RecapGodErrorChristMoment.errorSuppositionMatter
  , RecapGodErrorChristMoment.erroneousTruthAbsurd
  , RecapGodErrorChristMoment.sinSeemsRealUntilStripped
  , RecapGodErrorChristMoment.christIdealTruth
  , RecapGodErrorChristMoment.jesusPresentsChrist
  , RecapGodErrorChristMoment.principleNotPersonalityNeeded
  , RecapGodErrorChristMoment.demonstrationAboveWords
  , RecapGodErrorChristMoment.miraclesAsMarvelsMisread
  , RecapGodErrorChristMoment.evilsNotDivineOffspring
  , RecapGodErrorChristMoment.truthDestroysFalsity
  , RecapGodErrorChristMoment.noMatterToInfiniteSpirit
  ]

structure RecapGodErrorChrist where
  godSevenSynonyms : Bool
  oneMindDemand : Bool
  scientificStatementCentral : Bool
  errorUnreal : Bool
  christIdealTruth : Bool
  jesusDemonstratesPrinciple : Bool
  truthDestroysFalsity : Bool
deriving DecidableEq, Repr

def recapGodErrorChrist : RecapGodErrorChrist where
  godSevenSynonyms := true
  oneMindDemand := true
  scientificStatementCentral := true
  errorUnreal := true
  christIdealTruth := true
  jesusDemonstratesPrinciple := true
  truthDestroysFalsity := true

theorem eddy_recap_god_error_christ_witness :
    recapGodErrorChristTrace.length = 37
    ∧ recapGodErrorChristTrace.head? =
      some RecapGodErrorChristMoment.chapterFromClassBook
    ∧ recapGodErrorChristTrace.getLast? =
      some RecapGodErrorChristMoment.noMatterToInfiniteSpirit
    ∧ recapGodErrorChrist.godSevenSynonyms = true
    ∧ recapGodErrorChrist.oneMindDemand = true
    ∧ recapGodErrorChrist.scientificStatementCentral = true
    ∧ recapGodErrorChrist.errorUnreal = true
    ∧ recapGodErrorChrist.christIdealTruth = true
    ∧ recapGodErrorChrist.jesusDemonstratesPrinciple = true
    ∧ recapGodErrorChrist.truthDestroysFalsity = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyRecapGodErrorChristWitness
end Gnosis.Witnesses.Eddy
