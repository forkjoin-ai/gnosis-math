import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlMaidaJesusFeastClosingWitness

/-!
# Quran 5:109-120, Al-Maida -- Messengers Assembled, Jesus' Signs, the Feast, and Truthful Triumph

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:3913-3964`.

This bounded witness tracks the closing unit of Sura 5:

  * on the Day God assembles all messengers and asks what response they received, they
    defer unseen knowledge to God;
  * God reminds Jesus son of Mary of favour to him and his mother;
  * Jesus is strengthened with the holy spirit and speaks in infancy and maturity;
  * Jesus is taught Scripture, wisdom, Torah, and Gospel;
  * by God's leave Jesus forms a bird from clay, heals the blind and leper, and raises
    the dead;
  * God restrains the Children of Israel from harming Jesus despite their charge of sorcery;
  * the disciples are inspired to believe and bear witness to devotion;
  * the disciples ask for a feast from heaven so their hearts are reassured and they can
    be witnesses;
  * Jesus prays for the feast as festival, sign, and provision from the best provider;
  * God grants the feast with a warning against disbelief after it;
  * God asks whether Jesus told people to take him and his mother as gods beside God;
  * Jesus disowns saying what he had no right to say and affirms God's knowledge of the
    unseen;
  * Jesus says he commanded only worship of God, my Lord and your Lord, and that God was
    watcher after taking his soul;
  * punishment and forgiveness are left to the Almighty and Wise;
  * truthful people benefit from truthfulness, receive Gardens, and God is pleased with
    them and they with Him;
  * the sura closes with God's control of the heavens, earth, and everything in them.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive JesusFeastClosingMoment
  | messengersAssembled
  | favourToJesusMary
  | holySpiritSpeech
  | scriptureWisdomTorahGospel
  | signsByGodsLeave
  | israelRestrained
  | disciplesInspired
  | feastRequested
  | feastPrayer
  | feastWarning
  | divinityQuestion
  | jesusDisownsExcess
  | worshipMyLordYourLord
  | watcherAfterSoulTaken
  | truthfulTriumph
  | finalControl
deriving DecidableEq, Repr

def jesusFeastClosingMoments : List JesusFeastClosingMoment :=
  [ JesusFeastClosingMoment.messengersAssembled
  , JesusFeastClosingMoment.favourToJesusMary
  , JesusFeastClosingMoment.holySpiritSpeech
  , JesusFeastClosingMoment.scriptureWisdomTorahGospel
  , JesusFeastClosingMoment.signsByGodsLeave
  , JesusFeastClosingMoment.israelRestrained
  , JesusFeastClosingMoment.disciplesInspired
  , JesusFeastClosingMoment.feastRequested
  , JesusFeastClosingMoment.feastPrayer
  , JesusFeastClosingMoment.feastWarning
  , JesusFeastClosingMoment.divinityQuestion
  , JesusFeastClosingMoment.jesusDisownsExcess
  , JesusFeastClosingMoment.worshipMyLordYourLord
  , JesusFeastClosingMoment.watcherAfterSoulTaken
  , JesusFeastClosingMoment.truthfulTriumph
  , JesusFeastClosingMoment.finalControl
  ]

structure JesusFeastClosingPattern where
  messengersDeferUnseenKnowledge : Bool
  favourToJesusAndMary : Bool
  holySpiritInfancyMaturity : Bool
  scriptureWisdomTorahGospelTaught : Bool
  birdHealingLifeSigns : Bool
  signsByGodsLeave : Bool
  disciplesBelieveAndWitness : Bool
  feastHeartsReassured : Bool
  feastFestivalSignProvision : Bool
  disbeliefAfterFeastWarned : Bool
  twoGodsQuestionNamed : Bool
  jesusClaimsNoUnauthorizedSpeech : Bool
  unseenKnowledgeBelongsToGod : Bool
  worshipGodMyLordYourLord : Bool
  godWatcherWitnessAllThings : Bool
  truthfulBenefitGardens : Bool
  godPleasedSupremeTriumph : Bool
  finalControlAllThings : Bool
deriving DecidableEq, Repr

def jesusFeastClosingPattern : JesusFeastClosingPattern where
  messengersDeferUnseenKnowledge := true
  favourToJesusAndMary := true
  holySpiritInfancyMaturity := true
  scriptureWisdomTorahGospelTaught := true
  birdHealingLifeSigns := true
  signsByGodsLeave := true
  disciplesBelieveAndWitness := true
  feastHeartsReassured := true
  feastFestivalSignProvision := true
  disbeliefAfterFeastWarned := true
  twoGodsQuestionNamed := true
  jesusClaimsNoUnauthorizedSpeech := true
  unseenKnowledgeBelongsToGod := true
  worshipGodMyLordYourLord := true
  godWatcherWitnessAllThings := true
  truthfulBenefitGardens := true
  godPleasedSupremeTriumph := true
  finalControlAllThings := true

theorem quran_al_maida_jesus_feast_closing_witness :
    jesusFeastClosingMoments.length = 16
    ∧ jesusFeastClosingMoments.head? = some JesusFeastClosingMoment.messengersAssembled
    ∧ jesusFeastClosingMoments.getLast? = some JesusFeastClosingMoment.finalControl
    ∧ jesusFeastClosingPattern.messengersDeferUnseenKnowledge = true
    ∧ jesusFeastClosingPattern.favourToJesusAndMary = true
    ∧ jesusFeastClosingPattern.holySpiritInfancyMaturity = true
    ∧ jesusFeastClosingPattern.scriptureWisdomTorahGospelTaught = true
    ∧ jesusFeastClosingPattern.birdHealingLifeSigns = true
    ∧ jesusFeastClosingPattern.signsByGodsLeave = true
    ∧ jesusFeastClosingPattern.disciplesBelieveAndWitness = true
    ∧ jesusFeastClosingPattern.feastHeartsReassured = true
    ∧ jesusFeastClosingPattern.feastFestivalSignProvision = true
    ∧ jesusFeastClosingPattern.disbeliefAfterFeastWarned = true
    ∧ jesusFeastClosingPattern.twoGodsQuestionNamed = true
    ∧ jesusFeastClosingPattern.jesusClaimsNoUnauthorizedSpeech = true
    ∧ jesusFeastClosingPattern.unseenKnowledgeBelongsToGod = true
    ∧ jesusFeastClosingPattern.worshipGodMyLordYourLord = true
    ∧ jesusFeastClosingPattern.godWatcherWitnessAllThings = true
    ∧ jesusFeastClosingPattern.truthfulBenefitGardens = true
    ∧ jesusFeastClosingPattern.godPleasedSupremeTriumph = true
    ∧ jesusFeastClosingPattern.finalControlAllThings = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end QuranAlMaidaJesusFeastClosingWitness
end Gnosis.Witnesses.Islam
