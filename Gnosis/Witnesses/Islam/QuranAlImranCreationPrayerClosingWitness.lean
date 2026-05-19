import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlImranCreationPrayerClosingWitness

/-!
# Quran 3:189-200, Al Imran -- Creation Signs, Answered Prayer, and Closing Steadfastness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:2713-2750`.

This bounded witness tracks Quran 3:189-200, the close of Sura 3:

  * control of the heavens and earth belongs to God;
  * signs are found in creation and the alternation of night and day;
  * people of understanding remember God standing, sitting, and lying down;
  * reflection on creation yields prayer that it was not created without purpose;
  * the prayer asks protection from Fire, forgiveness, wiping away bad deeds, joining
    the righteous, receiving promised messengers, and avoiding humiliation on the Day;
  * the Lord answers that no worker's deed is lost, male or female;
  * emigrating, being driven out, suffering harm, fighting, and being killed are answered
    by erased bad deeds and Gardens;
  * believers are not to be deceived by disbelievers' movement through the land;
  * mindful people receive Gardens and hospitality from God;
  * some People of the Book humbly believe in God and revelation without selling signs;
  * the sura closes by commanding steadfastness, greater steadfastness, readiness,
    and mindfulness so believers may prosper.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive CreationPrayerClosingMoment
  | heavensEarthControl
  | creationNightDaySigns
  | remembrancePostures
  | purposefulCreationPrayer
  | fireForgivenessPrayer
  | promiseAndNoHumiliation
  | noDeedLost
  | migrationHarmReward
  | disbelieverTradeWarning
  | mindfulHospitality
  | humblePeopleBook
  | closingSteadfastness
deriving DecidableEq, Repr

def creationPrayerClosingMoments : List CreationPrayerClosingMoment :=
  [ CreationPrayerClosingMoment.heavensEarthControl
  , CreationPrayerClosingMoment.creationNightDaySigns
  , CreationPrayerClosingMoment.remembrancePostures
  , CreationPrayerClosingMoment.purposefulCreationPrayer
  , CreationPrayerClosingMoment.fireForgivenessPrayer
  , CreationPrayerClosingMoment.promiseAndNoHumiliation
  , CreationPrayerClosingMoment.noDeedLost
  , CreationPrayerClosingMoment.migrationHarmReward
  , CreationPrayerClosingMoment.disbelieverTradeWarning
  , CreationPrayerClosingMoment.mindfulHospitality
  , CreationPrayerClosingMoment.humblePeopleBook
  , CreationPrayerClosingMoment.closingSteadfastness
  ]

structure CreationPrayerClosingPattern where
  heavensEarthControl : Bool
  creationSignsNamed : Bool
  nightDayAlternationNamed : Bool
  remembranceStandingSittingLying : Bool
  notCreatedPurposeless : Bool
  fireProtectionPrayer : Bool
  promisedMessengersNamed : Bool
  noDeedLostMaleFemale : Bool
  migrationHarmFightingNamed : Bool
  badDeedsWipedGardensGiven : Bool
  disbelieverTradeBrief : Bool
  humblePeopleBookBelieve : Bool
  revelationNotSold : Bool
  steadfastReadyMindfulClose : Bool
deriving DecidableEq, Repr

def creationPrayerClosingPattern : CreationPrayerClosingPattern where
  heavensEarthControl := true
  creationSignsNamed := true
  nightDayAlternationNamed := true
  remembranceStandingSittingLying := true
  notCreatedPurposeless := true
  fireProtectionPrayer := true
  promisedMessengersNamed := true
  noDeedLostMaleFemale := true
  migrationHarmFightingNamed := true
  badDeedsWipedGardensGiven := true
  disbelieverTradeBrief := true
  humblePeopleBookBelieve := true
  revelationNotSold := true
  steadfastReadyMindfulClose := true

theorem quran_al_imran_creation_prayer_closing_witness :
    creationPrayerClosingMoments.length = 12
    ∧ creationPrayerClosingMoments.head? = some CreationPrayerClosingMoment.heavensEarthControl
    ∧ creationPrayerClosingMoments.getLast? = some CreationPrayerClosingMoment.closingSteadfastness
    ∧ creationPrayerClosingPattern.heavensEarthControl = true
    ∧ creationPrayerClosingPattern.creationSignsNamed = true
    ∧ creationPrayerClosingPattern.nightDayAlternationNamed = true
    ∧ creationPrayerClosingPattern.remembranceStandingSittingLying = true
    ∧ creationPrayerClosingPattern.notCreatedPurposeless = true
    ∧ creationPrayerClosingPattern.fireProtectionPrayer = true
    ∧ creationPrayerClosingPattern.promisedMessengersNamed = true
    ∧ creationPrayerClosingPattern.noDeedLostMaleFemale = true
    ∧ creationPrayerClosingPattern.migrationHarmFightingNamed = true
    ∧ creationPrayerClosingPattern.badDeedsWipedGardensGiven = true
    ∧ creationPrayerClosingPattern.disbelieverTradeBrief = true
    ∧ creationPrayerClosingPattern.humblePeopleBookBelieve = true
    ∧ creationPrayerClosingPattern.revelationNotSold = true
    ∧ creationPrayerClosingPattern.steadfastReadyMindfulClose = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end QuranAlImranCreationPrayerClosingWitness
end Gnosis.Witnesses.Islam
