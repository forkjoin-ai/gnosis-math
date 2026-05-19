import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlNisaHypocritesKillingMigrationPrayerWitness

/-!
# Quran 4:88-104, An-Nisa -- Hypocrites, Killing, Migration, and Guarded Prayer

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:3121-3208`.

This bounded witness tracks Quran 4:88-104:

  * believers are warned not to divide over hypocrites God has rejected;
  * those seeking refuge by treaty, withdrawing, not fighting, and offering peace are
    distinguished from those who neither withdraw nor restrain themselves;
  * a believer must never kill another believer except by mistake;
  * mistaken killing requires freeing a believing slave, compensation where applicable,
    treaty-recognition, charity-forgoing, or two consecutive months of fasting;
  * deliberate killing of a believer is answered by Hell, anger, rejection, and torment;
  * believers must be careful in battle and not deny the faith of one offering peace;
  * strivers with possessions and selves are ranked above those staying home, apart from
    incapacity, while all believers are promised good;
  * angels question those who wronged themselves by failing to migrate from oppression;
  * truly helpless men, women, and children are excepted;
  * migration for God finds refuge and plenty, and death on the road leaves reward sure;
  * travel permits shortened prayer under fear;
  * guarded prayer divides armed groups under the Prophet's leadership;
  * remembrance continues after prayer in all postures, and regular prayer is prescribed;
  * believers must not be faint-hearted in pursuit, because their hope from God differs.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive HypocritesKillingMigrationPrayerMoment
  | hypocriteDivision
  | peaceAndTreatyException
  | mistakenKillingRansom
  | deliberateKillingTorment
  | peaceGreetingCare
  | striversRanked
  | migrationQuestion
  | helplessException
  | migrantRewardSure
  | shortenedTravelPrayer
  | guardedPrayer
  | remembranceAfterPrayer
  | prescribedPrayerTimes
  | pursuitHope
deriving DecidableEq, Repr

def hypocritesKillingMigrationPrayerMoments : List HypocritesKillingMigrationPrayerMoment :=
  [ HypocritesKillingMigrationPrayerMoment.hypocriteDivision
  , HypocritesKillingMigrationPrayerMoment.peaceAndTreatyException
  , HypocritesKillingMigrationPrayerMoment.mistakenKillingRansom
  , HypocritesKillingMigrationPrayerMoment.deliberateKillingTorment
  , HypocritesKillingMigrationPrayerMoment.peaceGreetingCare
  , HypocritesKillingMigrationPrayerMoment.striversRanked
  , HypocritesKillingMigrationPrayerMoment.migrationQuestion
  , HypocritesKillingMigrationPrayerMoment.helplessException
  , HypocritesKillingMigrationPrayerMoment.migrantRewardSure
  , HypocritesKillingMigrationPrayerMoment.shortenedTravelPrayer
  , HypocritesKillingMigrationPrayerMoment.guardedPrayer
  , HypocritesKillingMigrationPrayerMoment.remembranceAfterPrayer
  , HypocritesKillingMigrationPrayerMoment.prescribedPrayerTimes
  , HypocritesKillingMigrationPrayerMoment.pursuitHope
  ]

structure HypocritesKillingMigrationPrayerPattern where
  hypocritesRejectedForDeeds : Bool
  treatyPeaceExceptionsNamed : Bool
  mistakenKillingRemedy : Bool
  deliberateKillingHell : Bool
  peaceGreetingNotDenied : Bool
  striversRankedAbove : Bool
  ranksForgivenessMercy : Bool
  migrationQuestionNamed : Bool
  helplessExceptionNamed : Bool
  migrantRewardSure : Bool
  shortenedPrayerAllowed : Bool
  armedGuardedPrayer : Bool
  remembranceAllPostures : Bool
  prayerPrescribedTimes : Bool
  hardshipSharedHopeDistinct : Bool
deriving DecidableEq, Repr

def hypocritesKillingMigrationPrayerPattern : HypocritesKillingMigrationPrayerPattern where
  hypocritesRejectedForDeeds := true
  treatyPeaceExceptionsNamed := true
  mistakenKillingRemedy := true
  deliberateKillingHell := true
  peaceGreetingNotDenied := true
  striversRankedAbove := true
  ranksForgivenessMercy := true
  migrationQuestionNamed := true
  helplessExceptionNamed := true
  migrantRewardSure := true
  shortenedPrayerAllowed := true
  armedGuardedPrayer := true
  remembranceAllPostures := true
  prayerPrescribedTimes := true
  hardshipSharedHopeDistinct := true

theorem quran_al_nisa_hypocrites_killing_migration_prayer_witness :
    hypocritesKillingMigrationPrayerMoments.length = 14
    ∧ hypocritesKillingMigrationPrayerMoments.head? = some HypocritesKillingMigrationPrayerMoment.hypocriteDivision
    ∧ hypocritesKillingMigrationPrayerMoments.getLast? = some HypocritesKillingMigrationPrayerMoment.pursuitHope
    ∧ hypocritesKillingMigrationPrayerPattern.hypocritesRejectedForDeeds = true
    ∧ hypocritesKillingMigrationPrayerPattern.treatyPeaceExceptionsNamed = true
    ∧ hypocritesKillingMigrationPrayerPattern.mistakenKillingRemedy = true
    ∧ hypocritesKillingMigrationPrayerPattern.deliberateKillingHell = true
    ∧ hypocritesKillingMigrationPrayerPattern.peaceGreetingNotDenied = true
    ∧ hypocritesKillingMigrationPrayerPattern.striversRankedAbove = true
    ∧ hypocritesKillingMigrationPrayerPattern.ranksForgivenessMercy = true
    ∧ hypocritesKillingMigrationPrayerPattern.migrationQuestionNamed = true
    ∧ hypocritesKillingMigrationPrayerPattern.helplessExceptionNamed = true
    ∧ hypocritesKillingMigrationPrayerPattern.migrantRewardSure = true
    ∧ hypocritesKillingMigrationPrayerPattern.shortenedPrayerAllowed = true
    ∧ hypocritesKillingMigrationPrayerPattern.armedGuardedPrayer = true
    ∧ hypocritesKillingMigrationPrayerPattern.remembranceAllPostures = true
    ∧ hypocritesKillingMigrationPrayerPattern.prayerPrescribedTimes = true
    ∧ hypocritesKillingMigrationPrayerPattern.hardshipSharedHopeDistinct = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end QuranAlNisaHypocritesKillingMigrationPrayerWitness
end Gnosis.Witnesses.Islam
