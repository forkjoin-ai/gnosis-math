import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraCharityParablesWitness

/-!
# Quran 2:261-274, Al-Baqara -- Charity Parables and Giving Ethics

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1997-2052`.

This witness tracks multiplied spending like seven ears, no reminders or hurtful
words, kind word better than hurtful charity, rock-and-rain exposure for showy
unbelief, garden-on-hill faith affirmation, burned garden warning, giving good
not bad things, Satan's poverty threat versus God's forgiveness and abundance,
wisdom as much good, public/private charity, guidance belonging to God, charity
benefiting the soul, needy self-restraint, and reward with no fear or grief.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive CharityParablesMoment
  | sevenEarsIncrease
  | noReminderHurt
  | kindWordForgiveness
  | rockRainShowiness
  | gardenHillFaith
  | burnedGardenReflection
  | giveGoodNotBad
  | satanPovertyGodAbundance
  | wisdomMuchGood
  | publicPrivateCharity
  | guidanceGods
  | needySelfRestraint
  | nightDayPrivatePublicReward
deriving DecidableEq, Repr

def charityParablesMoments : List CharityParablesMoment :=
  [ .sevenEarsIncrease, .noReminderHurt, .kindWordForgiveness, .rockRainShowiness
  , .gardenHillFaith, .burnedGardenReflection, .giveGoodNotBad
  , .satanPovertyGodAbundance, .wisdomMuchGood, .publicPrivateCharity
  , .guidanceGods, .needySelfRestraint, .nightDayPrivatePublicReward ]

theorem quran_al_baqara_charity_parables_witness :
    charityParablesMoments.length = 13
    ∧ charityParablesMoments.head? = some .sevenEarsIncrease
    ∧ charityParablesMoments.getLast? = some .nightDayPrivatePublicReward := by
  exact ⟨rfl, rfl, rfl⟩

end QuranAlBaqaraCharityParablesWitness
end Gnosis.Witnesses.Islam
