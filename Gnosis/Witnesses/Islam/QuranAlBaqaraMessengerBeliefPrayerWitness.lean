import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraMessengerBeliefPrayerWitness

/-!
# Quran 2:285-286, Al-Baqara -- Messenger Belief and Closing Prayer

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:2104-2114`.

This closing witness tracks the Messenger and faithful believing in what is sent
down, belief in God, angels, scriptures, and messengers, no distinction among
messengers, "we hear and obey," forgiveness and return, no soul burdened beyond
capacity, gain and suffering by deeds, and the closing prayer for no task over
forgetfulness or mistakes, no prior burdens, no unbearable load, pardon,
forgiveness, mercy, protection, and help against disbelievers.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive MessengerBeliefPrayerMoment
  | messengerFaithfulBelieve
  | beliefInGodAngelsScripturesMessengers
  | noMessengerDistinction
  | hearAndObey
  | forgivenessReturn
  | noSoulOverburdened
  | gainsAndSuffersDeeds
  | forgetMistakePrayer
  | noPriorOrUnbearableBurden
  | pardonForgiveMercy
  | protectorHelp
deriving DecidableEq, Repr

def messengerBeliefPrayerMoments : List MessengerBeliefPrayerMoment :=
  [ .messengerFaithfulBelieve, .beliefInGodAngelsScripturesMessengers
  , .noMessengerDistinction, .hearAndObey, .forgivenessReturn
  , .noSoulOverburdened, .gainsAndSuffersDeeds, .forgetMistakePrayer
  , .noPriorOrUnbearableBurden, .pardonForgiveMercy, .protectorHelp ]

theorem quran_al_baqara_messenger_belief_prayer_witness :
    messengerBeliefPrayerMoments.length = 11
    ∧ messengerBeliefPrayerMoments.head? = some .messengerFaithfulBelieve
    ∧ messengerBeliefPrayerMoments.getLast? = some .protectorHelp := by
  exact ⟨rfl, rfl, rfl⟩

end QuranAlBaqaraMessengerBeliefPrayerWitness
end Gnosis.Witnesses.Islam
