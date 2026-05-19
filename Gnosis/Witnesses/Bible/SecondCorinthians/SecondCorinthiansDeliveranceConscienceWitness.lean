import Init

namespace Gnosis.Witnesses.Bible.SecondCorinthians
namespace SecondCorinthiansDeliveranceConscienceWitness

/-! # 2 Corinthians 1:8-14 -- Deliverance, Prayer, and Conscience
Source text: `docs/ebooks/source-texts/bible-kjv.txt:92832-92850`. -/

structure DeliveranceConscience where
  troubleInAsiaPressedAboveStrength : Bool
  sentenceDeathNotTrustSelfButGodRaisingDead : Bool
  deliveredDoesDeliverWillDeliver : Bool
  prayerHelpAndManyThanks : Bool
  conscienceSimplicityGodlySincerity : Bool
  notFleshlyWisdomButGrace : Bool
  mutualRejoicingDayOfLordJesus : Bool
deriving DecidableEq, Repr

def deliveranceConscience : DeliveranceConscience where
  troubleInAsiaPressedAboveStrength := true
  sentenceDeathNotTrustSelfButGodRaisingDead := true
  deliveredDoesDeliverWillDeliver := true
  prayerHelpAndManyThanks := true
  conscienceSimplicityGodlySincerity := true
  notFleshlyWisdomButGrace := true
  mutualRejoicingDayOfLordJesus := true

theorem second_corinthians_deliverance_conscience_witness :
    deliveranceConscience.troubleInAsiaPressedAboveStrength = true
    ∧ deliveranceConscience.sentenceDeathNotTrustSelfButGodRaisingDead = true
    ∧ deliveranceConscience.deliveredDoesDeliverWillDeliver = true
    ∧ deliveranceConscience.prayerHelpAndManyThanks = true
    ∧ deliveranceConscience.conscienceSimplicityGodlySincerity = true
    ∧ deliveranceConscience.notFleshlyWisdomButGrace = true
    ∧ deliveranceConscience.mutualRejoicingDayOfLordJesus = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SecondCorinthiansDeliveranceConscienceWitness
end Gnosis.Witnesses.Bible.SecondCorinthians
