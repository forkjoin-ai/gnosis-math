import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraMessengerPedagogyWitness

/-!
# Quran 2:151-152, Al-Baqara -- Messenger, Teaching, Remembrance

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1462-1466`.

This bounded witness tracks the messenger pedagogy and response:

  * a Messenger from among the believers is sent;
  * he recites revelations, purifies, and teaches Scripture and wisdom;
  * he teaches what was not known;
  * remembrance is answered by divine remembrance;
  * thankfulness is commanded and ingratitude forbidden.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive MessengerPedagogyMoment
  | messengerAmongYou
  | revelationRecited
  | purification
  | scriptureWisdomTaught
  | unknownThingsTaught
  | reciprocalRemembrance
  | thankfulNotUngrateful
deriving DecidableEq, Repr

def messengerPedagogyMoments : List MessengerPedagogyMoment :=
  [ MessengerPedagogyMoment.messengerAmongYou
  , MessengerPedagogyMoment.revelationRecited
  , MessengerPedagogyMoment.purification
  , MessengerPedagogyMoment.scriptureWisdomTaught
  , MessengerPedagogyMoment.unknownThingsTaught
  , MessengerPedagogyMoment.reciprocalRemembrance
  , MessengerPedagogyMoment.thankfulNotUngrateful
  ]

structure MessengerTeachingPattern where
  messengerSentAmongYou : Bool
  messengerOfYourOwn : Bool
  revelationsRecited : Bool
  purificationGiven : Bool
  scriptureTaught : Bool
  wisdomTaught : Bool
  unknownThingsTaught : Bool
deriving DecidableEq, Repr

def messengerTeachingPattern : MessengerTeachingPattern where
  messengerSentAmongYou := true
  messengerOfYourOwn := true
  revelationsRecited := true
  purificationGiven := true
  scriptureTaught := true
  wisdomTaught := true
  unknownThingsTaught := true

structure RemembranceGratitudePattern where
  rememberGodCommand : Bool
  godRemembersYou : Bool
  thankfulnessCommand : Bool
  ingratitudeForbidden : Bool
deriving DecidableEq, Repr

def remembranceGratitudePattern : RemembranceGratitudePattern where
  rememberGodCommand := true
  godRemembersYou := true
  thankfulnessCommand := true
  ingratitudeForbidden := true

theorem quran_al_baqara_messenger_pedagogy_witness :
    messengerPedagogyMoments.length = 7
    ∧ messengerPedagogyMoments.head? = some MessengerPedagogyMoment.messengerAmongYou
    ∧ messengerPedagogyMoments.getLast? = some MessengerPedagogyMoment.thankfulNotUngrateful
    ∧ messengerTeachingPattern.messengerSentAmongYou = true
    ∧ messengerTeachingPattern.messengerOfYourOwn = true
    ∧ messengerTeachingPattern.revelationsRecited = true
    ∧ messengerTeachingPattern.purificationGiven = true
    ∧ messengerTeachingPattern.scriptureTaught = true
    ∧ messengerTeachingPattern.wisdomTaught = true
    ∧ messengerTeachingPattern.unknownThingsTaught = true
    ∧ remembranceGratitudePattern.rememberGodCommand = true
    ∧ remembranceGratitudePattern.godRemembersYou = true
    ∧ remembranceGratitudePattern.thankfulnessCommand = true
    ∧ remembranceGratitudePattern.ingratitudeForbidden = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end QuranAlBaqaraMessengerPedagogyWitness
end Gnosis.Witnesses.Islam
