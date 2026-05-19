import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraAbrahamIshmaelPrayerWitness

/-!
# Quran 2:127-129, Al-Baqara -- Abraham, Ishmael, Prayer for Messenger

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1368-1376`.

This bounded witness tracks Abraham and Ishmael's prayer while building the House:

  * Abraham and Ishmael build the foundations of the House;
  * they ask acceptance from the All Hearing, All Knowing Lord;
  * they ask to be devoted to God and for devoted descendants;
  * they ask to be shown worship and to have repentance accepted;
  * they ask for a messenger from among the descendants;
  * that messenger recites revelations, teaches Scripture and wisdom, and purifies;
  * divine might and wisdom close the prayer.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive AbrahamIshmaelPrayerMoment
  | foundationsBuilt
  | acceptanceRequested
  | devotionRequested
  | descendantsCommunityRequested
  | worshipShown
  | repentanceAccepted
  | messengerRaised
  | reciteTeachPurify
  | mightyWiseClose
deriving DecidableEq, Repr

def abrahamIshmaelPrayerMoments : List AbrahamIshmaelPrayerMoment :=
  [ AbrahamIshmaelPrayerMoment.foundationsBuilt
  , AbrahamIshmaelPrayerMoment.acceptanceRequested
  , AbrahamIshmaelPrayerMoment.devotionRequested
  , AbrahamIshmaelPrayerMoment.descendantsCommunityRequested
  , AbrahamIshmaelPrayerMoment.worshipShown
  , AbrahamIshmaelPrayerMoment.repentanceAccepted
  , AbrahamIshmaelPrayerMoment.messengerRaised
  , AbrahamIshmaelPrayerMoment.reciteTeachPurify
  , AbrahamIshmaelPrayerMoment.mightyWiseClose
  ]

structure HouseFoundationPrayerPattern where
  abrahamBuilds : Bool
  ishmaelBuilds : Bool
  houseFoundationsBuilt : Bool
  acceptanceRequested : Bool
  allHearingNamed : Bool
  allKnowingNamed : Bool
deriving DecidableEq, Repr

def houseFoundationPrayerPattern : HouseFoundationPrayerPattern where
  abrahamBuilds := true
  ishmaelBuilds := true
  houseFoundationsBuilt := true
  acceptanceRequested := true
  allHearingNamed := true
  allKnowingNamed := true

structure DevotionRepentancePattern where
  devotionToGodRequested : Bool
  devotedDescendantCommunityRequested : Bool
  worshipShownRequested : Bool
  repentanceAcceptanceRequested : Bool
  everRelentingNamed : Bool
  mostMercifulNamed : Bool
deriving DecidableEq, Repr

def devotionRepentancePattern : DevotionRepentancePattern where
  devotionToGodRequested := true
  devotedDescendantCommunityRequested := true
  worshipShownRequested := true
  repentanceAcceptanceRequested := true
  everRelentingNamed := true
  mostMercifulNamed := true

structure MessengerPrayerPattern where
  messengerFromAmongThemRequested : Bool
  revelationsRecited : Bool
  scriptureTaught : Bool
  wisdomTaught : Bool
  purificationGiven : Bool
  mightyNamed : Bool
  wiseNamed : Bool
deriving DecidableEq, Repr

def messengerPrayerPattern : MessengerPrayerPattern where
  messengerFromAmongThemRequested := true
  revelationsRecited := true
  scriptureTaught := true
  wisdomTaught := true
  purificationGiven := true
  mightyNamed := true
  wiseNamed := true

theorem quran_al_baqara_abraham_ishmael_prayer_witness :
    abrahamIshmaelPrayerMoments.length = 9
    ∧ abrahamIshmaelPrayerMoments.head? = some AbrahamIshmaelPrayerMoment.foundationsBuilt
    ∧ abrahamIshmaelPrayerMoments.getLast? = some AbrahamIshmaelPrayerMoment.mightyWiseClose
    ∧ houseFoundationPrayerPattern.abrahamBuilds = true
    ∧ houseFoundationPrayerPattern.ishmaelBuilds = true
    ∧ houseFoundationPrayerPattern.houseFoundationsBuilt = true
    ∧ houseFoundationPrayerPattern.acceptanceRequested = true
    ∧ houseFoundationPrayerPattern.allHearingNamed = true
    ∧ houseFoundationPrayerPattern.allKnowingNamed = true
    ∧ devotionRepentancePattern.devotionToGodRequested = true
    ∧ devotionRepentancePattern.devotedDescendantCommunityRequested = true
    ∧ devotionRepentancePattern.worshipShownRequested = true
    ∧ devotionRepentancePattern.repentanceAcceptanceRequested = true
    ∧ devotionRepentancePattern.everRelentingNamed = true
    ∧ devotionRepentancePattern.mostMercifulNamed = true
    ∧ messengerPrayerPattern.messengerFromAmongThemRequested = true
    ∧ messengerPrayerPattern.revelationsRecited = true
    ∧ messengerPrayerPattern.scriptureTaught = true
    ∧ messengerPrayerPattern.wisdomTaught = true
    ∧ messengerPrayerPattern.purificationGiven = true
    ∧ messengerPrayerPattern.mightyNamed = true
    ∧ messengerPrayerPattern.wiseNamed = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end QuranAlBaqaraAbrahamIshmaelPrayerWitness
end Gnosis.Witnesses.Islam
