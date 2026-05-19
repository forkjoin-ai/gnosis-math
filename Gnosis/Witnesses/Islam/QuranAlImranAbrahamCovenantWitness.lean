import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlImranAbrahamCovenantWitness

/-!
# Quran 3:65-92, Al Imran -- Abraham, Strategy, Covenant, and Accepted Devotion

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:2328-2411`.

This bounded witness tracks Quran 3:65-92:

  * Abraham is not made Jew or Christian; Torah and Gospel came after him;
  * Abraham is upright, devoted to God, and not an idolater;
  * the closest people to Abraham are those who follow him, this Prophet, and believers;
  * a group among the People of the Book seeks to lead believers astray;
  * truth is mixed with falsehood and concealed knowingly;
  * a strategy of believing in the morning and rejecting later is named;
  * guidance and grace are in God's hand;
  * trustworthiness among the People of the Book is distinguished from betrayal;
  * covenant and oath selling for small gain is condemned;
  * Scripture is twisted by tongues and falsely attributed to God;
  * no prophet commands people to take him, angels, or prophets as lords;
  * a pledge binds prophets to believe and support a confirming messenger;
  * willing and unwilling submission returns to God;
  * undivided belief in revelations and prophets is affirmed;
  * rejection after belief and clear proof receives curse, except repentance and mending;
  * no religion other than devotion is accepted, and true piety gives from cherished things.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive AbrahamCovenantMoment
  | abrahamChronology
  | uprightDevotion
  | closestToAbraham
  | astrayStrategy
  | concealedTruth
  | guidanceGrace
  | trustAndBetrayal
  | covenantSold
  | scriptureTwisted
  | noCreatedLords
  | prophetPledge
  | universalSubmission
  | undividedBelief
  | repentanceException
  | cherishedGiving
deriving DecidableEq, Repr

def abrahamCovenantMoments : List AbrahamCovenantMoment :=
  [ AbrahamCovenantMoment.abrahamChronology
  , AbrahamCovenantMoment.uprightDevotion
  , AbrahamCovenantMoment.closestToAbraham
  , AbrahamCovenantMoment.astrayStrategy
  , AbrahamCovenantMoment.concealedTruth
  , AbrahamCovenantMoment.guidanceGrace
  , AbrahamCovenantMoment.trustAndBetrayal
  , AbrahamCovenantMoment.covenantSold
  , AbrahamCovenantMoment.scriptureTwisted
  , AbrahamCovenantMoment.noCreatedLords
  , AbrahamCovenantMoment.prophetPledge
  , AbrahamCovenantMoment.universalSubmission
  , AbrahamCovenantMoment.undividedBelief
  , AbrahamCovenantMoment.repentanceException
  , AbrahamCovenantMoment.cherishedGiving
  ]

structure AbrahamCovenantPattern where
  abrahamNotJewChristian : Bool
  abrahamUprightDevoted : Bool
  prophetAndBelieversClosest : Bool
  astrayOnlyThemselves : Bool
  truthMixedAndHidden : Bool
  guidanceBelongsToGod : Bool
  graceInGodsHand : Bool
  trustSpectrumNamed : Bool
  covenantSoldCondemned : Bool
  scriptureTwistingNamed : Bool
  noProphetCommandsSelfLordship : Bool
  confirmingMessengerPledge : Bool
  allReturnToGod : Bool
  noDistinctionAmongProphets : Bool
  repentanceAndMendingException : Bool
  cherishedThingsGiven : Bool
deriving DecidableEq, Repr

def abrahamCovenantPattern : AbrahamCovenantPattern where
  abrahamNotJewChristian := true
  abrahamUprightDevoted := true
  prophetAndBelieversClosest := true
  astrayOnlyThemselves := true
  truthMixedAndHidden := true
  guidanceBelongsToGod := true
  graceInGodsHand := true
  trustSpectrumNamed := true
  covenantSoldCondemned := true
  scriptureTwistingNamed := true
  noProphetCommandsSelfLordship := true
  confirmingMessengerPledge := true
  allReturnToGod := true
  noDistinctionAmongProphets := true
  repentanceAndMendingException := true
  cherishedThingsGiven := true

theorem quran_al_imran_abraham_covenant_witness :
    abrahamCovenantMoments.length = 15
    ∧ abrahamCovenantMoments.head? = some AbrahamCovenantMoment.abrahamChronology
    ∧ abrahamCovenantMoments.getLast? = some AbrahamCovenantMoment.cherishedGiving
    ∧ abrahamCovenantPattern.abrahamNotJewChristian = true
    ∧ abrahamCovenantPattern.abrahamUprightDevoted = true
    ∧ abrahamCovenantPattern.prophetAndBelieversClosest = true
    ∧ abrahamCovenantPattern.astrayOnlyThemselves = true
    ∧ abrahamCovenantPattern.truthMixedAndHidden = true
    ∧ abrahamCovenantPattern.guidanceBelongsToGod = true
    ∧ abrahamCovenantPattern.graceInGodsHand = true
    ∧ abrahamCovenantPattern.trustSpectrumNamed = true
    ∧ abrahamCovenantPattern.covenantSoldCondemned = true
    ∧ abrahamCovenantPattern.scriptureTwistingNamed = true
    ∧ abrahamCovenantPattern.noProphetCommandsSelfLordship = true
    ∧ abrahamCovenantPattern.confirmingMessengerPledge = true
    ∧ abrahamCovenantPattern.allReturnToGod = true
    ∧ abrahamCovenantPattern.noDistinctionAmongProphets = true
    ∧ abrahamCovenantPattern.repentanceAndMendingException = true
    ∧ abrahamCovenantPattern.cherishedThingsGiven = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end QuranAlImranAbrahamCovenantWitness
end Gnosis.Witnesses.Islam
