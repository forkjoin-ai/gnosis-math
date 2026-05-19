import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraMessengerRejectionWitness

/-!
# Quran 2:87-91, Al-Baqara -- Messengers, Envy, Confirming Truth

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1211-1236`.

This bounded witness tracks the messenger-rejection unit:

  * Moses receives Scripture and later messengers follow in succession;
  * Jesus son of Mary receives clear signs and strengthening by the Holy Spirit;
  * unwanted messengers are met by arrogance, impostor accusations, and killing;
  * the wrapped-heart claim is answered by rejection for disbelief and little faith;
  * confirming Scripture arrives after prayers for victory but is rejected when known;
  * truth is denied from envy at God's bounty;
  * wrath upon wrath and humiliating torment are named;
  * partial belief in earlier revelation rejects later confirming truth.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive MessengerRejectionMoment
  | mosesScripture
  | messengerSuccession
  | jesusClearSigns
  | arrogantRejection
  | wrappedHeartClaim
  | confirmingScriptureRejected
  | envyAtBounty
  | wrathAndTorment
  | partialBeliefRefusal
deriving DecidableEq, Repr

def messengerRejectionMoments : List MessengerRejectionMoment :=
  [ MessengerRejectionMoment.mosesScripture
  , MessengerRejectionMoment.messengerSuccession
  , MessengerRejectionMoment.jesusClearSigns
  , MessengerRejectionMoment.arrogantRejection
  , MessengerRejectionMoment.wrappedHeartClaim
  , MessengerRejectionMoment.confirmingScriptureRejected
  , MessengerRejectionMoment.envyAtBounty
  , MessengerRejectionMoment.wrathAndTorment
  , MessengerRejectionMoment.partialBeliefRefusal
  ]

structure MessengerSuccessionPattern where
  mosesGivenScripture : Bool
  messengersAfterMoses : Bool
  jesusSonMaryNamed : Bool
  jesusGivenClearSigns : Bool
  holySpiritStrengthening : Bool
  unwantedMessageMetWithArrogance : Bool
  impostorAccusations : Bool
  prophetsKilled : Bool
deriving DecidableEq, Repr

def messengerSuccessionPattern : MessengerSuccessionPattern where
  mosesGivenScripture := true
  messengersAfterMoses := true
  jesusSonMaryNamed := true
  jesusGivenClearSigns := true
  holySpiritStrengthening := true
  unwantedMessageMetWithArrogance := true
  impostorAccusations := true
  prophetsKilled := true

structure ConfirmingTruthPattern where
  wrappedHeartClaim : Bool
  rejectedForDisbelief : Bool
  littleFaith : Bool
  scriptureFromGodCame : Bool
  confirmsWhatTheyHad : Bool
  victoryPrayerRemembered : Bool
  knownTruthDisbelieved : Bool
  disbelieversRejected : Bool
deriving DecidableEq, Repr

def confirmingTruthPattern : ConfirmingTruthPattern where
  wrappedHeartClaim := true
  rejectedForDisbelief := true
  littleFaith := true
  scriptureFromGodCame := true
  confirmsWhatTheyHad := true
  victoryPrayerRemembered := true
  knownTruthDisbelieved := true
  disbelieversRejected := true

structure EnvyPartialBeliefPattern where
  soulsSoldLowPrice : Bool
  godSentTruthDenied : Bool
  envyAtGodBounty : Bool
  bountySentToChosenServants : Bool
  wrathUponWrath : Bool
  humiliatingTorment : Bool
  believeRevelationCommand : Bool
  earlierRevelationClaimed : Bool
  laterTruthRejected : Bool
  laterTruthConfirmsWhatTheyHave : Bool
deriving DecidableEq, Repr

def envyPartialBeliefPattern : EnvyPartialBeliefPattern where
  soulsSoldLowPrice := true
  godSentTruthDenied := true
  envyAtGodBounty := true
  bountySentToChosenServants := true
  wrathUponWrath := true
  humiliatingTorment := true
  believeRevelationCommand := true
  earlierRevelationClaimed := true
  laterTruthRejected := true
  laterTruthConfirmsWhatTheyHave := true

theorem quran_al_baqara_messenger_rejection_witness :
    messengerRejectionMoments.length = 9
    ∧ messengerRejectionMoments.head? = some MessengerRejectionMoment.mosesScripture
    ∧ messengerRejectionMoments.getLast? = some MessengerRejectionMoment.partialBeliefRefusal
    ∧ messengerSuccessionPattern.mosesGivenScripture = true
    ∧ messengerSuccessionPattern.messengersAfterMoses = true
    ∧ messengerSuccessionPattern.jesusSonMaryNamed = true
    ∧ messengerSuccessionPattern.jesusGivenClearSigns = true
    ∧ messengerSuccessionPattern.holySpiritStrengthening = true
    ∧ messengerSuccessionPattern.unwantedMessageMetWithArrogance = true
    ∧ messengerSuccessionPattern.prophetsKilled = true
    ∧ confirmingTruthPattern.wrappedHeartClaim = true
    ∧ confirmingTruthPattern.rejectedForDisbelief = true
    ∧ confirmingTruthPattern.scriptureFromGodCame = true
    ∧ confirmingTruthPattern.confirmsWhatTheyHad = true
    ∧ confirmingTruthPattern.knownTruthDisbelieved = true
    ∧ envyPartialBeliefPattern.soulsSoldLowPrice = true
    ∧ envyPartialBeliefPattern.godSentTruthDenied = true
    ∧ envyPartialBeliefPattern.envyAtGodBounty = true
    ∧ envyPartialBeliefPattern.wrathUponWrath = true
    ∧ envyPartialBeliefPattern.humiliatingTorment = true
    ∧ envyPartialBeliefPattern.earlierRevelationClaimed = true
    ∧ envyPartialBeliefPattern.laterTruthRejected = true
    ∧ envyPartialBeliefPattern.laterTruthConfirmsWhatTheyHave = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · rfl

end QuranAlBaqaraMessengerRejectionWitness
end Gnosis.Witnesses.Islam
