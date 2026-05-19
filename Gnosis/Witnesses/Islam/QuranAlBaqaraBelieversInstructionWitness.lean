import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraBelieversInstructionWitness

/-!
# Quran 2:104-110, Al-Baqara -- Believers' Speech, Revelation, Forbearance

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1281-1299`.

This bounded witness tracks the direct address to believers:

  * believers are instructed in disciplined speech and attentive listening;
  * disbelieving People of the Book and idolaters resent good sent from God;
  * God chooses His grace and His bounty is unlimited;
  * superseded or forgotten revelation is replaced by better or similar;
  * God's power, sovereignty over heavens and earth, and sole protection are named;
  * demanding from the messenger as Moses was demanded from is warned against;
  * exchanging faith for disbelief marks straying;
  * envy after clear truth is met with forbearance until God's command;
  * prayer, alms, stored good, and God's sight close the unit.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive BelieversInstructionMoment
  | disciplinedSpeech
  | attentiveListening
  | resentmentOfGood
  | graceAndBounty
  | revelationReplacement
  | sovereigntyProtection
  | demandWarning
  | envyForbearance
  | prayerAlmsStoredGood
deriving DecidableEq, Repr

def believersInstructionMoments : List BelieversInstructionMoment :=
  [ BelieversInstructionMoment.disciplinedSpeech
  , BelieversInstructionMoment.attentiveListening
  , BelieversInstructionMoment.resentmentOfGood
  , BelieversInstructionMoment.graceAndBounty
  , BelieversInstructionMoment.revelationReplacement
  , BelieversInstructionMoment.sovereigntyProtection
  , BelieversInstructionMoment.demandWarning
  , BelieversInstructionMoment.envyForbearance
  , BelieversInstructionMoment.prayerAlmsStoredGood
  ]

structure SpeechListeningPattern where
  believersAddressed : Bool
  forbiddenPhraseAvoided : Bool
  replacementPhraseGiven : Bool
  listenCommand : Bool
  tormentForIgnoring : Bool
deriving DecidableEq, Repr

def speechListeningPattern : SpeechListeningPattern where
  believersAddressed := true
  forbiddenPhraseAvoided := true
  replacementPhraseGiven := true
  listenCommand := true
  tormentForIgnoring := true

structure GraceRevelationPattern where
  bookDisbelieversResentGood : Bool
  idolatersResentGood : Bool
  goodSentFromLord : Bool
  graceChosenByGod : Bool
  bountyNoLimit : Bool
  supersededRevelationReplaced : Bool
  forgottenRevelationReplaced : Bool
  betterOrSimilarReplacement : Bool
deriving DecidableEq, Repr

def graceRevelationPattern : GraceRevelationPattern where
  bookDisbelieversResentGood := true
  idolatersResentGood := true
  goodSentFromLord := true
  graceChosenByGod := true
  bountyNoLimit := true
  supersededRevelationReplaced := true
  forgottenRevelationReplaced := true
  betterOrSimilarReplacement := true

structure PowerForbearancePracticePattern where
  godPowerEverything : Bool
  heavensEarthControl : Bool
  noProtectorButGod : Bool
  noHelperButGod : Bool
  mosesLikeDemandWarned : Bool
  faithExchangedForDisbelief : Bool
  strayedFromRightPath : Bool
  envyAfterClearTruth : Bool
  forgiveAndForbear : Bool
  untilGodCommand : Bool
  prayerKept : Bool
  almsPaid : Bool
  storedGoodFoundWithGod : Bool
  godSeesActions : Bool
deriving DecidableEq, Repr

def powerForbearancePracticePattern : PowerForbearancePracticePattern where
  godPowerEverything := true
  heavensEarthControl := true
  noProtectorButGod := true
  noHelperButGod := true
  mosesLikeDemandWarned := true
  faithExchangedForDisbelief := true
  strayedFromRightPath := true
  envyAfterClearTruth := true
  forgiveAndForbear := true
  untilGodCommand := true
  prayerKept := true
  almsPaid := true
  storedGoodFoundWithGod := true
  godSeesActions := true

theorem quran_al_baqara_believers_instruction_witness :
    believersInstructionMoments.length = 9
    ∧ believersInstructionMoments.head? = some BelieversInstructionMoment.disciplinedSpeech
    ∧ believersInstructionMoments.getLast? = some BelieversInstructionMoment.prayerAlmsStoredGood
    ∧ speechListeningPattern.believersAddressed = true
    ∧ speechListeningPattern.forbiddenPhraseAvoided = true
    ∧ speechListeningPattern.replacementPhraseGiven = true
    ∧ speechListeningPattern.listenCommand = true
    ∧ graceRevelationPattern.bookDisbelieversResentGood = true
    ∧ graceRevelationPattern.idolatersResentGood = true
    ∧ graceRevelationPattern.graceChosenByGod = true
    ∧ graceRevelationPattern.bountyNoLimit = true
    ∧ graceRevelationPattern.betterOrSimilarReplacement = true
    ∧ powerForbearancePracticePattern.godPowerEverything = true
    ∧ powerForbearancePracticePattern.heavensEarthControl = true
    ∧ powerForbearancePracticePattern.noProtectorButGod = true
    ∧ powerForbearancePracticePattern.mosesLikeDemandWarned = true
    ∧ powerForbearancePracticePattern.faithExchangedForDisbelief = true
    ∧ powerForbearancePracticePattern.envyAfterClearTruth = true
    ∧ powerForbearancePracticePattern.forgiveAndForbear = true
    ∧ powerForbearancePracticePattern.prayerKept = true
    ∧ powerForbearancePracticePattern.almsPaid = true
    ∧ powerForbearancePracticePattern.storedGoodFoundWithGod = true
    ∧ powerForbearancePracticePattern.godSeesActions = true := by
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

end QuranAlBaqaraBelieversInstructionWitness
end Gnosis.Witnesses.Islam
