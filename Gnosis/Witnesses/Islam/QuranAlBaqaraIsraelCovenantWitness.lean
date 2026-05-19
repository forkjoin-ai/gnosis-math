import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraIsraelCovenantWitness

/-!
# Quran 2:40-46, Al-Baqara -- Israel, Covenant, Truth, Prayer

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1057-1081`.

This bounded witness tracks the opening Children of Israel address:

  * remembered blessing and reciprocal pledge;
  * belief in the confirming message;
  * refusal to sell messages for a small price;
  * truth must not be mixed with falsehood or knowingly hidden;
  * prayer, prescribed alms, and shared worship are commanded;
  * self-forgetting public righteousness is challenged;
  * help is sought through steadfastness and prayer;
  * humility, meeting the Lord, and return to Him close the unit.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive IsraelCovenantMoment
  | rememberBlessing
  | honorPledge
  | believeConfirmingMessage
  | doNotSellMessages
  | doNotMixTruthFalsehood
  | prayerAlmsWorship
  | doNotForgetYourself
  | seekHelpSteadfastPrayer
  | humbleMeetAndReturn
deriving DecidableEq, Repr

def israelCovenantMoments : List IsraelCovenantMoment :=
  [ IsraelCovenantMoment.rememberBlessing
  , IsraelCovenantMoment.honorPledge
  , IsraelCovenantMoment.believeConfirmingMessage
  , IsraelCovenantMoment.doNotSellMessages
  , IsraelCovenantMoment.doNotMixTruthFalsehood
  , IsraelCovenantMoment.prayerAlmsWorship
  , IsraelCovenantMoment.doNotForgetYourself
  , IsraelCovenantMoment.seekHelpSteadfastPrayer
  , IsraelCovenantMoment.humbleMeetAndReturn
  ]

structure CovenantRemembrancePattern where
  childrenOfIsraelAddressed : Bool
  blessingRemembered : Bool
  pledgeHonoredToGod : Bool
  divinePledgeHonoredBack : Bool
  fearDirectedToGod : Bool
  mindfulnessDirectedToGod : Bool
deriving DecidableEq, Repr

def covenantRemembrancePattern : CovenantRemembrancePattern where
  childrenOfIsraelAddressed := true
  blessingRemembered := true
  pledgeHonoredToGod := true
  divinePledgeHonoredBack := true
  fearDirectedToGod := true
  mindfulnessDirectedToGod := true

structure MessageTruthPattern where
  confirmingMessageBelieved : Bool
  firstDisbeliefRejected : Bool
  messagesNotSoldSmallPrice : Bool
  truthFalsehoodNotMixed : Bool
  truthNotHiddenKnowingly : Bool
deriving DecidableEq, Repr

def messageTruthPattern : MessageTruthPattern where
  confirmingMessageBelieved := true
  firstDisbeliefRejected := true
  messagesNotSoldSmallPrice := true
  truthFalsehoodNotMixed := true
  truthNotHiddenKnowingly := true

structure WorshipIntegrityPattern where
  prayerKeptUp : Bool
  prescribedAlmsPaid : Bool
  bowWithThoseWhoBow : Bool
  rightCommandedToOthers : Bool
  selfForgottenRebuked : Bool
  scriptureRecited : Bool
  senseQuestioned : Bool
deriving DecidableEq, Repr

def worshipIntegrityPattern : WorshipIntegrityPattern where
  prayerKeptUp := true
  prescribedAlmsPaid := true
  bowWithThoseWhoBow := true
  rightCommandedToOthers := true
  selfForgottenRebuked := true
  scriptureRecited := true
  senseQuestioned := true

structure HelpHumilityReturnPattern where
  helpThroughSteadfastness : Bool
  helpThroughPrayer : Bool
  hardExceptForHumble : Bool
  humbleKnowMeetingLord : Bool
  returnToLordKnown : Bool
deriving DecidableEq, Repr

def helpHumilityReturnPattern : HelpHumilityReturnPattern where
  helpThroughSteadfastness := true
  helpThroughPrayer := true
  hardExceptForHumble := true
  humbleKnowMeetingLord := true
  returnToLordKnown := true

theorem quran_al_baqara_israel_covenant_witness :
    israelCovenantMoments.length = 9
    ∧ israelCovenantMoments.head? = some IsraelCovenantMoment.rememberBlessing
    ∧ israelCovenantMoments.getLast? = some IsraelCovenantMoment.humbleMeetAndReturn
    ∧ covenantRemembrancePattern.childrenOfIsraelAddressed = true
    ∧ covenantRemembrancePattern.blessingRemembered = true
    ∧ covenantRemembrancePattern.pledgeHonoredToGod = true
    ∧ covenantRemembrancePattern.divinePledgeHonoredBack = true
    ∧ covenantRemembrancePattern.fearDirectedToGod = true
    ∧ messageTruthPattern.confirmingMessageBelieved = true
    ∧ messageTruthPattern.firstDisbeliefRejected = true
    ∧ messageTruthPattern.messagesNotSoldSmallPrice = true
    ∧ messageTruthPattern.truthFalsehoodNotMixed = true
    ∧ messageTruthPattern.truthNotHiddenKnowingly = true
    ∧ worshipIntegrityPattern.prayerKeptUp = true
    ∧ worshipIntegrityPattern.prescribedAlmsPaid = true
    ∧ worshipIntegrityPattern.bowWithThoseWhoBow = true
    ∧ worshipIntegrityPattern.selfForgottenRebuked = true
    ∧ worshipIntegrityPattern.scriptureRecited = true
    ∧ helpHumilityReturnPattern.helpThroughSteadfastness = true
    ∧ helpHumilityReturnPattern.helpThroughPrayer = true
    ∧ helpHumilityReturnPattern.hardExceptForHumble = true
    ∧ helpHumilityReturnPattern.humbleKnowMeetingLord = true
    ∧ helpHumilityReturnPattern.returnToLordKnown = true := by
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

end QuranAlBaqaraIsraelCovenantWitness
end Gnosis.Witnesses.Islam
