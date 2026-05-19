import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraCovenantEthicsWitness

/-!
# Quran 2:83-86, Al-Baqara -- Covenant Ethics and Partial Observance

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1192-1210`.

This bounded witness tracks the concrete covenant-ethics indictment:

  * worship of God alone is joined to care for parents, kin, orphans, and the poor;
  * good speech, prayer, and prescribed alms are named;
  * bloodshed and exile are forbidden and acknowledged;
  * killing, expulsion, sin, aggression, and captive-ransoming expose contradiction;
  * believing some Scripture while rejecting other parts is challenged;
  * disgrace, harsh torment, unlightened punishment, and no help close the unit.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive CovenantEthicsMoment
  | worshipAndCare
  | speechPrayerAlms
  | turningAway
  | bloodAndExilePledge
  | acknowledgedTestimony
  | killingExpulsionAggression
  | captiveRansomContradiction
  | partialScriptureQuestion
  | disgraceAndTorment
  | worldBoughtForHereafter
deriving DecidableEq, Repr

def covenantEthicsMoments : List CovenantEthicsMoment :=
  [ CovenantEthicsMoment.worshipAndCare
  , CovenantEthicsMoment.speechPrayerAlms
  , CovenantEthicsMoment.turningAway
  , CovenantEthicsMoment.bloodAndExilePledge
  , CovenantEthicsMoment.acknowledgedTestimony
  , CovenantEthicsMoment.killingExpulsionAggression
  , CovenantEthicsMoment.captiveRansomContradiction
  , CovenantEthicsMoment.partialScriptureQuestion
  , CovenantEthicsMoment.disgraceAndTorment
  , CovenantEthicsMoment.worldBoughtForHereafter
  ]

structure WorshipCarePattern where
  childrenIsraelPledge : Bool
  worshipNoneButGod : Bool
  parentsGoodness : Bool
  kinGoodness : Bool
  orphansGoodness : Bool
  poorGoodness : Bool
  goodWordsToPeople : Bool
  prayerKept : Bool
  almsPaid : Bool
  mostTurnedAway : Bool
deriving DecidableEq, Repr

def worshipCarePattern : WorshipCarePattern where
  childrenIsraelPledge := true
  worshipNoneButGod := true
  parentsGoodness := true
  kinGoodness := true
  orphansGoodness := true
  poorGoodness := true
  goodWordsToPeople := true
  prayerKept := true
  almsPaid := true
  mostTurnedAway := true

structure BloodExilePattern where
  bloodshedForbidden : Bool
  homelandExpulsionForbidden : Bool
  pledgeAcknowledged : Bool
  testimonyPresent : Bool
  killingOneAnother : Bool
  drivingOwnPeopleOut : Bool
  helpInSinAndAggression : Bool
  captivesRansomed : Bool
  expulsionStillWrong : Bool
deriving DecidableEq, Repr

def bloodExilePattern : BloodExilePattern where
  bloodshedForbidden := true
  homelandExpulsionForbidden := true
  pledgeAcknowledged := true
  testimonyPresent := true
  killingOneAnother := true
  drivingOwnPeopleOut := true
  helpInSinAndAggression := true
  captivesRansomed := true
  expulsionStillWrong := true

structure PartialScriptureOutcomePattern where
  someScriptureBelieved : Bool
  otherScriptureRejected : Bool
  disgraceInThisLife : Bool
  resurrectionHarshTorment : Bool
  godAwareOfActions : Bool
  worldBoughtAtHereafterPrice : Bool
  tormentNotLightened : Bool
  noHelpGiven : Bool
deriving DecidableEq, Repr

def partialScriptureOutcomePattern : PartialScriptureOutcomePattern where
  someScriptureBelieved := true
  otherScriptureRejected := true
  disgraceInThisLife := true
  resurrectionHarshTorment := true
  godAwareOfActions := true
  worldBoughtAtHereafterPrice := true
  tormentNotLightened := true
  noHelpGiven := true

theorem quran_al_baqara_covenant_ethics_witness :
    covenantEthicsMoments.length = 10
    ∧ covenantEthicsMoments.head? = some CovenantEthicsMoment.worshipAndCare
    ∧ covenantEthicsMoments.getLast? = some CovenantEthicsMoment.worldBoughtForHereafter
    ∧ worshipCarePattern.worshipNoneButGod = true
    ∧ worshipCarePattern.parentsGoodness = true
    ∧ worshipCarePattern.orphansGoodness = true
    ∧ worshipCarePattern.goodWordsToPeople = true
    ∧ worshipCarePattern.prayerKept = true
    ∧ worshipCarePattern.almsPaid = true
    ∧ worshipCarePattern.mostTurnedAway = true
    ∧ bloodExilePattern.bloodshedForbidden = true
    ∧ bloodExilePattern.homelandExpulsionForbidden = true
    ∧ bloodExilePattern.pledgeAcknowledged = true
    ∧ bloodExilePattern.killingOneAnother = true
    ∧ bloodExilePattern.drivingOwnPeopleOut = true
    ∧ bloodExilePattern.helpInSinAndAggression = true
    ∧ bloodExilePattern.captivesRansomed = true
    ∧ partialScriptureOutcomePattern.someScriptureBelieved = true
    ∧ partialScriptureOutcomePattern.otherScriptureRejected = true
    ∧ partialScriptureOutcomePattern.disgraceInThisLife = true
    ∧ partialScriptureOutcomePattern.resurrectionHarshTorment = true
    ∧ partialScriptureOutcomePattern.worldBoughtAtHereafterPrice = true
    ∧ partialScriptureOutcomePattern.tormentNotLightened = true
    ∧ partialScriptureOutcomePattern.noHelpGiven = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · rfl

end QuranAlBaqaraCovenantEthicsWitness
end Gnosis.Witnesses.Islam
