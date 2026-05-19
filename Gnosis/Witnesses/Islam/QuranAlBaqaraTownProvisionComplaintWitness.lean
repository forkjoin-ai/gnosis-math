import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraTownProvisionComplaintWitness

/-!
# Quran 2:58-61, Al-Baqara -- Town, Water, Provision Complaint

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1107-1130`.

This bounded witness tracks the next Israel remembrance unit:

  * town entry is paired with humble gate-entry and a request for relief;
  * forgiveness and increased reward are promised;
  * wrongdoers substitute another word and receive plague for disobedience;
  * Moses prays for water, strikes the rock, and twelve springs appear;
  * each group knows its drinking place;
  * eating and drinking God's sustenance is paired with the ban on corruption;
  * the one-food complaint asks for produce, herbs, cucumbers, garlic, lentils, and onions;
  * exchanging better for worse leads to Egypt, humiliation, wretchedness, and wrath;
  * persistent message-rejection, killing prophets, disobedience, and lawbreaking are named.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive TownProvisionComplaintMoment
  | townGateHumility
  | wordSubstitutionPlague
  | mosesWaterRock
  | twelveSprings
  | eatDrinkNoCorruption
  | foodComplaint
  | betterForWorseExchange
  | humiliationWrath
  | rejectionAndLawbreaking
deriving DecidableEq, Repr

def townProvisionComplaintMoments : List TownProvisionComplaintMoment :=
  [ TownProvisionComplaintMoment.townGateHumility
  , TownProvisionComplaintMoment.wordSubstitutionPlague
  , TownProvisionComplaintMoment.mosesWaterRock
  , TownProvisionComplaintMoment.twelveSprings
  , TownProvisionComplaintMoment.eatDrinkNoCorruption
  , TownProvisionComplaintMoment.foodComplaint
  , TownProvisionComplaintMoment.betterForWorseExchange
  , TownProvisionComplaintMoment.humiliationWrath
  , TownProvisionComplaintMoment.rejectionAndLawbreaking
  ]

structure TownGatePattern where
  townEntryCommanded : Bool
  eatFreelyPermitted : Bool
  humbleGateEntry : Bool
  reliefWordCommanded : Bool
  forgivenessPromised : Bool
  goodDoersIncreased : Bool
  wrongdoersSubstitutedWord : Bool
  plagueSentForDisobedience : Bool
deriving DecidableEq, Repr

def townGatePattern : TownGatePattern where
  townEntryCommanded := true
  eatFreelyPermitted := true
  humbleGateEntry := true
  reliefWordCommanded := true
  forgivenessPromised := true
  goodDoersIncreased := true
  wrongdoersSubstitutedWord := true
  plagueSentForDisobedience := true

structure WaterProvisionPattern where
  mosesPrayedForWater : Bool
  rockStruckWithStaff : Bool
  twelveSpringsGushed : Bool
  eachGroupKnewDrinkingPlace : Bool
  eatGodSustenance : Bool
  drinkGodSustenance : Bool
  corruptionInLandForbidden : Bool
deriving DecidableEq, Repr

def waterProvisionPattern : WaterProvisionPattern where
  mosesPrayedForWater := true
  rockStruckWithStaff := true
  twelveSpringsGushed := true
  eachGroupKnewDrinkingPlace := true
  eatGodSustenance := true
  drinkGodSustenance := true
  corruptionInLandForbidden := true

structure ComplaintWrathPattern where
  oneFoodComplaint : Bool
  produceRequested : Bool
  herbsCucumbersGarlicLentilsOnionsRequested : Bool
  betterForWorseExchangeNamed : Bool
  egyptGivenAsAnswer : Bool
  humiliationStruck : Bool
  wretchednessStruck : Bool
  wrathIncurred : Bool
  messagesPersistentlyRejected : Bool
  prophetsKilledWrongly : Bool
  disobedienceNamed : Bool
  lawbreakingNamed : Bool
deriving DecidableEq, Repr

def complaintWrathPattern : ComplaintWrathPattern where
  oneFoodComplaint := true
  produceRequested := true
  herbsCucumbersGarlicLentilsOnionsRequested := true
  betterForWorseExchangeNamed := true
  egyptGivenAsAnswer := true
  humiliationStruck := true
  wretchednessStruck := true
  wrathIncurred := true
  messagesPersistentlyRejected := true
  prophetsKilledWrongly := true
  disobedienceNamed := true
  lawbreakingNamed := true

theorem quran_al_baqara_town_provision_complaint_witness :
    townProvisionComplaintMoments.length = 9
    ∧ townProvisionComplaintMoments.head? =
        some TownProvisionComplaintMoment.townGateHumility
    ∧ townProvisionComplaintMoments.getLast? =
        some TownProvisionComplaintMoment.rejectionAndLawbreaking
    ∧ townGatePattern.townEntryCommanded = true
    ∧ townGatePattern.humbleGateEntry = true
    ∧ townGatePattern.forgivenessPromised = true
    ∧ townGatePattern.wrongdoersSubstitutedWord = true
    ∧ townGatePattern.plagueSentForDisobedience = true
    ∧ waterProvisionPattern.mosesPrayedForWater = true
    ∧ waterProvisionPattern.rockStruckWithStaff = true
    ∧ waterProvisionPattern.twelveSpringsGushed = true
    ∧ waterProvisionPattern.eachGroupKnewDrinkingPlace = true
    ∧ waterProvisionPattern.corruptionInLandForbidden = true
    ∧ complaintWrathPattern.oneFoodComplaint = true
    ∧ complaintWrathPattern.herbsCucumbersGarlicLentilsOnionsRequested = true
    ∧ complaintWrathPattern.betterForWorseExchangeNamed = true
    ∧ complaintWrathPattern.humiliationStruck = true
    ∧ complaintWrathPattern.wretchednessStruck = true
    ∧ complaintWrathPattern.wrathIncurred = true
    ∧ complaintWrathPattern.messagesPersistentlyRejected = true
    ∧ complaintWrathPattern.prophetsKilledWrongly = true
    ∧ complaintWrathPattern.disobedienceNamed = true
    ∧ complaintWrathPattern.lawbreakingNamed = true := by
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

end QuranAlBaqaraTownProvisionComplaintWitness
end Gnosis.Witnesses.Islam
