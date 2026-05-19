import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraIsraelDeliveranceWitness

/-!
# Quran 2:47-57, Al-Baqara -- Israel, Deliverance, Moses, Provision

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1082-1106`.

This bounded witness tracks the first remembrance sequence after the opening
Children of Israel covenant charge:

  * blessing and favor are remembered;
  * the guarded Day rejects substitution, intercession, ransom, and help;
  * Pharaoh's torment, slaughter, and sparing are named as trial;
  * the sea is parted, Israel saved, and Pharaoh's people drowned;
  * Moses' forty nights are followed by calf worship and forgiveness;
  * Scripture and discernment are given for guidance;
  * repentance after the calf is accepted;
  * the face-to-face demand is answered by thunderbolt and revival;
  * shade, manna, and quails are provided, while self-wronging is named.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive IsraelDeliveranceMoment
  | favoredBlessing
  | guardedDay
  | pharaohTorment
  | seaParted
  | calfWrongForgiven
  | scriptureDiscernment
  | repentanceAccepted
  | thunderboltRevival
  | shadeMannaQuails
deriving DecidableEq, Repr

def israelDeliveranceMoments : List IsraelDeliveranceMoment :=
  [ IsraelDeliveranceMoment.favoredBlessing
  , IsraelDeliveranceMoment.guardedDay
  , IsraelDeliveranceMoment.pharaohTorment
  , IsraelDeliveranceMoment.seaParted
  , IsraelDeliveranceMoment.calfWrongForgiven
  , IsraelDeliveranceMoment.scriptureDiscernment
  , IsraelDeliveranceMoment.repentanceAccepted
  , IsraelDeliveranceMoment.thunderboltRevival
  , IsraelDeliveranceMoment.shadeMannaQuails
  ]

structure FavorJudgmentPattern where
  childrenOfIsraelAddressedAgain : Bool
  blessingRememberedAgain : Bool
  favoredOverOtherPeople : Bool
  guardedDayNamed : Bool
  noSoulStandsForAnother : Bool
  noIntercessionAccepted : Bool
  noRansomAccepted : Bool
  noHelpGiven : Bool
deriving DecidableEq, Repr

def favorJudgmentPattern : FavorJudgmentPattern where
  childrenOfIsraelAddressedAgain := true
  blessingRememberedAgain := true
  favoredOverOtherPeople := true
  guardedDayNamed := true
  noSoulStandsForAnother := true
  noIntercessionAccepted := true
  noRansomAccepted := true
  noHelpGiven := true

structure DeliveranceTrialPattern where
  savedFromPharaohPeople : Bool
  terribleTorment : Bool
  sonsSlaughtered : Bool
  womenSpared : Bool
  greatTrialFromLord : Bool
  seaParted : Bool
  israelSaved : Bool
  pharaohPeopleDrowned : Bool
  witnessedBeforeEyes : Bool
deriving DecidableEq, Repr

def deliveranceTrialPattern : DeliveranceTrialPattern where
  savedFromPharaohPeople := true
  terribleTorment := true
  sonsSlaughtered := true
  womenSpared := true
  greatTrialFromLord := true
  seaParted := true
  israelSaved := true
  pharaohPeopleDrowned := true
  witnessedBeforeEyes := true

structure MosesCalfGuidancePattern where
  fortyNightsAppointed : Bool
  calfWorshipWhileAway : Bool
  terribleWrong : Bool
  forgivenForThankfulness : Bool
  scriptureGivenToMoses : Bool
  discernmentGiven : Bool
  guidanceAim : Bool
  repentanceToMaker : Bool
  repentanceAccepted : Bool
  relentingMercifulNamed : Bool
deriving DecidableEq, Repr

def mosesCalfGuidancePattern : MosesCalfGuidancePattern where
  fortyNightsAppointed := true
  calfWorshipWhileAway := true
  terribleWrong := true
  forgivenForThankfulness := true
  scriptureGivenToMoses := true
  discernmentGiven := true
  guidanceAim := true
  repentanceToMaker := true
  repentanceAccepted := true
  relentingMercifulNamed := true

structure RevivalProvisionPattern where
  faceToFaceDemand : Bool
  thunderboltsStruck : Bool
  revivedAfterDeath : Bool
  thankfulnessAim : Bool
  cloudShadeProvided : Bool
  mannaSentDown : Bool
  quailsSentDown : Bool
  goodThingsProvided : Bool
  selfWrongingNamed : Bool
deriving DecidableEq, Repr

def revivalProvisionPattern : RevivalProvisionPattern where
  faceToFaceDemand := true
  thunderboltsStruck := true
  revivedAfterDeath := true
  thankfulnessAim := true
  cloudShadeProvided := true
  mannaSentDown := true
  quailsSentDown := true
  goodThingsProvided := true
  selfWrongingNamed := true

theorem quran_al_baqara_israel_deliverance_witness :
    israelDeliveranceMoments.length = 9
    ∧ israelDeliveranceMoments.head? = some IsraelDeliveranceMoment.favoredBlessing
    ∧ israelDeliveranceMoments.getLast? = some IsraelDeliveranceMoment.shadeMannaQuails
    ∧ favorJudgmentPattern.favoredOverOtherPeople = true
    ∧ favorJudgmentPattern.noSoulStandsForAnother = true
    ∧ favorJudgmentPattern.noIntercessionAccepted = true
    ∧ favorJudgmentPattern.noRansomAccepted = true
    ∧ deliveranceTrialPattern.savedFromPharaohPeople = true
    ∧ deliveranceTrialPattern.terribleTorment = true
    ∧ deliveranceTrialPattern.sonsSlaughtered = true
    ∧ deliveranceTrialPattern.greatTrialFromLord = true
    ∧ deliveranceTrialPattern.seaParted = true
    ∧ deliveranceTrialPattern.pharaohPeopleDrowned = true
    ∧ mosesCalfGuidancePattern.fortyNightsAppointed = true
    ∧ mosesCalfGuidancePattern.calfWorshipWhileAway = true
    ∧ mosesCalfGuidancePattern.forgivenForThankfulness = true
    ∧ mosesCalfGuidancePattern.scriptureGivenToMoses = true
    ∧ mosesCalfGuidancePattern.discernmentGiven = true
    ∧ mosesCalfGuidancePattern.repentanceAccepted = true
    ∧ revivalProvisionPattern.faceToFaceDemand = true
    ∧ revivalProvisionPattern.thunderboltsStruck = true
    ∧ revivalProvisionPattern.revivedAfterDeath = true
    ∧ revivalProvisionPattern.cloudShadeProvided = true
    ∧ revivalProvisionPattern.mannaSentDown = true
    ∧ revivalProvisionPattern.selfWrongingNamed = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · rfl

end QuranAlBaqaraIsraelDeliveranceWitness
end Gnosis.Witnesses.Islam
