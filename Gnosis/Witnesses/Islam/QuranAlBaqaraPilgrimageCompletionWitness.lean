import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraPilgrimageCompletionWitness

/-!
# Quran 2:196, Al-Baqara -- Pilgrimage Completion and Compensation

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1656-1668`.

This bounded witness tracks major/minor pilgrimage completion:

  * major and minor pilgrimages are completed for God's sake;
  * prevention requires an affordable sacrificial offering;
  * shaving waits until the offering reaches its place;
  * illness or scalp ailment is compensated by fasting, feeding the poor, or sacrifice;
  * safety after minor-to-major break requires an affordable offering;
  * lack of means requires three days fasting during pilgrimage and seven after return;
  * the rule applies away from the Sacred Mosque household;
  * mindfulness and God's stern retribution close the unit.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive PilgrimageCompletionMoment
  | pilgrimagesCompleted
  | preventionOffering
  | shavingBoundary
  | illnessCompensation
  | safetyOffering
  | tenDayFasting
  | sacredMosqueDistance
  | mindfulSternRetribution
deriving DecidableEq, Repr

def pilgrimageCompletionMoments : List PilgrimageCompletionMoment :=
  [ PilgrimageCompletionMoment.pilgrimagesCompleted
  , PilgrimageCompletionMoment.preventionOffering
  , PilgrimageCompletionMoment.shavingBoundary
  , PilgrimageCompletionMoment.illnessCompensation
  , PilgrimageCompletionMoment.safetyOffering
  , PilgrimageCompletionMoment.tenDayFasting
  , PilgrimageCompletionMoment.sacredMosqueDistance
  , PilgrimageCompletionMoment.mindfulSternRetribution
  ]

structure PilgrimageOfferingPattern where
  majorPilgrimageCompleted : Bool
  minorPilgrimageCompleted : Bool
  forGodsSake : Bool
  preventedCase : Bool
  affordableOffering : Bool
  shavingDelayed : Bool
  offeringReachesPlace : Bool
deriving DecidableEq, Repr

def pilgrimageOfferingPattern : PilgrimageOfferingPattern where
  majorPilgrimageCompleted := true
  minorPilgrimageCompleted := true
  forGodsSake := true
  preventedCase := true
  affordableOffering := true
  shavingDelayed := true
  offeringReachesPlace := true

structure CompensationMindfulnessPattern where
  illnessOrScalpAilment : Bool
  fastingCompensation : Bool
  feedingPoorCompensation : Bool
  sacrificeCompensation : Bool
  safetyBreakOffering : Bool
  lacksMeansCase : Bool
  threeDaysDuringPilgrimage : Bool
  sevenDaysOnReturn : Bool
  tenDaysTotal : Bool
  notNearSacredMosque : Bool
  mindfulOfGod : Bool
  sternRetribution : Bool
deriving DecidableEq, Repr

def compensationMindfulnessPattern : CompensationMindfulnessPattern where
  illnessOrScalpAilment := true
  fastingCompensation := true
  feedingPoorCompensation := true
  sacrificeCompensation := true
  safetyBreakOffering := true
  lacksMeansCase := true
  threeDaysDuringPilgrimage := true
  sevenDaysOnReturn := true
  tenDaysTotal := true
  notNearSacredMosque := true
  mindfulOfGod := true
  sternRetribution := true

theorem quran_al_baqara_pilgrimage_completion_witness :
    pilgrimageCompletionMoments.length = 8
    ∧ pilgrimageCompletionMoments.head? =
        some PilgrimageCompletionMoment.pilgrimagesCompleted
    ∧ pilgrimageCompletionMoments.getLast? =
        some PilgrimageCompletionMoment.mindfulSternRetribution
    ∧ pilgrimageOfferingPattern.majorPilgrimageCompleted = true
    ∧ pilgrimageOfferingPattern.minorPilgrimageCompleted = true
    ∧ pilgrimageOfferingPattern.forGodsSake = true
    ∧ pilgrimageOfferingPattern.preventedCase = true
    ∧ pilgrimageOfferingPattern.affordableOffering = true
    ∧ pilgrimageOfferingPattern.shavingDelayed = true
    ∧ compensationMindfulnessPattern.illnessOrScalpAilment = true
    ∧ compensationMindfulnessPattern.fastingCompensation = true
    ∧ compensationMindfulnessPattern.feedingPoorCompensation = true
    ∧ compensationMindfulnessPattern.sacrificeCompensation = true
    ∧ compensationMindfulnessPattern.safetyBreakOffering = true
    ∧ compensationMindfulnessPattern.lacksMeansCase = true
    ∧ compensationMindfulnessPattern.threeDaysDuringPilgrimage = true
    ∧ compensationMindfulnessPattern.sevenDaysOnReturn = true
    ∧ compensationMindfulnessPattern.tenDaysTotal = true
    ∧ compensationMindfulnessPattern.notNearSacredMosque = true
    ∧ compensationMindfulnessPattern.mindfulOfGod = true
    ∧ compensationMindfulnessPattern.sternRetribution = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

end QuranAlBaqaraPilgrimageCompletionWitness
end Gnosis.Witnesses.Islam
