import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraFastingRamadanWitness

/-!
# Quran 2:183-186, Al-Baqara -- Fasting, Ramadan, Nearness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1581-1596`.

This bounded witness tracks fasting and Ramadan:

  * fasting is prescribed for believers as for those before them, aiming at God-awareness;
  * specified days allow illness and journey make-up;
  * extreme difficulty has compensation through feeding a needy person;
  * voluntary good is better, and fasting is better if known;
  * Ramadan is the month of Quran revelation as guidance, clear messages, and discernment;
  * God wants ease, not hardship, completion, glorification, and thankfulness;
  * God is near, responds to callers, and calls servants to respond, believe, and be guided.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive FastingRamadanMoment
  | fastingPrescribed
  | mindfulnessAim
  | illnessJourneyMakeup
  | needyCompensation
  | ramadanRevelation
  | guidanceDiscernment
  | easeCompletionGratitude
  | divineNearnessResponse
deriving DecidableEq, Repr

def fastingRamadanMoments : List FastingRamadanMoment :=
  [ FastingRamadanMoment.fastingPrescribed
  , FastingRamadanMoment.mindfulnessAim
  , FastingRamadanMoment.illnessJourneyMakeup
  , FastingRamadanMoment.needyCompensation
  , FastingRamadanMoment.ramadanRevelation
  , FastingRamadanMoment.guidanceDiscernment
  , FastingRamadanMoment.easeCompletionGratitude
  , FastingRamadanMoment.divineNearnessResponse
  ]

structure FastingDisciplinePattern where
  believersAddressed : Bool
  fastingPrescribed : Bool
  prescribedForEarlierPeople : Bool
  mindfulnessAim : Bool
  specificDays : Bool
  illnessMakeupLater : Bool
  journeyMakeupLater : Bool
  extremeDifficultyCompensation : Bool
  needyPersonFed : Bool
  voluntaryGoodBetter : Bool
  fastingBetterIfKnown : Bool
deriving DecidableEq, Repr

def fastingDisciplinePattern : FastingDisciplinePattern where
  believersAddressed := true
  fastingPrescribed := true
  prescribedForEarlierPeople := true
  mindfulnessAim := true
  specificDays := true
  illnessMakeupLater := true
  journeyMakeupLater := true
  extremeDifficultyCompensation := true
  needyPersonFed := true
  voluntaryGoodBetter := true
  fastingBetterIfKnown := true

structure RamadanGuidancePattern where
  ramadanMonthNamed : Bool
  quranRevealed : Bool
  guidanceForMankind : Bool
  clearMessages : Bool
  guidanceGiven : Bool
  rightWrongDistinguished : Bool
  presentShouldFast : Bool
  easeWanted : Bool
  hardshipNotWanted : Bool
  periodCompleted : Bool
  godGlorifiedForGuidance : Bool
  thankfulnessAim : Bool
deriving DecidableEq, Repr

def ramadanGuidancePattern : RamadanGuidancePattern where
  ramadanMonthNamed := true
  quranRevealed := true
  guidanceForMankind := true
  clearMessages := true
  guidanceGiven := true
  rightWrongDistinguished := true
  presentShouldFast := true
  easeWanted := true
  hardshipNotWanted := true
  periodCompleted := true
  godGlorifiedForGuidance := true
  thankfulnessAim := true

structure NearnessResponsePattern where
  servantsAsk : Bool
  godNear : Bool
  godRespondsToCallers : Bool
  servantsRespondToGod : Bool
  servantsBelieveInGod : Bool
  guidanceAim : Bool
deriving DecidableEq, Repr

def nearnessResponsePattern : NearnessResponsePattern where
  servantsAsk := true
  godNear := true
  godRespondsToCallers := true
  servantsRespondToGod := true
  servantsBelieveInGod := true
  guidanceAim := true

theorem quran_al_baqara_fasting_ramadan_witness :
    fastingRamadanMoments.length = 8
    ∧ fastingRamadanMoments.head? = some FastingRamadanMoment.fastingPrescribed
    ∧ fastingRamadanMoments.getLast? = some FastingRamadanMoment.divineNearnessResponse
    ∧ fastingDisciplinePattern.believersAddressed = true
    ∧ fastingDisciplinePattern.fastingPrescribed = true
    ∧ fastingDisciplinePattern.prescribedForEarlierPeople = true
    ∧ fastingDisciplinePattern.mindfulnessAim = true
    ∧ fastingDisciplinePattern.illnessMakeupLater = true
    ∧ fastingDisciplinePattern.journeyMakeupLater = true
    ∧ fastingDisciplinePattern.needyPersonFed = true
    ∧ ramadanGuidancePattern.ramadanMonthNamed = true
    ∧ ramadanGuidancePattern.quranRevealed = true
    ∧ ramadanGuidancePattern.guidanceForMankind = true
    ∧ ramadanGuidancePattern.clearMessages = true
    ∧ ramadanGuidancePattern.rightWrongDistinguished = true
    ∧ ramadanGuidancePattern.presentShouldFast = true
    ∧ ramadanGuidancePattern.easeWanted = true
    ∧ ramadanGuidancePattern.hardshipNotWanted = true
    ∧ ramadanGuidancePattern.godGlorifiedForGuidance = true
    ∧ ramadanGuidancePattern.thankfulnessAim = true
    ∧ nearnessResponsePattern.godNear = true
    ∧ nearnessResponsePattern.godRespondsToCallers = true
    ∧ nearnessResponsePattern.servantsRespondToGod = true
    ∧ nearnessResponsePattern.servantsBelieveInGod = true
    ∧ nearnessResponsePattern.guidanceAim = true := by
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

end QuranAlBaqaraFastingRamadanWitness
end Gnosis.Witnesses.Islam
