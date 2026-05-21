import Init

namespace Gnosis.Witnesses.Bible.SecondThessalonians
namespace SecondThessaloniansIniquityDelusionWitness

/-!
# 2 Thessalonians 2:1-12 -- Shaken Timing, Man of Sin, and Delusion

Source text: `docs/ebooks/source-texts/bible-kjv.txt:95167-95207`.

This is a deception-boundary witness. False timing claims shake the mind; the
counterproof is not date arithmetic but the exposure of substitution: the man of
sin enthrones himself as God, lying power follows, and delusion closes over those
who refuse the love of truth.

No `sorry`, no new `axiom`.
-/

structure ShakenTimingBoundary where
  comingAndGatheringNamed : Bool := true
  mindNotSoonShaken : Bool := true
  falseSpiritWordLetterRejected : Bool := true
  dayNotAtHandClaimRejected : Bool := true
  fallingAwayFirst : Bool := true
  manOfSinRevealed : Bool := true
  selfExaltationAsGod : Bool := true
deriving DecidableEq, Repr

def shakenTimingBoundary : ShakenTimingBoundary := {}

def timingDeceptionBoundary (b : ShakenTimingBoundary) : Prop :=
  b.comingAndGatheringNamed = true ∧
  b.mindNotSoonShaken = true ∧
  b.falseSpiritWordLetterRejected = true ∧
  b.dayNotAtHandClaimRejected = true ∧
  b.fallingAwayFirst = true ∧
  b.manOfSinRevealed = true ∧
  b.selfExaltationAsGod = true

structure DelusionCounterproof where
  mysteryIniquityAlreadyWorks : Bool := true
  restraintUntilRevealedTime : Bool := true
  wickedConsumedByMouthSpirit : Bool := true
  destroyedByBrightnessComing : Bool := true
  satanicPowerSignsLyingWonders : Bool := true
  unrighteousDeceivableness : Bool := true
  loveOfTruthNotReceived : Bool := true
  strongDelusionBelievesLie : Bool := true
  pleasureInUnrighteousnessJudged : Bool := true
deriving DecidableEq, Repr

def delusionCounterproof : DelusionCounterproof := {}

def delusionFromTruthRefusal (d : DelusionCounterproof) : Prop :=
  d.mysteryIniquityAlreadyWorks = true ∧
  d.restraintUntilRevealedTime = true ∧
  d.wickedConsumedByMouthSpirit = true ∧
  d.destroyedByBrightnessComing = true ∧
  d.satanicPowerSignsLyingWonders = true ∧
  d.unrighteousDeceivableness = true ∧
  d.loveOfTruthNotReceived = true ∧
  d.strongDelusionBelievesLie = true ∧
  d.pleasureInUnrighteousnessJudged = true

theorem second_thessalonians_timing_deception :
    timingDeceptionBoundary shakenTimingBoundary := by
  unfold timingDeceptionBoundary shakenTimingBoundary
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem second_thessalonians_delusion_counterproof :
    delusionFromTruthRefusal delusionCounterproof := by
  unfold delusionFromTruthRefusal delusionCounterproof
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem second_thessalonians_iniquity_delusion_witness :
    timingDeceptionBoundary shakenTimingBoundary ∧
    delusionFromTruthRefusal delusionCounterproof := by
  exact ⟨second_thessalonians_timing_deception,
    second_thessalonians_delusion_counterproof⟩

end SecondThessaloniansIniquityDelusionWitness
end Gnosis.Witnesses.Bible.SecondThessalonians
