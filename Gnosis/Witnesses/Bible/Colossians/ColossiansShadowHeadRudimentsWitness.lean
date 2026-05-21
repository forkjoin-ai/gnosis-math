import Init

namespace Gnosis.Witnesses.Bible.Colossians
namespace ColossiansShadowHeadRudimentsWitness

/-!
# Colossians 2:16-23 -- Shadow Judgments, Lost Head, and Rudiment Ordinances

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94781-94807`.

The counterproof is ritual and ascetic capture: meat, drink, days, angel worship,
and touch-taste-handle ordinances can look wise while losing the Head.

No `sorry`, no new `axiom`.
-/

structure ShadowJudgment where
  meatDrinkDayJudgmentRejected : Bool := true
  shadowBodyDistinguished : Bool := true
  voluntaryHumilityAngelWorshipRejected : Bool := true
  unseenIntrusionNamed : Bool := true
  fleshlyMindPuffed : Bool := true
  notHoldingHead : Bool := true
  bodyIncreaseFromHead : Bool := true
deriving DecidableEq, Repr

def shadowJudgment : ShadowJudgment := {}

def shadowHeadBoundary (s : ShadowJudgment) : Prop :=
  s.meatDrinkDayJudgmentRejected = true ∧ s.shadowBodyDistinguished = true ∧
  s.voluntaryHumilityAngelWorshipRejected = true ∧ s.unseenIntrusionNamed = true ∧
  s.fleshlyMindPuffed = true ∧ s.notHoldingHead = true ∧ s.bodyIncreaseFromHead = true

structure RudimentOrdinance where
  deadWithChristFromRudiments : Bool := true
  worldOrdinanceSubjectionQuestioned : Bool := true
  touchTasteHandleNamed : Bool := true
  perishWithUsing : Bool := true
  commandmentsDoctrinesOfMen : Bool := true
  shewOfWisdomWillWorship : Bool := true
  noHonorAgainstFleshSatisfying : Bool := true
deriving DecidableEq, Repr

def rudimentOrdinance : RudimentOrdinance := {}

def rudimentOrdinanceGap (r : RudimentOrdinance) : Prop :=
  r.deadWithChristFromRudiments = true ∧ r.worldOrdinanceSubjectionQuestioned = true ∧
  r.touchTasteHandleNamed = true ∧ r.perishWithUsing = true ∧
  r.commandmentsDoctrinesOfMen = true ∧ r.shewOfWisdomWillWorship = true ∧
  r.noHonorAgainstFleshSatisfying = true

theorem colossians_shadow_head_boundary :
    shadowHeadBoundary shadowJudgment := by
  unfold shadowHeadBoundary shadowJudgment
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem colossians_rudiment_ordinance_gap :
    rudimentOrdinanceGap rudimentOrdinance := by
  unfold rudimentOrdinanceGap rudimentOrdinance
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem colossians_shadow_head_rudiments_witness :
    shadowHeadBoundary shadowJudgment ∧
    rudimentOrdinanceGap rudimentOrdinance := by
  exact ⟨colossians_shadow_head_boundary, colossians_rudiment_ordinance_gap⟩

end ColossiansShadowHeadRudimentsWitness
end Gnosis.Witnesses.Bible.Colossians
