import Init

namespace Gnosis.Witnesses.Bible.FirstTimothy
namespace FirstTimothyPrayerOrderMediatorWitness

/-!
# 1 Timothy 2 -- Universal Prayer, One Mediator, and Ordered Profession

Source text: `docs/ebooks/source-texts/bible-kjv.txt:95326-95365`.

The public order witness begins with prayer for all, including rulers, because
God wills salvation and truth-knowledge. The center is one mediator and ransom
for all; embodied order is then framed as godliness-profession rather than
display.

No `sorry`, no new `axiom`.
-/

structure UniversalPrayerMediator where
  prayersForAllAndAuthorities : Bool := true
  quietPeaceableGodlyLife : Bool := true
  godWillsAllSavedTruthKnown : Bool := true
  oneGodOneMediator : Bool := true
  christRansomForAll : Bool := true
  gentileTeacherInTruth : Bool := true
deriving DecidableEq, Repr

def universalPrayerMediator : UniversalPrayerMediator := {}

def universalPrayerMediatorWitness (u : UniversalPrayerMediator) : Prop :=
  u.prayersForAllAndAuthorities = true ∧ u.quietPeaceableGodlyLife = true ∧
  u.godWillsAllSavedTruthKnown = true ∧ u.oneGodOneMediator = true ∧
  u.christRansomForAll = true ∧ u.gentileTeacherInTruth = true

structure OrderedProfession where
  holyHandsWithoutWrathDoubt : Bool := true
  modestGoodWorksAdorning : Bool := true
  learningAndSubjectionNamed : Bool := true
  creationAndDeceptionArgument : Bool := true
  continuationFaithCharityHoliness : Bool := true
deriving DecidableEq, Repr

def orderedProfession : OrderedProfession := {}

def orderedProfessionWitness (o : OrderedProfession) : Prop :=
  o.holyHandsWithoutWrathDoubt = true ∧ o.modestGoodWorksAdorning = true ∧
  o.learningAndSubjectionNamed = true ∧ o.creationAndDeceptionArgument = true ∧
  o.continuationFaithCharityHoliness = true

theorem first_timothy_universal_prayer_mediator :
    universalPrayerMediatorWitness universalPrayerMediator := by
  unfold universalPrayerMediatorWitness universalPrayerMediator
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_timothy_ordered_profession :
    orderedProfessionWitness orderedProfession := by
  unfold orderedProfessionWitness orderedProfession
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem first_timothy_prayer_order_mediator_witness :
    universalPrayerMediatorWitness universalPrayerMediator ∧
    orderedProfessionWitness orderedProfession := by
  exact ⟨first_timothy_universal_prayer_mediator,
    first_timothy_ordered_profession⟩

end FirstTimothyPrayerOrderMediatorWitness
end Gnosis.Witnesses.Bible.FirstTimothy
