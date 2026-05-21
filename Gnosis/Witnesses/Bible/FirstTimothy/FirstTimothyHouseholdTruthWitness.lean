import Init

namespace Gnosis.Witnesses.Bible.FirstTimothy
namespace FirstTimothyHouseholdTruthWitness

/-!
# 1 Timothy 3 -- Overseers, Deacons, Household of God, Mystery of Godliness

Source text: `docs/ebooks/source-texts/bible-kjv.txt:95366-95412`.

Office is treated as tested household truth, not status. The church is named as
house of God, pillar and ground of truth, and the mystery of godliness is a
confessed arc from flesh manifestation to glory.

No `sorry`, no new `axiom`.
-/

structure TestedOffices where
  bishopDesiresGoodWork : Bool := true
  bishopBlamelessSoberHospitableAptTeach : Bool := true
  notViolentGreedyCovetous : Bool := true
  householdRuleTestsChurchCare : Bool := true
  novicePrideSnareRejected : Bool := true
  deaconsGravePureConscienceProved : Bool := true
  householdFaithfulnessForDeacons : Bool := true
deriving DecidableEq, Repr

def testedOffices : TestedOffices := {}

def testedOfficesWitness (t : TestedOffices) : Prop :=
  t.bishopDesiresGoodWork = true ∧ t.bishopBlamelessSoberHospitableAptTeach = true ∧
  t.notViolentGreedyCovetous = true ∧ t.householdRuleTestsChurchCare = true ∧
  t.novicePrideSnareRejected = true ∧ t.deaconsGravePureConscienceProved = true ∧
  t.householdFaithfulnessForDeacons = true

structure HouseholdTruthMystery where
  behaviorInHouseOfGod : Bool := true
  churchLivingGod : Bool := true
  pillarGroundTruth : Bool := true
  godlinessMysteryGreat : Bool := true
  manifestFleshJustifiedSpirit : Bool := true
  seenPreachedBelievedGlorified : Bool := true
deriving DecidableEq, Repr

def householdTruthMystery : HouseholdTruthMystery := {}

def householdTruthWitness (h : HouseholdTruthMystery) : Prop :=
  h.behaviorInHouseOfGod = true ∧ h.churchLivingGod = true ∧
  h.pillarGroundTruth = true ∧ h.godlinessMysteryGreat = true ∧
  h.manifestFleshJustifiedSpirit = true ∧ h.seenPreachedBelievedGlorified = true

theorem first_timothy_tested_offices :
    testedOfficesWitness testedOffices := by
  unfold testedOfficesWitness testedOffices
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_timothy_household_truth :
    householdTruthWitness householdTruthMystery := by
  unfold householdTruthWitness householdTruthMystery
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_timothy_household_truth_witness :
    testedOfficesWitness testedOffices ∧ householdTruthWitness householdTruthMystery := by
  exact ⟨first_timothy_tested_offices, first_timothy_household_truth⟩

end FirstTimothyHouseholdTruthWitness
end Gnosis.Witnesses.Bible.FirstTimothy
