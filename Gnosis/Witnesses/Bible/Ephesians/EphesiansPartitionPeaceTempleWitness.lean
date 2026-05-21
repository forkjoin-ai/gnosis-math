import Init

namespace Gnosis.Witnesses.Bible.Ephesians
namespace EphesiansPartitionPeaceTempleWitness

/-!
# Ephesians 2:11-22 -- Far-Off Gentiles, Broken Partition, and Holy Temple

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94076-94103`.

This is Ephesians' major reconciliation topology: far-off Gentiles are brought
near, the partition wall is broken, enmity is slain, and both access the Father
by one Spirit. The final image is a fitted building becoming habitation.

No `sorry`, no new `axiom`.
-/

structure FarOffMadeNigh where
  gentilesInFleshRemembered : Bool := true
  uncircumcisionLabelByMadeHands : Bool := true
  withoutChristFormerly : Bool := true
  aliensFromCommonwealth : Bool := true
  strangersFromPromiseCovenants : Bool := true
  noHopeWithoutGod : Bool := true
  madeNighByBlood : Bool := true
deriving DecidableEq, Repr

def farOffMadeNigh : FarOffMadeNigh := {}

def farOffNighWitness (f : FarOffMadeNigh) : Prop :=
  f.gentilesInFleshRemembered = true ∧
  f.uncircumcisionLabelByMadeHands = true ∧
  f.withoutChristFormerly = true ∧
  f.aliensFromCommonwealth = true ∧
  f.strangersFromPromiseCovenants = true ∧
  f.noHopeWithoutGod = true ∧
  f.madeNighByBlood = true

structure PartitionPeace where
  christOurPeace : Bool := true
  bothMadeOne : Bool := true
  middleWallBrokenDown : Bool := true
  enmityAbolishedInFlesh : Bool := true
  oneNewManMade : Bool := true
  bothReconciledInOneBodyByCross : Bool := true
  peacePreachedFarAndNear : Bool := true
  bothAccessByOneSpirit : Bool := true
deriving DecidableEq, Repr

def partitionPeace : PartitionPeace := {}

def partitionPeaceWitness (p : PartitionPeace) : Prop :=
  p.christOurPeace = true ∧
  p.bothMadeOne = true ∧
  p.middleWallBrokenDown = true ∧
  p.enmityAbolishedInFlesh = true ∧
  p.oneNewManMade = true ∧
  p.bothReconciledInOneBodyByCross = true ∧
  p.peacePreachedFarAndNear = true ∧
  p.bothAccessByOneSpirit = true

structure HouseholdTemple where
  noMoreStrangersForeigners : Bool := true
  fellowcitizensWithSaints : Bool := true
  householdOfGod : Bool := true
  apostlesProphetsFoundation : Bool := true
  christChiefCornerStone : Bool := true
  buildingFitlyFramed : Bool := true
  holyTempleGrowing : Bool := true
  habitationOfGodThroughSpirit : Bool := true
deriving DecidableEq, Repr

def householdTemple : HouseholdTemple := {}

def templeHabitationWitness (t : HouseholdTemple) : Prop :=
  t.noMoreStrangersForeigners = true ∧
  t.fellowcitizensWithSaints = true ∧
  t.householdOfGod = true ∧
  t.apostlesProphetsFoundation = true ∧
  t.christChiefCornerStone = true ∧
  t.buildingFitlyFramed = true ∧
  t.holyTempleGrowing = true ∧
  t.habitationOfGodThroughSpirit = true

theorem ephesians_far_off_nigh :
    farOffNighWitness farOffMadeNigh := by
  unfold farOffNighWitness farOffMadeNigh
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ephesians_partition_peace :
    partitionPeaceWitness partitionPeace := by
  unfold partitionPeaceWitness partitionPeace
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ephesians_temple_habitation :
    templeHabitationWitness householdTemple := by
  unfold templeHabitationWitness householdTemple
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ephesians_partition_peace_temple_witness :
    farOffNighWitness farOffMadeNigh ∧
    partitionPeaceWitness partitionPeace ∧
    templeHabitationWitness householdTemple := by
  exact ⟨ephesians_far_off_nigh,
    ephesians_partition_peace,
    ephesians_temple_habitation⟩

end EphesiansPartitionPeaceTempleWitness
end Gnosis.Witnesses.Bible.Ephesians
