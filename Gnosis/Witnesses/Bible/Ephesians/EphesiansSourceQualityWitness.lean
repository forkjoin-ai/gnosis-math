import Gnosis.Witnesses.Bible.Ephesians.EphesiansArmorBoldnessClosingWitness
import Gnosis.Witnesses.Bible.Ephesians.EphesiansChosenAdoptionGraceWitness
import Gnosis.Witnesses.Bible.Ephesians.EphesiansDeadGraceWorkmanshipWitness
import Gnosis.Witnesses.Bible.Ephesians.EphesiansEnlightenedHeadshipWitness
import Gnosis.Witnesses.Bible.Ephesians.EphesiansHouseholdOrderWitness
import Gnosis.Witnesses.Bible.Ephesians.EphesiansInnerFullnessPrayerWitness
import Gnosis.Witnesses.Bible.Ephesians.EphesiansLightWisdomWitness
import Gnosis.Witnesses.Bible.Ephesians.EphesiansMarriageMysteryWitness
import Gnosis.Witnesses.Bible.Ephesians.EphesiansMysteryFellowheirsWitness
import Gnosis.Witnesses.Bible.Ephesians.EphesiansMysteryGatheringInheritanceWitness
import Gnosis.Witnesses.Bible.Ephesians.EphesiansOldNewWalkWitness
import Gnosis.Witnesses.Bible.Ephesians.EphesiansPartitionPeaceTempleWitness
import Gnosis.Witnesses.Bible.Ephesians.EphesiansSpiritSealEarnestWitness
import Gnosis.Witnesses.Bible.Ephesians.EphesiansUnityGiftMaturityWitness

namespace Gnosis.Witnesses.Bible.Ephesians
namespace EphesiansSourceQualityWitness

/-!
# Ephesians -- Source Quality Spine

This repair module is the interpretive spine for the fast Ephesians pass. The
book invariant is pleromatic body assembly: all things gathered in Christ,
far-off and near made one, gifts differentiated without shattering unity, and
the church built as a Spirit habitation.

Primary gap/counterproof: every local partition tries to become ultimate again:
Gentile alienation, doctrine-wind, old-man vanity, darkness, household power, and
high-place conflict. Ephesians does not solve this by erasing structure; it
orders structure through headship, love, light, and armor.

Unseen sat: fullness is not a static possession. It is a fitted, growing body
whose joints supply one another while the head remains non-substitutable.

No `sorry`, no new `axiom`.
-/

structure EphesiansInvariant where
  allThingsGatheredInChrist : Bool := true
  farAndNearMadeOneBody : Bool := true
  giftsServeMatureBody : Bool := true
  fullnessExpressedAsHabitation : Bool := true
deriving DecidableEq, Repr

def ephesiansInvariant : EphesiansInvariant := {}

def pleromaticBodyAssembly (i : EphesiansInvariant) : Prop :=
  i.allThingsGatheredInChrist = true ∧
  i.farAndNearMadeOneBody = true ∧
  i.giftsServeMatureBody = true ∧
  i.fullnessExpressedAsHabitation = true

structure EphesiansCounterproof where
  partitionWallCannotGovernBody : Bool := true
  doctrineWindCannotMatureBody : Bool := true
  darknessCannotInterpretLight : Bool := true
  householdPowerCannotReplaceChristChurchMystery : Bool := true
  fleshBloodCannotNameTheFinalConflict : Bool := true
deriving DecidableEq, Repr

def ephesiansCounterproof : EphesiansCounterproof := {}

def partitionReturnRejected (g : EphesiansCounterproof) : Prop :=
  g.partitionWallCannotGovernBody = true ∧
  g.doctrineWindCannotMatureBody = true ∧
  g.darknessCannotInterpretLight = true ∧
  g.householdPowerCannotReplaceChristChurchMystery = true ∧
  g.fleshBloodCannotNameTheFinalConflict = true

theorem ephesians_quality_invariant :
    pleromaticBodyAssembly ephesiansInvariant := by
  unfold pleromaticBodyAssembly ephesiansInvariant
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem ephesians_quality_counterproof :
    partitionReturnRejected ephesiansCounterproof := by
  unfold partitionReturnRejected ephesiansCounterproof
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem ephesians_source_quality_witness :
    pleromaticBodyAssembly ephesiansInvariant ∧
    partitionReturnRejected ephesiansCounterproof ∧
    EphesiansMysteryGatheringInheritanceWitness.gatheredInheritanceWitness
      EphesiansMysteryGatheringInheritanceWitness.gatheringInheritance ∧
    EphesiansPartitionPeaceTempleWitness.partitionPeaceWitness
      EphesiansPartitionPeaceTempleWitness.partitionPeace ∧
    EphesiansUnityGiftMaturityWitness.maturityWitness
      EphesiansUnityGiftMaturityWitness.giftMaturity ∧
    EphesiansLightWisdomWitness.loveLightWitness
      EphesiansLightWisdomWitness.loveLightWalk ∧
    EphesiansArmorBoldnessClosingWitness.armorStandWitness
      EphesiansArmorBoldnessClosingWitness.armorStand := by
  exact ⟨ephesians_quality_invariant,
    ephesians_quality_counterproof,
    EphesiansMysteryGatheringInheritanceWitness.ephesians_gathered_inheritance,
    EphesiansPartitionPeaceTempleWitness.ephesians_partition_peace,
    EphesiansUnityGiftMaturityWitness.ephesians_maturity,
    EphesiansLightWisdomWitness.ephesians_love_light,
    EphesiansArmorBoldnessClosingWitness.ephesians_armor_stand⟩

end EphesiansSourceQualityWitness
end Gnosis.Witnesses.Bible.Ephesians
