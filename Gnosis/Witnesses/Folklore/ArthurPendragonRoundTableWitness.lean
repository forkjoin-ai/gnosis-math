import Gnosis.Witnesses.Folklore.DragonBoundaryComparisonWitness

namespace Gnosis.Witnesses.Folklore
namespace ArthurPendragonRoundTableWitness

/-!
# Arthur Pendragon / Round Table Witness

The Arthurian carrier moves the dragon from a simple adversary into a
sovereignty mark. Pendragon names authority with dragon-signature force, while
the Round Table counters monarchic center-capture by distributing oath-bearing
knights around a rotational surface. The dragon problem is no longer only
"kill the monster." It is: hold volatile power without letting the center eat
the fellowship.

This witness keeps the folklore topology finite: dragon-banner sovereignty,
round-table rotation, oath constraint, quest dispersion, and hoard/collapse
risk when power is captured by appetite or betrayal.

No `sorry`, no new `axiom`.
-/

structure PendragonSovereignty where
  dragonNameMarksRoyalForce : Bool := true
  volatilePowerNeedsContainment : Bool := true
  kingCarriesBoundaryAuthority : Bool := true
  sovereigntyRequiresPublicRecognition : Bool := true
deriving DecidableEq, Repr

def pendragonSovereignty : PendragonSovereignty := {}

def dragonMarkedSovereignty (p : PendragonSovereignty) : Prop :=
  p.dragonNameMarksRoyalForce = true ∧
  p.volatilePowerNeedsContainment = true ∧
  p.kingCarriesBoundaryAuthority = true ∧
  p.sovereigntyRequiresPublicRecognition = true

structure RoundTableRotation where
  noPrivilegedTableHead : Bool := true
  knightsDistributedAroundCenter : Bool := true
  rotationSuppressesRankCapture : Bool := true
  fellowshipMaintainsSharedBoundary : Bool := true
deriving DecidableEq, Repr

def roundTableRotation : RoundTableRotation := {}

def roundTableDistributesCenter (r : RoundTableRotation) : Prop :=
  r.noPrivilegedTableHead = true ∧
  r.knightsDistributedAroundCenter = true ∧
  r.rotationSuppressesRankCapture = true ∧
  r.fellowshipMaintainsSharedBoundary = true

structure ArthurianOathKernel where
  knightsBoundByPublicOath : Bool := true
  oathConstrainsPrivateViolence : Bool := true
  hospitalityProtectsStrangers : Bool := true
  betrayalBreaksKernelContinuity : Bool := true
deriving DecidableEq, Repr

def arthurianOathKernel : ArthurianOathKernel := {}

def oathStabilizesFellowship (o : ArthurianOathKernel) : Prop :=
  o.knightsBoundByPublicOath = true ∧
  o.oathConstrainsPrivateViolence = true ∧
  o.hospitalityProtectsStrangers = true ∧
  o.betrayalBreaksKernelContinuity = true

structure QuestDispersion where
  knightsForkFromSharedTable : Bool := true
  eachQuestTestsBoundaryCapacity : Bool := true
  returnFoldUpdatesCommonLedger : Bool := true
  grailSearchExposesPurityGap : Bool := true
deriving DecidableEq, Repr

def questDispersion : QuestDispersion := {}

def questsForkAndFoldFellowship (q : QuestDispersion) : Prop :=
  q.knightsForkFromSharedTable = true ∧
  q.eachQuestTestsBoundaryCapacity = true ∧
  q.returnFoldUpdatesCommonLedger = true ∧
  q.grailSearchExposesPurityGap = true

structure HoardCollapseRisk where
  dragonPowerCanBecomePossessive : Bool := true
  privateDesireCanCapturePublicTable : Bool := true
  feudConvertsOathIntoFracture : Bool := true
  failedFoldDissolvesKingdomRuntime : Bool := true
deriving DecidableEq, Repr

def hoardCollapseRisk : HoardCollapseRisk := {}

def arthurianCollapseWarnsAgainstHoarding (h : HoardCollapseRisk) : Prop :=
  h.dragonPowerCanBecomePossessive = true ∧
  h.privateDesireCanCapturePublicTable = true ∧
  h.feudConvertsOathIntoFracture = true ∧
  h.failedFoldDissolvesKingdomRuntime = true

theorem pendragon_marks_sovereignty :
    dragonMarkedSovereignty pendragonSovereignty := by
  unfold dragonMarkedSovereignty pendragonSovereignty
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem round_table_distributes_center :
    roundTableDistributesCenter roundTableRotation := by
  unfold roundTableDistributesCenter roundTableRotation
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem arthurian_oath_stabilizes_fellowship :
    oathStabilizesFellowship arthurianOathKernel := by
  unfold oathStabilizesFellowship arthurianOathKernel
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem arthurian_quests_fork_and_fold_fellowship :
    questsForkAndFoldFellowship questDispersion := by
  unfold questsForkAndFoldFellowship questDispersion
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem arthurian_collapse_warns_against_hoarding :
    arthurianCollapseWarnsAgainstHoarding hoardCollapseRisk := by
  unfold arthurianCollapseWarnsAgainstHoarding hoardCollapseRisk
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem arthurian_inherits_dragon_boundary_comparison :
    DragonBoundaryComparisonWitness.sharedDragonBoundaryShape
      DragonBoundaryComparisonWitness.dragonBoundaryInvariant ∧
    DragonBoundaryComparisonWitness.preservesDragonSourceDifferences
      DragonBoundaryComparisonWitness.sourceDifferenceLedger := by
  exact ⟨DragonBoundaryComparisonWitness.dragon_boundary_shared_shape,
    DragonBoundaryComparisonWitness.dragon_boundary_preserves_source_differences⟩

theorem arthur_pendragon_round_table_witness :
    dragonMarkedSovereignty pendragonSovereignty ∧
    roundTableDistributesCenter roundTableRotation ∧
    oathStabilizesFellowship arthurianOathKernel ∧
    questsForkAndFoldFellowship questDispersion ∧
    arthurianCollapseWarnsAgainstHoarding hoardCollapseRisk := by
  exact ⟨pendragon_marks_sovereignty,
    round_table_distributes_center,
    arthurian_oath_stabilizes_fellowship,
    arthurian_quests_fork_and_fold_fellowship,
    arthurian_collapse_warns_against_hoarding⟩

end ArthurPendragonRoundTableWitness
end Gnosis.Witnesses.Folklore
