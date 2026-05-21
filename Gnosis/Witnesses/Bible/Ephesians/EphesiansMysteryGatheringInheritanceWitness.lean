import Init

namespace Gnosis.Witnesses.Bible.Ephesians
namespace EphesiansMysteryGatheringInheritanceWitness

/-!
# Ephesians 1:7-12 -- Redemption, Mystery, Gathering, and Inheritance

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94021-94038`.

The chapter's first major topological claim is gathering: heaven and earth are
not left as split namespaces but gathered together in Christ in the fullness of
times. Inheritance is then keyed to purpose and counsel, not local boasting.

No `sorry`, no new `axiom`.
-/

structure RedemptionWisdomMystery where
  redemptionThroughBlood : Bool := true
  forgivenessAccordingToGraceRiches : Bool := true
  graceAboundedInWisdomPrudence : Bool := true
  mysteryOfWillMadeKnown : Bool := true
  purposeInHimself : Bool := true
deriving DecidableEq, Repr

def redemptionWisdomMystery : RedemptionWisdomMystery := {}

def mysteryDisclosureWitness (m : RedemptionWisdomMystery) : Prop :=
  m.redemptionThroughBlood = true ∧
  m.forgivenessAccordingToGraceRiches = true ∧
  m.graceAboundedInWisdomPrudence = true ∧
  m.mysteryOfWillMadeKnown = true ∧
  m.purposeInHimself = true

structure GatheringInheritance where
  fullnessOfTimesDispensation : Bool := true
  allThingsGatheredInChrist : Bool := true
  heavenAndEarthGathered : Bool := true
  inheritanceObtainedInChrist : Bool := true
  predestinatedAccordingToPurpose : Bool := true
  allWorkedAfterCounselOfWill : Bool := true
  praiseOfGloryForFirstTrusters : Bool := true
deriving DecidableEq, Repr

def gatheringInheritance : GatheringInheritance := {}

def gatheredInheritanceWitness (g : GatheringInheritance) : Prop :=
  g.fullnessOfTimesDispensation = true ∧
  g.allThingsGatheredInChrist = true ∧
  g.heavenAndEarthGathered = true ∧
  g.inheritanceObtainedInChrist = true ∧
  g.predestinatedAccordingToPurpose = true ∧
  g.allWorkedAfterCounselOfWill = true ∧
  g.praiseOfGloryForFirstTrusters = true

theorem ephesians_mystery_disclosure :
    mysteryDisclosureWitness redemptionWisdomMystery := by
  unfold mysteryDisclosureWitness redemptionWisdomMystery
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem ephesians_gathered_inheritance :
    gatheredInheritanceWitness gatheringInheritance := by
  unfold gatheredInheritanceWitness gatheringInheritance
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ephesians_mystery_gathering_inheritance_witness :
    mysteryDisclosureWitness redemptionWisdomMystery ∧
    gatheredInheritanceWitness gatheringInheritance := by
  exact ⟨ephesians_mystery_disclosure,
    ephesians_gathered_inheritance⟩

end EphesiansMysteryGatheringInheritanceWitness
end Gnosis.Witnesses.Bible.Ephesians
