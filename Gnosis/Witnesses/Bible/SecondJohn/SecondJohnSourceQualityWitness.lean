import Gnosis.Witnesses.Bible.SecondJohn.SecondJohnTruthLoveHospitalityWitness

namespace Gnosis.Witnesses.Bible.SecondJohn
namespace SecondJohnSourceQualityWitness

/-!
# 2 John -- Source Quality Spine

Book-level invariant: 2 John compresses truth, love, doctrine, and hospitality
into one household protocol. Truth must dwell and remain; love must walk after
commandment; reception must distinguish embodied confession from antichrist
doctrine.

Counterproof: hospitality is not automatically virtue. A house can become a
participation port for evil works when blessing is detached from doctrine. The
small epistle's severity is therefore not social coldness; it is boundary
control for love that refuses to become an open exploit.

No `sorry`, no new `axiom`.
-/

structure SecondJohnBookInvariant where
  truthDwellsCommunally : Bool := true
  loveWalksAsCommandment : Bool := true
  fleshComingConfessionAuditsDoctrine : Bool := true
  rewardRequiresSelfWatch : Bool := true
  hospitalitySharesWorks : Bool := true
  inkYieldsToFaceToFaceJoy : Bool := true
deriving DecidableEq, Repr

def secondJohnBookInvariant : SecondJohnBookInvariant := {}

def secondJohnQualitySpine (s : SecondJohnBookInvariant) : Prop :=
  s.truthDwellsCommunally = true ∧
  s.loveWalksAsCommandment = true ∧
  s.fleshComingConfessionAuditsDoctrine = true ∧
  s.rewardRequiresSelfWatch = true ∧
  s.hospitalitySharesWorks = true ∧
  s.inkYieldsToFaceToFaceJoy = true

theorem second_john_source_quality_spine :
    secondJohnQualitySpine secondJohnBookInvariant := by
  unfold secondJohnQualitySpine secondJohnBookInvariant
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem second_john_source_quality_witness :
    secondJohnQualitySpine secondJohnBookInvariant ∧
    SecondJohnTruthLoveHospitalityWitness.truthDwellingLedger
      SecondJohnTruthLoveHospitalityWitness.truthDwellingGreeting ∧
    SecondJohnTruthLoveHospitalityWitness.loveIsCommandWalk
      SecondJohnTruthLoveHospitalityWitness.commandLoveWalk ∧
    SecondJohnTruthLoveHospitalityWitness.participationBoundaryWitness
      SecondJohnTruthLoveHospitalityWitness.hospitalityBoundary := by
  exact ⟨second_john_source_quality_spine,
    SecondJohnTruthLoveHospitalityWitness.second_john_truth_dwelling,
    SecondJohnTruthLoveHospitalityWitness.second_john_love_command_walk,
    SecondJohnTruthLoveHospitalityWitness.second_john_participation_boundary⟩

end SecondJohnSourceQualityWitness
end Gnosis.Witnesses.Bible.SecondJohn
