import Gnosis.Witnesses.Bible.ThirdJohn.ThirdJohnTruthWalkDiotrephesWitness

namespace Gnosis.Witnesses.Bible.ThirdJohn
namespace ThirdJohnSourceQualityWitness

/-!
# 3 John -- Source Quality Spine

Book-level invariant: 3 John makes truth mobile. Gaius walks it, traveling
workers carry it, receivers become fellowhelpers to it, Diotrephes blocks it,
and Demetrius is confirmed by convergent testimony.

Counterproof: local preeminence can masquerade as church order while functioning
as gate capture. The sign is not mere disagreement; it is refusal to receive,
malicious output, blocking the brethren, and expelling those who keep the
channel open.

No `sorry`, no new `axiom`.
-/

structure ThirdJohnBookInvariant where
  truthWalkRequiresTestimony : Bool := true
  hospitalityForwardsNameWorkers : Bool := true
  receptionMakesFellowhelpers : Bool := true
  preeminenceCapturesTheGate : Bool := true
  demetriusHasConvergentWitness : Bool := true
  faceToFaceCompletesInk : Bool := true
deriving DecidableEq, Repr

def thirdJohnBookInvariant : ThirdJohnBookInvariant := {}

def thirdJohnQualitySpine (t : ThirdJohnBookInvariant) : Prop :=
  t.truthWalkRequiresTestimony = true ∧
  t.hospitalityForwardsNameWorkers = true ∧
  t.receptionMakesFellowhelpers = true ∧
  t.preeminenceCapturesTheGate = true ∧
  t.demetriusHasConvergentWitness = true ∧
  t.faceToFaceCompletesInk = true

theorem third_john_source_quality_spine :
    thirdJohnQualitySpine thirdJohnBookInvariant := by
  unfold thirdJohnQualitySpine thirdJohnBookInvariant
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem third_john_source_quality_witness :
    thirdJohnQualitySpine thirdJohnBookInvariant ∧
    ThirdJohnTruthWalkDiotrephesWitness.truthWalkTestimony
      ThirdJohnTruthWalkDiotrephesWitness.gaiusTruthWalk ∧
    ThirdJohnTruthWalkDiotrephesWitness.supportBecomesTruthLabor
      ThirdJohnTruthWalkDiotrephesWitness.fellowhelperHospitality ∧
    ThirdJohnTruthWalkDiotrephesWitness.preeminenceCaptureRejected
      ThirdJohnTruthWalkDiotrephesWitness.diotrephesDemetriusBoundary := by
  exact ⟨third_john_source_quality_spine,
    ThirdJohnTruthWalkDiotrephesWitness.third_john_truth_walk,
    ThirdJohnTruthWalkDiotrephesWitness.third_john_support_truth_labor,
    ThirdJohnTruthWalkDiotrephesWitness.third_john_preeminence_capture_rejected⟩

end ThirdJohnSourceQualityWitness
end Gnosis.Witnesses.Bible.ThirdJohn
